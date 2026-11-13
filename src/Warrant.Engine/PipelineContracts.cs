using System.Collections.Immutable;
using Warrant.Cic;
using Warrant.Engine.Contracts;
using Warrant.Engine.Reports;
using Warrant.Kernel;
using Warrant.Meta;
using Warrant.Semantics;
using Warrant.Vir;

namespace Warrant.Engine;

public static partial class Pipeline
{
    /// <summary>The tactic fuel of a vacuity check (M6 KTD25), a small part of a unit's: it only looks for an easy refutation.</summary>
    private const long VacuityFuel = 200_000;

    private sealed partial class RunState
    {
        /// <summary>The keys of the units with a contract obligation (M6 KTD12), from the run's translation.</summary>
        private HashSet<string> _contracts = new(StringComparer.Ordinal);

        /// <summary>Records which translated units have a contract obligation.</summary>
        private void RecordContracts(Translation translation) =>
            _contracts = translation.Units.Where(u => u.Contract is not null).Select(u => u.Key).ToHashSet(StringComparer.Ordinal);

        /// <summary>
        /// Why a unit that depends on <paramref name="dep"/>, whose outcome is <paramref name="outcome"/>, is skipped: a
        /// unit whose contract is not proved is not usable as a lemma (M6 U10), so its users report that, not a goal of
        /// their own.
        /// </summary>
        private string SkipReason(string dep, string name, UnitOutcome outcome) =>
            _contracts.Contains(dep) && outcome is NotProvedOutcome or UndecidedOutcome
                ? $"it depends on {name}, whose contract is not proved."
                : $"it depends on {name}, which was not admitted.";
    }

    private sealed partial class Scope
    {
        /// <summary>
        /// A function's contract obligation (M6 KTD12, KTD16, KTD25, KTD26), after its definition: each <c>Spec.Requires</c>
        /// checked not to be unsatisfiable, each well-definedness obligation of its <c>Spec</c> expressions proved and
        /// admitted, then the obligation, proved by its <c>[ProofFor]</c> script and admitted as <c>f.$contract</c>, and for a
        /// pure method with <c>Spec.Ensures</c>, <c>f.$contract_spec</c> derived from it. Any of them that is not proved
        /// is the unit's outcome, WRT0001 at the node that produced it (KTD18). All of it runs in the unit's one budget.
        /// </summary>
        private UnitOutcome AdmitContract(
            EngineUnit unit,
            TranslatedUnit translated,
            ContractObligation contract,
            ImmutableArray<UnitAssumption> assumptions,
            List<KernelDeclaration> admitted,
            TheoremBudget budget)
        {
            var key = unit.Unit.Key;
            var kind = unit.Unit.Kind;
            var display = translated.DisplayName;
            if (contract.Script is { } script && run.ConstOutsideDependencies(unit, script) is { } outside)
            {
                var owner = RunState.Display(run.Units[outside.Owner]);
                return new FailedOutcome(
                    key, kind, display, assumptions,
                    $"Malformed proof script: Lean.Const(\"{outside.Constant}\") names a constant of '{OutcomeText.ShortName(owner)}', which this method does not depend on; name it with nameof({OutcomeText.ShortName(owner)}) instead.")
                {
                    Code = FailedOutcome.MalformedScriptCode,
                    Node = VirTree.IdOf(unit.Unit, outside.Node),
                };
            }
            if (CachedProofs is null)
            {
                foreach (var vacuity in contract.Vacuity)
                {
                    if (Refute(unit, vacuity, display, assumptions, budget) is { } refuted)
                    {
                        return refuted;
                    }
                }
            }
            UnitOutcome? Admit(TheoremShell shell, Func<UnitOutcome?> prove) =>
                CachedProofs is null ? prove() : AdmitCached(unit, shell, display, assumptions, admitted, budget, prove);

            _contractAssumptions = [];
            foreach (var wd in contract.WellDefinedness)
            {
                if (Admit(wd.Theorem, () => ProveWellDefined(unit, wd, display, assumptions, admitted, budget)) is { } failure)
                {
                    return failure;
                }
            }
            if (Admit(contract.Theorem, () => ProveContract(unit, translated.Name, contract, display, assumptions, admitted, budget)) is { } unproved)
            {
                return unproved;
            }
            if (contract.Spec is { } spec && Admit(spec, () => DeriveSpec(unit, contract, spec, display, assumptions, admitted, budget)) is { } underived)
            {
                return underived;
            }
            return new TranslatedOutcome(key, kind, display, [.. assumptions, .. _contractAssumptions.Distinct()], [.. admitted]);
        }

        /// <summary>
        /// The assumptions the default procedure found the proof relies on (M6 KTD20, U12): each callee contract it used,
        /// the contract's proof or a well-definedness or no-overflow proof (#247), and each explicit throw it could not
        /// show unreachable, the method's own or a verified callee's.
        /// </summary>
        private List<UnitAssumption> _contractAssumptions = [];

        /// <summary>
        /// The assumptions a walk relied on (KTD20, U12's <see cref="MayThrowSubject"/>): each verified callee's contract,
        /// whether the walk used it at the call or a leftover assumed a pure callee's <c>$contract_spec</c> (#173, #223),
        /// each explicit throw it did not show unreachable (#92), each throw a verified callee it calls may raise, and an
        /// exception from each dependency member it calls, at the call (M6 U20). The members' contracts themselves are
        /// extraction's <c>ExternalContract</c> assumptions (KTD9), listed whether or not the walk reached the call (#223).
        /// </summary>
        private void Record(EngineUnit unit, VcWalker walker) =>
            Record(
                unit, walker.Throws.Select(t => (t.Type, t.Node)), walker.ExternalCalls,
                walker.Calls.Concat(walker.PureCallees.Select(c => run.KeyOfConstant(c)).OfType<string>().Select(k => (k, (int?)null))));

        private void Record(
            EngineUnit unit, IEnumerable<(string Type, int? Node)> throws, IEnumerable<(string Member, int? Node)> externalCalls,
            IEnumerable<(string Callee, int? Node)> calls)
        {
            var key = unit.Unit.Key;
            foreach (var (type, node) in throws)
            {
                _contractAssumptions.Add(new UnitAssumption(key, new VirAssumption(VirAssumptionKind.MayThrow, new MayThrowSubject(type, node).Format())));
            }
            foreach (var (member, node) in externalCalls)
            {
                _contractAssumptions.Add(new UnitAssumption(key, new VirAssumption(VirAssumptionKind.MayThrow, new MayThrowSubject(member, node).Format())));
            }
            foreach (var call in calls)
            {
                _contractAssumptions.Add(new UnitAssumption(key, new VirAssumption(VirAssumptionKind.CalleeContract, call.Callee)));
                if (!run.Outcomes.TryGetValue(call.Callee, out var callee))
                {
                    continue;
                }
                foreach (var a in callee.Assumptions.Where(a => a.Assumption.Kind == VirAssumptionKind.MayThrow && a.UnitKey == call.Callee))
                {
                    var thrown = MayThrowSubject.Parse(a.Assumption.Subject);
                    var propagated = new MayThrowSubject(thrown.Thrown, thrown.Node, thrown.In ?? call.Callee, call.Callee, call.Node);
                    _contractAssumptions.Add(new UnitAssumption(key, new VirAssumption(VirAssumptionKind.MayThrow, propagated.Format())));
                }
            }
        }

        /// <summary>
        /// The names a contract obligation's binders are introduced under: the world, the operations of its dependencies,
        /// <c>self</c>, the parameters, then the operations' contracts (M6 U19), as the statement names them.
        /// </summary>
        private static List<Name> BinderNames(ContractObligation contract) => [.. contract.BinderNames];

        private void CountSearchOnce()
        {
            if (!_searched)
            {
                _searched = true;
                run.CountSearch();
            }
        }

        /// <summary>
        /// The obligation itself (KTD12): its <c>[ProofFor]</c> script from the triple, after its binders are introduced
        /// (KTD16), or without one the default procedure (KTD13, KTD14): the VC walker, then the VC simp set, then omega.
        /// The proof is admitted as <c>f.$contract</c>. Null when it was admitted, else the unit's outcome: every VC the
        /// default procedure did not prove, each at its node (#90).
        /// </summary>
        private UnitOutcome? ProveContract(
            EngineUnit unit, Name function, ContractObligation contract, string display, ImmutableArray<UnitAssumption> assumptions,
            List<KernelDeclaration> admitted, TheoremBudget budget)
        {
            var key = unit.Unit.Key;
            var kind = unit.Unit.Kind;
            var shell = contract.Theorem;
            CountSearchOnce();
            var meta = new MetaM(Env, budget.Meta) { KernelLimits = budget.Kernel, Attributes = Attributes, DisplayNames = run.Names };
            var printer = new GoalPrinter(Env, run.Names);
            var ensures = (unit.Unit.Body as BlockStmt)?.Stmts.OfType<EnsuresStmt>().FirstOrDefault();
            var ensuresNode = ensures is null ? null : VirTree.IdOf(unit.Unit, ensures);
            VcWalker WalkerIn(MetaM m) => new(m, Attributes, unit.Unit, VcKind.Postcondition, ensuresNode, contract.Raising ? null : function);
            VcWalker NewWalker() => WalkerIn(meta);
            if (contract.Script is not { } script)
            {
                return Default(
                    unit, shell, contract.Binders, BinderNames(contract), null, NewWalker,
                    (walker, g) => walker.Contract(g, contract.Program, function, contract.Raising, contract.Operations), display, assumptions, admitted, budget, meta, printer);
            }
            var recorder = options.TacticTrace is null
                ? null
                : new TacticRecorder(goals => printer.PpGoals(meta.MCtx, goals), node => VirTree.IdOf(unit.Unit, node));
            (Expr? Proof, UnitOutcome? Failure) found;
            var walked = new List<VcWalker>();
            try
            {
                // Tactic.VcGen() runs the walker from the triple and leaves its VCs, readied but not simplified (KTD16).
                var runner = new TacticRunner(new TacticM(meta, []), recorder)
                {
                    VcGen = goal =>
                    {
                        var walker = NewWalker();
                        walked.Add(walker);
                        walker.Contract(goal, contract.Program, function, contract.Raising, contract.Operations);
                        if (walker.Leftovers.FirstOrDefault(l => l.Failure is not null) is { } failed)
                        {
                            throw new TacticException("vcgen", failed.Goal, $"{VcKinds.Text(failed.Kind)}: {failed.Failure}");
                        }
                        return [.. walker.Leftovers.Select(walker.Prepare)];
                    },
                };
                found = Search(unit, shell, script, BinderNames(contract), display, assumptions, budget, meta, printer, runner, () => []);
            }
            finally
            {
                if (recorder is not null)
                {
                    options.TacticTrace!(unit.Unit.Key, recorder.Steps);
                }
            }
            if (found.Failure is { } failure)
            {
                return failure;
            }
            // The report must not depend on how the script was written (#229): the trusted statement allows every explicit
            // and external exception, so what the proof relied on is listed from every walk the script ran, or, when it ran
            // none, from a walk made only for the list, its proof discarded.
            foreach (var walker in walked)
            {
                Record(unit, walker);
            }
            if (walked.Count == 0)
            {
                RecordWithoutAProof(unit, contract, function, budget, WalkerIn);
            }
            return AdmitProof(unit, shell, VcWalker.Strip(found.Proof!), $"the kernel rejected the proof Warrant built for {Shown(shell.Name)}", display, assumptions, admitted, budget)
                ?? (ProofTerms.IsAdmittedAs(Env, shell) ? null : new FailedOutcome(key, kind, display, assumptions, $"the kernel admitted {Shown(shell.Name)} with a type other than its statement."));
        }

        /// <summary>
        /// What a contract proved by a script that never ran <c>Tactic.VcGen()</c> relied on (#229): the walk the default
        /// procedure would make, on a goal of its own whose proof is discarded, recorded as <see cref="Record(EngineUnit, VcWalker)"/>
        /// records any. When that walk cannot be completed (it raises, or meets a shape it has no rule for), every explicit
        /// throw, every call to a dependency member and every verified callee with an admitted contract in the method's VIR is
        /// listed instead: more than the proof may need, never less.
        /// </summary>
        private void RecordWithoutAProof(EngineUnit unit, ContractObligation contract, Name function, TheoremBudget budget, Func<MetaM, VcWalker> newWalker)
        {
            try
            {
                var meta = new MetaM(Env, budget.Meta) { KernelLimits = budget.Kernel, Attributes = Attributes, DisplayNames = run.Names };
                var walker = newWalker(meta);
                var root = meta.MkFreshExprSyntheticOpaqueMVar(contract.Theorem.Type);
                walker.Contract(meta.IntroN(root.Id, contract.Binders, BinderNames(contract)).Goal, contract.Program, function, contract.Raising, contract.Operations);
                TacticFuelUsed = Math.Max(TacticFuelUsed, meta.Budget.FuelUsed);
                if (!walker.Leftovers.Any(l => l.Kind == VcKind.Unsupported))
                {
                    // Readying the leftovers names the pure callees whose contracts they would assume (#173, #223).
                    foreach (var leftover in walker.Leftovers)
                    {
                        walker.Prepare(leftover);
                    }
                    Record(unit, walker);
                    return;
                }
            }
#pragma warning disable CA1031 // The walk only lists assumptions; any failure falls back to the list from the VIR below.
            catch (Exception ex) when (ex is not OperationCanceledException)
#pragma warning restore CA1031
            {
            }
            var throws = new List<(string Type, int? Node)>();
            var external = new List<(string Member, int? Node)>();
            // Under Spec.NoThrow the proof showed the method's own explicit throws unreachable (#182).
            bool own = !(contract.Raising && VcWalker.HasNoThrow(unit.Unit));
            var calls = new List<(string Callee, int? Node)>();
            foreach (var node in VirTree.PreOrder(unit.Unit))
            {
                switch (node)
                {
                    case ThrowStmt t when own:
                        throws.Add((t.Exception, VirTree.IdOf(unit.Unit, node)));
                        break;
                    case ThrowExpr t when own:
                        throws.Add((t.Exception, VirTree.IdOf(unit.Unit, node)));
                        break;
                    case ExternalCallExpr x:
                        external.Add((x.Member, VirTree.IdOf(unit.Unit, node)));
                        break;
                    case CallExpr c when c.Target != unit.Unit.Key && Env.Find(LeanNames.Contract(c.Target)) is not null:
                        calls.Add((c.Target, VirTree.IdOf(unit.Unit, node)));
                        break;
                }
            }
            Record(unit, throws, external, calls);
        }

        /// <summary>
        /// The default procedure on one obligation (KTD13, KTD14): its binders introduced, the walk, then the VC simp set
        /// and omega on each leftover. Every leftover that is not proved is WRT0001 at its node with its kind (#90), the
        /// first one the outcome's message. Null when the proof was admitted, else the unit's outcome.
        /// </summary>
        private UnitOutcome? Default(
            EngineUnit unit, TheoremShell shell, int binders, IReadOnlyList<Name> names, int? at, Func<VcWalker> newWalker, Action<VcWalker, MVarId> walk,
            string display, ImmutableArray<UnitAssumption> assumptions, List<KernelDeclaration> admitted, TheoremBudget budget, MetaM meta, GoalPrinter printer)
        {
            var key = unit.Unit.Key;
            var kind = unit.Unit.Kind;
            Expr proof;
            List<VcFailure> failures;
            VcWalker walker;
            try
            {
                walker = newWalker();
                var root = meta.MkFreshExprSyntheticOpaqueMVar(shell.Type);
                walk(walker, meta.IntroN(root.Id, binders, names).Goal);
                failures = walker.Close(g => PrintFailure(meta, printer, g));
                proof = VcWalker.Strip(meta.InstantiateMVars(root));
                TacticFuelUsed = Math.Max(TacticFuelUsed, meta.Budget.FuelUsed);
            }
            catch (Exception ex) when (ex is MetaResourceException or KernelResourceException)
            {
                return budget.Undecided(key, kind, display, assumptions, ex, "running the default procedure (the VC walker, simp and omega)");
            }
            catch (InsufficientExecutionStackException)
            {
                return new UndecidedOutcome(key, kind, display, assumptions, "the default procedure ran out of stack.");
            }
#pragma warning disable CA1031 // KTD19: an unexpected failure in Meta ends this unit as Warrant's bug, not the whole run.
            catch (Exception ex) when (ex is not OperationCanceledException)
#pragma warning restore CA1031
            {
                return new InternalErrorOutcome(key, kind, display, assumptions, $"the VC walker failed unexpectedly: {ex.GetType().Name}: {ex.Message}");
            }
            if (failures.Count > 0)
            {
                var first = failures[0];
                return new NotProvedOutcome(key, kind, display, assumptions, first.Message, first.Goals, first.Node ?? at, []) { Vcs = [.. failures] };
            }
            if (proof.HasExprMVar || proof.HasLevelMVar || proof.HasFVar)
            {
                return new InternalErrorOutcome(key, kind, display, assumptions, $"the default procedure closed {Shown(shell.Name)}, but the proof term still has a hole.");
            }
            Record(unit, walker);
            return AdmitProof(unit, shell, proof, $"the kernel rejected the proof Warrant built for {Shown(shell.Name)}", display, assumptions, admitted, budget);
        }

        /// <summary>
        /// A failing VC's goal as the report shows it, without the hypotheses whose type is <c>True</c> (#240): a path
        /// condition the VC simp set rewrote to <c>True</c>, such as a <c>Spec.Requires</c> under the branch that refutes
        /// it, says nothing. Display only: they are cleared from a fresh copy of the goal (the failing goal may already be
        /// assigned, as omega's is), and the Meta state is restored afterwards.
        /// </summary>
        private static string PrintFailure(MetaM meta, GoalPrinter printer, MVarId goal)
        {
            var saved = meta.SaveState();
            try
            {
                var decl = meta.GetMVarDecl(goal);
                var shown = meta.MkFreshExprMVarAt(decl.LCtx, decl.LocalInstances, meta.InstantiateMVars(decl.Type), MetavarKind.SyntheticOpaque, decl.UserName).Id;
                foreach (var local in decl.LCtx.Decls.ToList())
                {
                    if (!local.IsImplementationDetail && VcWalker.IsTrue(meta.InstantiateMVars(local.Type)))
                    {
                        shown = meta.TryClear(shown, local.FVarId);
                    }
                }
                return printer.PpGoals(meta.MCtx, [shown]);
            }
            finally
            {
                meta.Restore(saved);
            }
        }

        /// <summary>
        /// One well-definedness obligation (KTD26): a callee's precondition is a plain proposition, proved as a decrease
        /// obligation is, by its binders introduced and omega (and, where omega fails, the VC simp set then omega); that a partial operation does not raise, or that a pure
        /// body's implicit arithmetic does not overflow (#244), is a triple over its model, proved by the default procedure
        /// (KTD13, KTD14) and reported at the operation. Null when it was admitted, else the unit's outcome.
        /// </summary>
        private UnitOutcome? ProveWellDefined(
            EngineUnit unit, SpecObligation wd, string display, ImmutableArray<UnitAssumption> assumptions,
            List<KernelDeclaration> admitted, TheoremBudget budget)
        {
            CountSearchOnce();
            var at = VirTree.IdOf(unit.Unit, wd.Node);
            if (wd.Kind != SpecObligationKind.CalleePrecondition)
            {
                var meta = new MetaM(Env, budget.Meta) { KernelLimits = budget.Kernel, Attributes = Attributes, DisplayNames = run.Names };
                var vc = wd.Kind == SpecObligationKind.NoOverflow ? VcKind.ArithmeticOverflow : VcKind.WellDefinedness;
                int before = _contractAssumptions.Count;
                var failure = Default(
                    unit, wd.Theorem, wd.Binders, [], at, () => new VcWalker(meta, Attributes, unit.Unit, vc, at, null),
                    (walker, g) => walker.WellDefined(g), display, assumptions, admitted, budget, meta, new GoalPrinter(Env, run.Names));
                // The operation is not run, so no throw is reached; but the proof may rest on a pure callee's contract, its
                // $contract_spec, which the report lists (#247).
                var recorded = _contractAssumptions.GetRange(before, _contractAssumptions.Count - before);
                _contractAssumptions.RemoveRange(before, recorded.Count);
                _contractAssumptions.AddRange(recorded.Where(a => a.Assumption.Kind == VirAssumptionKind.CalleeContract));
                return failure;
            }
            // #256: a recursive method's call to itself must be within its own Spec.Requires.
            var what = wd.Node is CallExpr { Target: var target } && string.Equals(target, unit.Unit.Key, StringComparison.Ordinal)
                ? "the precondition of the method's recursive call"
                : "the precondition of a method called in a Spec expression";
            return Omega(unit, wd.Theorem, wd.Binders, at, what, display, assumptions, admitted, budget);
        }

        /// <summary>
        /// KTD25: whether a <c>Spec.Requires</c>, under the ones before it, admits no input. Its refutation is tried with
        /// omega under a small budget; if omega finds one, the method fails at that <c>Spec.Requires</c>, since every claim
        /// after it would hold vacuously. Null when no refutation was found, else the unit's outcome.
        /// </summary>
        private UnitOutcome? Refute(
            EngineUnit unit, SpecObligation vacuity, string display, ImmutableArray<UnitAssumption> assumptions, TheoremBudget budget,
            string message = "The contract is unsatisfiable: no input satisfies this Spec.Requires and the ones before it, so every claim after it would hold vacuously (M6 KTD25).")
        {
            var key = unit.Unit.Key;
            var kind = unit.Unit.Kind;
            CountSearchOnce();
            var meta = new MetaM(Env, budget.Meta with { Fuel = Math.Min(budget.Meta.Fuel, VacuityFuel) }) { KernelLimits = budget.Kernel, Attributes = Attributes, DisplayNames = run.Names };
            try
            {
                var goal = meta.MkFreshExprSyntheticOpaqueMVar(vacuity.Theorem.Type);
                meta.OmegaTactic(meta.IntroN(goal.Id, vacuity.Binders).Goal);
            }
            catch (Exception ex) when (ex is MetaResourceException or KernelResourceException)
            {
                // The small budget ran out: no easy refutation, unless the unit's own deadline passed or the run was cancelled.
                return budget.DeadlinePassed || options.CancellationToken.IsCancellationRequested
                    ? budget.Undecided(key, kind, display, assumptions, ex, "checking that the contract's Spec.Requires is satisfiable")
                    : null;
            }
            catch (Exception ex) when (ex is MetaException or InsufficientExecutionStackException)
            {
                return null;
            }
#pragma warning disable CA1031 // KTD19: an unexpected failure in Meta ends this unit as Warrant's bug, not the whole run.
            catch (Exception ex)
#pragma warning restore CA1031
            {
                return new InternalErrorOutcome(key, kind, display, assumptions, $"Meta failed unexpectedly: {ex.GetType().Name}: {ex.Message}");
            }
            return new NotProvedOutcome(key, kind, display, assumptions, message, "", VirTree.IdOf(unit.Unit, vacuity.Node), []);
        }

        /// <summary>
        /// <c>f.$contract_spec</c> from <c>f.$contract</c> at the world <c>Unit</c> (KTD12): <c>fun params h =&gt;
        /// f.$contract Unit params () h</c>, which the kernel checks by unfolding the triple at <c>pure (f params)</c>. Null
        /// when it was admitted, else the unit's outcome.
        /// </summary>
        private UnitOutcome? DeriveSpec(
            EngineUnit unit, ContractObligation contract, TheoremShell spec, string display, ImmutableArray<UnitAssumption> assumptions,
            List<KernelDeclaration> admitted, TheoremBudget budget)
        {
            var binders = new List<(Name Name, Expr Type)>();
            var type = spec.Type;
            for (int i = 0; i < contract.SpecBinders; i++)
            {
                var forall = (ForallExpr)type;
                binders.Add((forall.BinderName, forall.BinderType));
                type = forall.Body;
            }
            int parameters = contract.Binders - 1;
            bool hasPre = contract.SpecBinders > parameters;
            var args = new List<Expr> { SpecWorld };
            for (int i = 0; i < parameters; i++)
            {
                args.Add(Expr.BVar(contract.SpecBinders - 1 - i));
            }
            args.Add(SpecState);
            args.Add(hasPre ? Expr.BVar(0) : TrueIntro);
            Expr proof = Expr.App(Expr.Const(contract.Theorem.Name), [.. args]);
            for (int i = binders.Count - 1; i >= 0; i--)
            {
                proof = Expr.Lam(binders[i].Name, binders[i].Type, proof);
            }
            return AdmitProof(unit, spec, proof, $"the kernel rejected the derivation of {Shown(spec.Name)} from {Shown(contract.Theorem.Name)}", display, assumptions, admitted, budget);
        }

        private static readonly Expr SpecWorld = Expr.Const(Name.Parse("Unit"));
        private static readonly Expr SpecState = Expr.Const(Name.Parse("Unit.unit"));
        private static readonly Expr TrueIntro = Expr.Const(Name.Parse("True.intro"));

        /// <summary>
        /// A proposition proved as a decrease obligation is (M5a KTD15): its binders introduced, then <c>Tactic.Omega()</c>'s
        /// pipeline (and, where that fails, the VC simp set then omega), and the proof admitted. Null when it was admitted, else the unit's outcome, WRT0001 at
        /// <paramref name="at"/> with the goal.
        /// </summary>
        private UnitOutcome? Omega(
            EngineUnit unit, TheoremShell shell, int binders, int? at, string what, string display, ImmutableArray<UnitAssumption> assumptions,
            List<KernelDeclaration> admitted, TheoremBudget budget)
        {
            var key = unit.Unit.Key;
            var kind = unit.Unit.Kind;
            var meta = new MetaM(Env, budget.Meta) { KernelLimits = budget.Kernel, Attributes = Attributes, DisplayNames = run.Names };
            var goal = meta.MkFreshExprSyntheticOpaqueMVar(shell.Type);
            MVarId? current = null;
            MVarId? stated = null;
            Expr proof;
            try
            {
                current = stated = meta.IntroN(goal.Id, binders).Goal;
                // omega alone first; where it fails, the VC simp set, as the default procedure's leftovers get it, then
                // omega again: the simp set decides a conjunct about constants only, such as `7 ≤ 1000` in a recursive
                // call's precondition, which omega alone does not (#256). The simp set is used only where needed: it
                // costs fuel and time on every other precondition (#272).
                var saved = meta.SaveState();
                try
                {
                    meta.OmegaTactic(current.Value);
                }
                catch (MetaException ex) when (ex is not MetaResourceException)
                {
                    meta.Restore(saved);
                    if (meta.SimpAll(current.Value, VcSimpSet.Context(meta)) is { } rest)
                    {
                        current = rest.Goal;
                        meta.OmegaTactic(current.Value);
                    }
                }
                proof = meta.InstantiateMVars(goal);
                TacticFuelUsed = Math.Max(TacticFuelUsed, meta.Budget.FuelUsed);
            }
            catch (Exception ex) when (ex is MetaResourceException or KernelResourceException)
            {
                return budget.Undecided(key, kind, display, assumptions, ex, $"proving {what}");
            }
            catch (InsufficientExecutionStackException)
            {
                return new UndecidedOutcome(key, kind, display, assumptions, $"proving {what} ran out of stack.");
            }
            catch (MetaException ex)
            {
                // The proposition as stated, not what the VC simp set left of it, which can be `⊢ False` (PR #265).
                var failed = stated ?? (ex is TacticException { Goal: { } g } && meta.MCtx.FindDecl(g) is not null ? g : current ?? goal.Id);
                return new NotProvedOutcome(key, kind, display, assumptions, ex.Message, new GoalPrinter(Env, run.Names).PpGoals(meta.MCtx, [failed]), at, []);
            }
#pragma warning disable CA1031 // KTD19: an unexpected failure in Meta ends this unit as Warrant's bug, not the whole run.
            catch (Exception ex)
#pragma warning restore CA1031
            {
                return new InternalErrorOutcome(key, kind, display, assumptions, $"Meta failed unexpectedly: {ex.GetType().Name}: {ex.Message}");
            }
            if (proof.HasExprMVar || proof.HasLevelMVar || proof.HasFVar)
            {
                return new InternalErrorOutcome(key, kind, display, assumptions, $"omega closed {Shown(shell.Name)}, but the proof term still has a hole.");
            }
            return AdmitProof(unit, shell, proof, $"the kernel rejected the proof Warrant built for {Shown(shell.Name)}", display, assumptions, admitted, budget);
        }

        /// <summary>
        /// A generated declaration as messages name it (#272): its display name, such as <c>F (well-definedness 1)</c>,
        /// never its Lean constant.
        /// </summary>
        private string Shown(Name name) => run.Shown(name);

        /// <summary>Admits a proved obligation into the run's fork. Null when it was admitted, else the unit's outcome.</summary>
        private UnitOutcome? AdmitProof(
            EngineUnit unit, TheoremShell shell, Expr proof, string rejected, string display, ImmutableArray<UnitAssumption> assumptions,
            List<KernelDeclaration> admitted, TheoremBudget budget)
        {
            try
            {
                AddDeclaration(unit.Unit.Key, shell.WithProof(proof), admitted, budget);
                return null;
            }
            catch (KernelResourceException ex)
            {
                return budget.Undecided(unit.Unit.Key, unit.Unit.Kind, display, assumptions, ex, $"the kernel checked {Shown(shell.Name)}");
            }
            catch (KernelException ex)
            {
                return new InternalErrorOutcome(unit.Unit.Key, unit.Unit.Kind, display, assumptions, $"{rejected}: {ex.Message}");
            }
        }
    }
}
