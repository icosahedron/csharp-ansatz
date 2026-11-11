using System.Collections.Immutable;
using Warrant.Cic;
using Warrant.Engine.Reports;
using Warrant.Kernel;
using Warrant.Meta;
using Warrant.Semantics;
using Warrant.Vir;

namespace Warrant.Engine;

public static partial class Pipeline
{
    /// <summary>
    /// The first line of the message of a contract obligation that waits for its default procedure: VC generation, then
    /// the VC simp set, then omega (M6 KTD13, KTD14), which M6 U11 builds.
    /// </summary>
    internal const string DefaultProcedurePending =
        "the default procedure (Tactic.VcGen(), then simp and omega) is not available until M6 U11, so nothing proves this obligation yet";

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

            foreach (var wd in contract.WellDefinedness)
            {
                if (Admit(wd.Theorem, () => ProveWellDefined(unit, wd, display, assumptions, admitted, budget)) is { } failure)
                {
                    return failure;
                }
            }
            if (Admit(contract.Theorem, () => ProveContract(unit, contract, display, assumptions, admitted, budget)) is { } unproved)
            {
                return unproved;
            }
            if (contract.Spec is { } spec && Admit(spec, () => DeriveSpec(unit, contract, spec, display, assumptions, admitted, budget)) is { } underived)
            {
                return underived;
            }
            return new TranslatedOutcome(key, kind, display, assumptions, [.. admitted]);
        }

        /// <summary>The names a contract obligation's binders are introduced under: the world, <c>self</c>, then the parameters.</summary>
        private static List<Name> BinderNames(EngineUnit unit)
        {
            List<Name> names = [Name.From("σ")];
            if (unit.Unit.Self is not null)
            {
                names.Add(Name.From("self"));
            }
            names.AddRange((unit.Unit.Params ?? VirList<VirParam>.Empty).Select(p => Name.From(p.Name)));
            return names;
        }

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
        /// (KTD16), and the proof admitted as <c>f.$contract</c>. Without a script it waits for the default procedure (M6
        /// U11), so it is not proved. Null when it was admitted, else the unit's outcome.
        /// </summary>
        private UnitOutcome? ProveContract(
            EngineUnit unit, ContractObligation contract, string display, ImmutableArray<UnitAssumption> assumptions,
            List<KernelDeclaration> admitted, TheoremBudget budget)
        {
            var key = unit.Unit.Key;
            var kind = unit.Unit.Kind;
            var shell = contract.Theorem;
            CountSearchOnce();
            var meta = new MetaM(Env, budget.Meta) { KernelLimits = budget.Kernel, Attributes = Attributes, DisplayNames = run.Names };
            var printer = new GoalPrinter(Env, run.Names);
            if (contract.Script is not { } script)
            {
                return Pending(unit, shell, contract.Binders, BinderNames(unit), null, $"The contract obligation was not proved: {DefaultProcedurePending}; a [ProofFor] script that does not start with Tactic.VcGen() can prove it now.", display, assumptions, budget);
            }
            var recorder = options.TacticTrace is null
                ? null
                : new TacticRecorder(goals => printer.PpGoals(meta.MCtx, goals), node => VirTree.IdOf(unit.Unit, node));
            (Expr? Proof, UnitOutcome? Failure) found;
            try
            {
                found = Search(unit, shell, script, BinderNames(unit), display, assumptions, budget, meta, printer, new TacticRunner(new TacticM(meta, []), recorder), () => []);
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
            return AdmitProof(unit, shell, found.Proof!, $"the kernel rejected the proof Warrant built for the contract obligation {shell.Name}", display, assumptions, admitted, budget)
                ?? (ProofTerms.IsAdmittedAs(Env, shell) ? null : new FailedOutcome(key, kind, display, assumptions, $"the kernel admitted {shell.Name} with a type other than its statement."));
        }

        /// <summary>
        /// One well-definedness obligation (KTD26): a callee's precondition is a plain proposition, proved as a decrease
        /// obligation is, by its binders introduced and omega; that a partial operation does not raise is a triple over its
        /// model, which waits for the default procedure (M6 U11). Null when it was admitted, else the unit's outcome.
        /// </summary>
        private UnitOutcome? ProveWellDefined(
            EngineUnit unit, SpecObligation wd, string display, ImmutableArray<UnitAssumption> assumptions,
            List<KernelDeclaration> admitted, TheoremBudget budget)
        {
            CountSearchOnce();
            var at = VirTree.IdOf(unit.Unit, wd.Node);
            if (wd.Kind != SpecObligationKind.CalleePrecondition)
            {
                return Pending(unit, wd.Theorem, wd.Binders, [], at, $"The well-definedness of a Spec expression (that this operation does not raise) was not proved: {DefaultProcedurePending}.", display, assumptions, budget);
            }
            return Omega(unit, wd.Theorem, wd.Binders, at, "the precondition of a method called in a Spec expression", display, assumptions, admitted, budget);
        }

        /// <summary>
        /// KTD25: whether a <c>Spec.Requires</c>, under the ones before it, admits no input. Its refutation is tried with
        /// omega under a small budget; if omega finds one, the method fails at that <c>Spec.Requires</c>, since every claim
        /// after it would hold vacuously. Null when no refutation was found, else the unit's outcome.
        /// </summary>
        private UnitOutcome? Refute(EngineUnit unit, SpecObligation vacuity, string display, ImmutableArray<UnitAssumption> assumptions, TheoremBudget budget)
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
            return new NotProvedOutcome(
                key, kind, display, assumptions,
                "The contract is unsatisfiable: no input satisfies this Spec.Requires and the ones before it, so every claim after it would hold vacuously (M6 KTD25).",
                "", VirTree.IdOf(unit.Unit, vacuity.Node), []);
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
            return AdmitProof(unit, spec, proof, $"the kernel rejected the derivation of {spec.Name} from {contract.Theorem.Name}", display, assumptions, admitted, budget);
        }

        private static readonly Expr SpecWorld = Expr.Const(Name.Parse("Unit"));
        private static readonly Expr SpecState = Expr.Const(Name.Parse("Unit.unit"));
        private static readonly Expr TrueIntro = Expr.Const(Name.Parse("True.intro"));

        /// <summary>
        /// A proposition proved as a decrease obligation is (M5a KTD15): its binders introduced, then <c>Tactic.Omega()</c>'s
        /// pipeline, and the proof admitted. Null when it was admitted, else the unit's outcome, WRT0001 at
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
            Expr proof;
            try
            {
                current = meta.IntroN(goal.Id, binders).Goal;
                meta.OmegaTactic(current.Value);
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
                var failed = ex is TacticException { Goal: { } g } && meta.MCtx.FindDecl(g) is not null ? g : current ?? goal.Id;
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
                return new InternalErrorOutcome(key, kind, display, assumptions, $"omega closed {shell.Name}, but the proof term still has a hole.");
            }
            return AdmitProof(unit, shell, proof, $"the kernel rejected the proof Warrant built for {shell.Name}", display, assumptions, admitted, budget);
        }

        /// <summary>
        /// An obligation nothing can prove yet: WRT0001 at <paramref name="at"/>, with its goal after its binders are
        /// introduced under <paramref name="names"/> (or their own names).
        /// </summary>
        private NotProvedOutcome Pending(
            EngineUnit unit, TheoremShell shell, int binders, IReadOnlyList<Name> names, int? at, string message, string display,
            ImmutableArray<UnitAssumption> assumptions, TheoremBudget budget)
        {
            string goals;
            try
            {
                var meta = new MetaM(Env, budget.Meta) { KernelLimits = budget.Kernel, Attributes = Attributes, DisplayNames = run.Names };
                var goal = meta.MkFreshExprSyntheticOpaqueMVar(shell.Type);
                var introduced = meta.IntroN(goal.Id, binders, names).Goal;
                goals = new GoalPrinter(Env, run.Names).PpGoals(meta.MCtx, [introduced]);
            }
            catch (Exception ex) when (ex is MetaException or KernelException or InsufficientExecutionStackException)
            {
                goals = "";
            }
            return new NotProvedOutcome(unit.Unit.Key, unit.Unit.Kind, display, assumptions, message, goals, at, []);
        }

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
                return budget.Undecided(unit.Unit.Key, unit.Unit.Kind, display, assumptions, ex, $"the kernel checked {shell.Name}");
            }
            catch (KernelException ex)
            {
                return new InternalErrorOutcome(unit.Unit.Key, unit.Unit.Kind, display, assumptions, $"{rejected}: {ex.Message}");
            }
        }
    }
}
