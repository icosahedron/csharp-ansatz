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
    private static readonly Name BoolFalse = Name.Parse("Bool.false");
    private static readonly Name EqName = Name.Parse("Eq");
    private static readonly Name LtName = Name.Parse("LT.lt");
    private static readonly Name LeName = Name.Parse("LE.le");

    /// <summary>
    /// Where one unit is admitted (KTD8): the run's fork for a definition or type, a theorem's own fork of its level's
    /// environment for a theorem. What the unit admits is recorded here and merged into the run by the caller.
    /// </summary>
    private sealed partial class Scope(RunState run, KernelEnvironment env, Sidecar attributes)
    {
        private readonly EngineOptions options = run.Options;

        private KernelEnvironment Env => env;

        private Sidecar Attributes => attributes;

        private TheoremBudget? _budget;

        /// <summary>The environment the unit admits into.</summary>
        public KernelEnvironment Environment => env;

        /// <summary>The most tactic fuel one successful proof search of the unit used (M5b KTD13).</summary>
        public long TacticFuelUsed { get; private set; }

        /// <summary>
        /// Whether a fixed proof ran out of a kernel resource and the next one was tried, so the outcome depends on the
        /// exact kernel budget even when it is a proof (M5b KTD13).
        /// </summary>
        public bool BudgetExact { get; private set; }

        /// <summary>Whether the unit's deadline has passed; false for a unit that never started its budget.</summary>
        public bool DeadlinePassed => _budget?.DeadlinePassed ?? false;

        private bool _searched;

        public UnitOutcome Admit(TranslatedUnit translated)
        {
            var unit = run.Units[translated.Key];
            var display = translated.DisplayName;
            var assumptions = run.Assumptions(unit);
            if (translated.Theorem is { } shell)
            {
                run.CountSearch();
                if (shell.Script is { } script && run.ConstOutsideDependencies(unit, script) is { } outside)
                {
                    var owner = RunState.Display(run.Units[outside.Owner]);
                    return new FailedOutcome(
                        unit.Unit.Key, unit.Unit.Kind, display, assumptions,
                        $"Malformed proof script: Lean.Const(\"{outside.Constant}\") names a constant of '{OutcomeText.ShortName(owner)}', which this theorem does not depend on; name it with nameof({OutcomeText.ShortName(owner)}) instead.")
                    {
                        Code = FailedOutcome.MalformedScriptCode,
                        Node = VirTree.IdOf(unit.Unit, outside.Node),
                    };
                }
                var budget = _budget = new TheoremBudget(options, shell.Budget);
                _searched = true;
                _theorem = true;
                // #236: the statement's well-definedness obligations, each by the default procedure as a contract's are,
                // whatever proves the claim itself; the theorem is proved only when all of them are.
                var wellDefined = new List<KernelDeclaration>();
                foreach (var wd in translated.WellDefinedness)
                {
                    if (ProveWellDefined(unit, wd, display, assumptions, wellDefined, budget) is { } failure)
                    {
                        return failure;
                    }
                }
                var outcome = shell.Script is null && shell.Statement.Instance is not null
                    ? Compute(unit, shell, display, assumptions, budget)
                    : RunScript(unit, shell, display, assumptions, budget);
                return outcome is ProvedOutcome proved ? proved with { WellDefinedness = [.. wellDefined.Cast<TheoremDecl>()] } : outcome;
            }
            var admitted = new List<KernelDeclaration>();
            var definitionBudget = _budget = new TheoremBudget(options, null);
            if (translated.Recursion is { } recursion)
            {
                return AdmitRecursive(unit, translated, recursion, assumptions, admitted, definitionBudget);
            }
            foreach (var declaration in translated.Declarations)
            {
                try
                {
                    AddDeclaration(unit.Unit.Key, declaration, admitted, definitionBudget);
                    if (declaration is DefinitionDecl { Value: { Hints.Kind: ReducibilityHintsKind.Abbrev } abbrev })
                    {
                        // KTD9: an open enum and its members are `abbrev`s (docs/m4/05), reducible as Lean's are, so simp
                        // and instance resolution see through them (docs/m5a/05).
                        Attributes.SetReducibilityStatus(abbrev.Name, ReducibilityStatus.Reducible);
                    }
                    if (declaration is InductiveDecl inductive)
                    {
                        // KTD8: casesOn and ctorIdx, which Lean's elaborator would have made, each built after the last is admitted.
                        foreach (var construction in Constructions.For(Env, inductive))
                        {
                            AddDeclaration(unit.Unit.Key, construction, admitted, definitionBudget);
                            Constructions.Register(Attributes, construction.Value);
                        }
                    }
                }
                catch (KernelResourceException ex)
                {
                    return definitionBudget.Undecided(unit.Unit.Key, unit.Unit.Kind, display, assumptions, ex, "the kernel checked the definition");
                }
                catch (KernelException ex)
                {
                    return new FailedOutcome(unit.Unit.Key, unit.Unit.Kind, display, assumptions, ex.Message);
                }
            }
            if (translated.Contract is { } contract)
            {
                // M6 KTD12: the definition, then its contract obligation, as a recursive method's decrease proofs.
                return AdmitContract(unit, translated, contract, assumptions, admitted, definitionBudget);
            }
            if (translated.MemberContract is { } member)
            {
                return AdmitMemberContract(unit, translated, member, assumptions, admitted, definitionBudget);
            }
            return new TranslatedOutcome(unit.Unit.Key, unit.Unit.Kind, display, assumptions, [.. admitted]);
        }

        /// <summary>
        /// A contract-class member's checks (M6 U19): each of its <c>Spec</c> calls checked not to be unsatisfiable together
        /// with the ones before it (KTD25), then the well-definedness of its <c>Spec</c> expressions (KTD26). The contract
        /// itself is never proved: it is a hypothesis of each caller's obligation (KTD9).
        /// </summary>
        private UnitOutcome AdmitMemberContract(
            EngineUnit unit,
            TranslatedUnit translated,
            MemberContract member,
            ImmutableArray<UnitAssumption> assumptions,
            List<KernelDeclaration> admitted,
            TheoremBudget budget)
        {
            var display = translated.DisplayName;
            if (CachedProofs is null)
            {
                foreach (var vacuity in member.Vacuity)
                {
                    const string unsatisfiable = "The contract is unsatisfiable: no result satisfies this Spec call together with the ones before it, so every method that calls the member would hold vacuously after the call (M6 KTD25).";
                    if (Refute(unit, vacuity, display, assumptions, budget, unsatisfiable) is { } refuted)
                    {
                        return refuted;
                    }
                }
            }
            foreach (var wd in member.WellDefinedness)
            {
                UnitOutcome? Prove() => ProveWellDefined(unit, wd, display, assumptions, admitted, budget);
                if ((CachedProofs is null ? Prove() : AdmitCached(unit, wd.Theorem, display, assumptions, admitted, budget, Prove)) is { } failure)
                {
                    return failure;
                }
            }
            return new TranslatedOutcome(unit.Unit.Key, unit.Unit.Kind, display, assumptions, [.. admitted]);
        }

        /// <summary>
        /// A recursive method (M5a KTD14, KTD15): each decrease theorem proved by the omega pipeline and admitted, then the
        /// definition, which refers to them, marked irreducible for Meta as Lean marks its well-founded definitions, then
        /// the equation lemma with its bare <c>Nat.fix_eq</c> proof. A decrease theorem that is not proved is WRT0001 at
        /// its call, with its goal; an equation lemma the kernel rejects fails the unit. All of it runs in the unit's one
        /// budget, and running out of it anywhere is WRT0006 (M5b KTD11).
        /// </summary>
        private UnitOutcome AdmitRecursive(
            EngineUnit unit,
            TranslatedUnit translated,
            RecursiveDefinition recursion,
            ImmutableArray<UnitAssumption> assumptions,
            List<KernelDeclaration> admitted,
            TheoremBudget budget)
        {
            var key = unit.Unit.Key;
            var kind = unit.Unit.Kind;
            var display = translated.DisplayName;
            foreach (var decrease in recursion.Decreases)
            {
                var failure = CachedProofs is null
                    ? ProveDecrease(unit, decrease, display, assumptions, admitted, budget)
                    : AdmitCached(unit, decrease.Theorem, display, assumptions, admitted, budget, () => ProveDecrease(unit, decrease, display, assumptions, admitted, budget));
                if (failure is not null)
                {
                    return failure;
                }
            }
            try
            {
                foreach (var declaration in translated.Declarations)
                {
                    AddDeclaration(key, declaration, admitted, budget);
                }
                Attributes.SetReducibilityStatus(translated.Name, ReducibilityStatus.Irreducible);
            }
            catch (KernelResourceException ex)
            {
                return budget.Undecided(key, kind, display, assumptions, ex, "the kernel checked the definition");
            }
            catch (KernelException ex)
            {
                return new FailedOutcome(key, kind, display, assumptions, ex.Message);
            }
            UnitOutcome? Equation()
            {
                try
                {
                    AddDeclaration(key, recursion.Equation.WithProof(recursion.EquationProof), admitted, budget);
                    return null;
                }
                catch (KernelResourceException ex)
                {
                    return budget.Undecided(key, kind, display, assumptions, ex, $"the kernel checked the equation lemma {recursion.Equation.Name}");
                }
                catch (KernelException ex)
                {
                    return new FailedOutcome(key, kind, display, assumptions, $"the kernel rejected the equation lemma {recursion.Equation.Name}: {ex.Message}");
                }
            }

            var equation = CachedProofs is null ? Equation() : AdmitCached(unit, recursion.Equation, display, assumptions, admitted, budget, Equation);
            return equation ?? new TranslatedOutcome(key, kind, display, assumptions, [.. admitted]);
        }

        /// <summary>
        /// One decrease theorem (KTD15): its binders introduced under their own names, then <c>Tactic.Omega()</c>'s
        /// pipeline; the proof the kernel admits. Null when it was admitted, else the unit's outcome.
        /// </summary>
        private UnitOutcome? ProveDecrease(
            EngineUnit unit,
            DecreaseObligation decrease,
            string display,
            ImmutableArray<UnitAssumption> assumptions,
            List<KernelDeclaration> admitted,
            TheoremBudget budget)
        {
            var key = unit.Unit.Key;
            var kind = unit.Unit.Kind;
            var shell = decrease.Theorem;
            if (!_searched)
            {
                _searched = true;
                run.CountSearch();
            }
            var meta = new MetaM(Env, budget.Meta) { KernelLimits = budget.Kernel, Attributes = Attributes, DisplayNames = run.Names };
            var goal = meta.MkFreshExprSyntheticOpaqueMVar(shell.Type);
            MVarId? current = null;
            Expr proof;
            try
            {
                var introduced = meta.IntroN(goal.Id, decrease.Binders).Goal;
                current = introduced;
                meta.OmegaTactic(introduced);
                proof = meta.InstantiateMVars(goal);
                TacticFuelUsed = Math.Max(TacticFuelUsed, meta.Budget.FuelUsed);
            }
            catch (Exception ex) when (ex is MetaResourceException or KernelResourceException)
            {
                return budget.Undecided(key, kind, display, assumptions, ex, $"proving the decrease of {Describe(unit, decrease)}");
            }
            catch (InsufficientExecutionStackException)
            {
                return new UndecidedOutcome(key, kind, display, assumptions, "proving a decrease obligation ran out of stack.");
            }
            catch (MetaException ex)
            {
                var failed = ex is TacticException { Goal: { } g } && meta.MCtx.FindDecl(g) is not null ? g : current ?? goal.Id;
                var printer = new GoalPrinter(Env, run.Names);
                return new NotProvedOutcome(key, kind, display, assumptions, ex.Message, printer.PpGoals(meta.MCtx, [failed]), VirTree.IdOf(unit.Unit, decrease.Call), [])
                {
                    Decrease = new DecreaseFailure(decrease.Index, VirTree.IdOf(unit.Unit, decrease.Call), VirTree.IdOf(unit.Unit, decrease.Measure)),
                };
            }
#pragma warning disable CA1031 // KTD19: an unexpected failure in Meta ends this unit as Warrant's bug, not the whole run.
            catch (Exception ex)
#pragma warning restore CA1031
            {
                return new InternalErrorOutcome(key, kind, display, assumptions, $"Meta failed unexpectedly: {ex.GetType().Name}: {ex.Message}");
            }
            if (proof.HasExprMVar || proof.HasLevelMVar || proof.HasFVar)
            {
                return new InternalErrorOutcome(key, kind, display, assumptions, $"omega closed the decrease obligation {shell.Name}, but the proof term still has a hole.");
            }
            try
            {
                AddDeclaration(key, shell.WithProof(proof), admitted, budget);
            }
            catch (KernelResourceException ex)
            {
                return budget.Undecided(key, kind, display, assumptions, ex, "the kernel checked a decrease proof");
            }
            catch (KernelException ex)
            {
                return new InternalErrorOutcome(key, kind, display, assumptions, $"the kernel rejected the decrease proof Warrant built for {shell.Name}: {ex.Message}");
            }
            return null;
        }

        private static string Describe(EngineUnit unit, DecreaseObligation decrease) => $"recursive call {decrease.Index} of {RunState.Display(unit)}";

        /// <summary>
        /// Admits one of a definition's or type's declarations into the run's fork and records <paramref name="key"/> as the
        /// owner of its constants (KTD33): the fork keeps them even if a later step of the unit fails or runs out. A
        /// theorem's well-definedness theorems (#236) go into its own fork only, and reach the run with its outcome.
        /// </summary>
        private void AddDeclaration(string key, KernelDeclaration declaration, List<KernelDeclaration> admitted, TheoremBudget budget)
        {
            Kernel.Kernel.Add(Env, declaration, budget.Kernel);
            if (!_theorem)
            {
                run.Admitted.Add(declaration);
                run.Own(key, declaration);
            }
            admitted.Add(declaration);
        }

        /// <summary>
        /// Whether the unit is a theorem, which runs on a worker in its own fork (KTD8): what it admits reaches the run
        /// with its outcome, in <see cref="RunState"/>'s admission of its level, never from the worker.
        /// </summary>
        private bool _theorem;

        /// <summary>
        /// A closed theorem with no script (M4, KTD12): tries <c>rfl</c>, then <c>decide</c>; if neither is admitted, reduces
        /// <c>decide P D</c> to tell false from undecided.
        /// </summary>
        private UnitOutcome Compute(EngineUnit unit, TheoremShell shell, string display, ImmutableArray<UnitAssumption> assumptions, TheoremBudget budget)
        {
            var key = unit.Unit.Key;
            foreach (var (kind, proof) in new[] { (ProofKind.Rfl, ProofTerms.Rfl(shell.Statement)), (ProofKind.Decide, ProofTerms.Decide(shell.Statement)) })
            {
                if (proof is null)
                {
                    continue;
                }
                var declaration = shell.WithProof(proof);
                try
                {
                    Kernel.Kernel.Add(Env, declaration, budget.Kernel);
                }
                catch (KernelResourceException ex) when (budget.Kernel.CancellationToken.IsCancellationRequested || DateTimeOffset.UtcNow >= budget.Kernel.Deadline)
                {
                    // KTD12: a cancellation or a passed deadline is shared by every method, so the next one cannot
                    // succeed. Running out of fuel falls through to the next method, which gets its own fuel, as in M5a.
                    return budget.Undecided(key, unit.Unit.Kind, display, assumptions, ex, $"the kernel checked the {kind.ToString().ToLowerInvariant()} proof");
                }
                catch (KernelException ex)
                {
                    // Running out of fuel or a numeral's size falls through to the next proof, which more budget
                    // might not have needed.
                    BudgetExact |= ex is KernelResourceException;
                    continue;
                }
                if (!ProofTerms.IsAdmittedAs(Env, shell))
                {
                    return new FailedOutcome(key, unit.Unit.Kind, display, assumptions, $"the kernel admitted {shell.Name} with a type other than its statement.");
                }
                return new ProvedOutcome(key, unit.Unit.Kind, display, assumptions, kind, declaration);
            }

            Expr decided;
            try
            {
                decided = new TypeChecker(Env, limits: budget.Kernel).Whnf(Operators.Decide(shell.Statement));
            }
            catch (KernelResourceException ex)
            {
                return new UndecidedOutcome(key, unit.Unit.Kind, display, assumptions, $"the kernel ran out of resources deciding the claim: {budget.Exhausted(ex)}.") { Exhausted = budget.Which(ex) };
            }
            catch (KernelException ex)
            {
                return new UndecidedOutcome(key, unit.Unit.Kind, display, assumptions, $"the kernel could not decide the claim: {ex.Message}");
            }
            catch (InsufficientExecutionStackException ex)
            {
                return new UndecidedOutcome(key, unit.Unit.Kind, display, assumptions, $"the kernel ran out of stack deciding the claim: {ex.Message}");
            }
            if (decided is ConstExpr { Name: var b } && b == BoolFalse)
            {
                return new FalseOutcome(key, unit.Unit.Kind, display, assumptions, Sides(unit, shell));
            }
            return new UndecidedOutcome(key, unit.Unit.Kind, display, assumptions, "the claim does not compute to false, and neither proof was accepted.");
        }

        /// <summary>
        /// A theorem with a script, or with parameters (docs/m5a/04, "The loop"; KTD19): the goal <c>?g : statement</c>, the
        /// theorem's own parameters introduced under their C# names, then the script; with no goals left, the instantiated
        /// <c>?g</c> goes to the kernel. Each way it can fail is caught as what it is.
        /// </summary>
        /// <exception cref="OperationCanceledException">The run was cancelled during the counterexample search (KTD32).</exception>
        private UnitOutcome RunScript(EngineUnit unit, TheoremShell shell, string display, ImmutableArray<UnitAssumption> assumptions, TheoremBudget budget)
        {
            var meta = new MetaM(Env, budget.Meta) { KernelLimits = budget.Kernel, Attributes = Attributes, DisplayNames = run.Names };
            var printer = new GoalPrinter(Env, run.Names);
            var recorder = options.TacticTrace is null
                ? null
                : new TacticRecorder(goals => printer.PpGoals(meta.MCtx, goals), node => VirTree.IdOf(unit.Unit, node));
            try
            {
                return RunScript(unit, shell, display, assumptions, budget, meta, printer, new TacticRunner(new TacticM(meta, []), recorder));
            }
            finally
            {
                if (recorder is not null)
                {
                    options.TacticTrace!(unit.Unit.Key, recorder.Steps);
                }
            }
        }

        private UnitOutcome RunScript(
            EngineUnit unit, TheoremShell shell, string display, ImmutableArray<UnitAssumption> assumptions, TheoremBudget budget,
            MetaM meta, GoalPrinter printer, TacticRunner runner)
        {
            var key = unit.Unit.Key;
            var kind = unit.Unit.Kind;
            var parameters = unit.Unit.Params ?? VirList<VirParam>.Empty;
            var (proof, failure) = Search(
                unit, shell, shell.Script ?? VirList<TacticNode>.Empty, [.. parameters.Select(p => Name.From(p.Name))], display, assumptions, budget, meta, printer, runner,
                () => Counterexample.Search(Env, unit.Unit, shell, run.Definitions, options.CancellationToken));
            if (failure is not null)
            {
                return failure;
            }
            var declaration = shell.WithProof(proof!);
            try
            {
                Kernel.Kernel.Add(Env, declaration, budget.Kernel);
            }
            catch (KernelResourceException ex)
            {
                return budget.Undecided(key, kind, display, assumptions, ex, "the kernel checked the proof");
            }
            catch (KernelException ex)
            {
                return new InternalErrorOutcome(key, kind, display, assumptions, $"the kernel rejected the proof Warrant built: {ex.Message}");
            }
            if (!ProofTerms.IsAdmittedAs(Env, shell))
            {
                return new FailedOutcome(key, kind, display, assumptions, $"the kernel admitted {shell.Name} with a type other than its statement.");
            }
            return new ProvedOutcome(key, kind, display, assumptions, ProofKind.Script, declaration);
        }

        /// <summary>
        /// A proof script's search (docs/m5a/04, "The loop"; KTD19): the goal <c>?g : statement</c>, its first binders
        /// introduced under <paramref name="names"/>, then <paramref name="script"/>; the instantiated <c>?g</c> when no goal
        /// is left, with no hole or free variable, else the unit's outcome. Each way it can fail is caught as what it is.
        /// </summary>
        private (Expr? Proof, UnitOutcome? Failure) Search(
            EngineUnit unit, TheoremShell shell, VirList<TacticNode> script, List<Name> names, string display, ImmutableArray<UnitAssumption> assumptions,
            TheoremBudget budget, MetaM meta, GoalPrinter printer, TacticRunner runner, Func<ImmutableArray<CounterexampleValue>> counterexample)
        {
            var key = unit.Unit.Key;
            var kind = unit.Unit.Kind;
            var tactics = runner.State;

            (Expr?, UnitOutcome?) NotProved(string message, IEnumerable<MVarId> goals, TacticNode? at) => (null, new NotProvedOutcome(
                key, kind, display, assumptions, message, printer.PpGoals(meta.MCtx, goals), at is null ? null : VirTree.IdOf(unit.Unit, at),
                counterexample()));

            Expr proof;
            try
            {
                var goal = meta.MkFreshExprSyntheticOpaqueMVar(shell.Type);
                tactics.Goals = [goal.Id];
                if (names.Count > 0)
                {
                    tactics.LiftMetaTactic1(g => meta.IntroN(g, names.Count, names).Goal);
                }
                foreach (var node in script)
                {
                    runner.Run(node);
                }
                if (tactics.GetUnsolvedGoals() is { IsEmpty: false } unsolved)
                {
                    return NotProved("unsolved goals", unsolved, null);
                }
                proof = meta.InstantiateMVars(goal);
                TacticFuelUsed = Math.Max(TacticFuelUsed, meta.Budget.FuelUsed);
            }
            catch (TacticUnavailableException ex)
            {
                return NotProved(ex.Message, tactics.GetUnsolvedGoals(), runner.FailedAt);
            }
            catch (Exception ex) when (ex is MetaResourceException or KernelResourceException)
            {
                return (null, budget.Undecided(key, kind, display, assumptions, ex, "running the proof script"));
            }
            catch (InsufficientExecutionStackException)
            {
                return (null, new UndecidedOutcome(key, kind, display, assumptions, "the proof script ran out of stack."));
            }
            catch (MetaException ex) when (runner.FailedAt is { } failedAt)
            {
                var goals = ex is TacticException { Goal: { } g } && meta.MCtx.FindDecl(g) is not null ? [g] : tactics.GetUnsolvedGoals();
                return NotProved(ex.Message, goals, failedAt);
            }
#pragma warning disable CA1031 // KTD19: an unexpected failure in Meta ends this theorem as Warrant's bug, not the whole run.
            catch (Exception ex) when (ex is not OperationCanceledException)
#pragma warning restore CA1031
            {
                return (null, new InternalErrorOutcome(key, kind, display, assumptions, $"Meta failed unexpectedly: {ex.GetType().Name}: {ex.Message}"));
            }

            if (options.TamperWithProof is { } tamper)
            {
                proof = tamper(proof);
            }
            if (proof.HasExprMVar || proof.HasLevelMVar || proof.HasFVar)
            {
                return (null, new InternalErrorOutcome(key, kind, display, assumptions, "the proof script closed every goal, but the proof term still has a hole or a free variable."));
            }
            return (proof, null);
        }

        /// <summary>
        /// The two sides of a false claim that is one comparison, in source order, with their values read back. The
        /// statement's proposition has them as <c>@Eq T a b</c>, <c>@LT.lt T i a b</c> or <c>@LE.le T i a b</c>, with
        /// <c>&gt;</c> and <c>&gt;=</c> swapped; record and closed-type equality are not on their operands, so their values
        /// are unknown.
        /// </summary>
        private ImmutableArray<ReadBackSide> Sides(EngineUnit unit, TheoremShell shell)
        {
            if (unit.Unit.Statement is not CompareExpr { Op: not CompareOp.Ne } compare)
            {
                return [];
            }
            int Id(VirNode node) =>
                VirTree.IdOf(unit.Unit, node) ?? throw new InvalidOperationException("a statement operand is not among the unit's nodes");

            (Expr Type, Expr Left, Expr Right)? operands = null;
            if (compare.Kind is not (CompareKind.Record or CompareKind.Closed) && shell.Type.GetAppFn() is ConstExpr head)
            {
                var args = shell.Type.GetAppArgs();
                var swapped = compare.Op is CompareOp.Gt or CompareOp.Ge;
                if (head.Name == EqName && compare.Op == CompareOp.Eq && args.Length == 3)
                {
                    operands = (args[0], args[1], args[2]);
                }
                else if ((head.Name == LtName && compare.Op is CompareOp.Lt or CompareOp.Gt
                    || head.Name == LeName && compare.Op is CompareOp.Le or CompareOp.Ge) && args.Length == 4)
                {
                    operands = swapped ? (args[0], args[3], args[2]) : (args[0], args[2], args[3]);
                }
            }

            ReadBackSide Side(VirExpr node, Expr? term)
            {
                var id = Id(node);
                var value = term is null || operands is not { } o
                    ? new UnknownValue("the comparison's operands are not read back")
                    : ReadBack.Core(Env, term, o.Type, options.Kernel);
                return new ReadBackSide(id, value);
            }

            return [Side(compare.L, operands?.Left), Side(compare.R, operands?.Right)];
        }
    }
}
