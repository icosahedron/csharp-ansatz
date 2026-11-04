using System.Collections.Immutable;
using System.Globalization;
using Warrant.Cic;
using Warrant.Engine.Reports;
using Warrant.Kernel;
using Warrant.Meta;
using Warrant.Semantics;
using Warrant.Vir;

namespace Warrant.Engine;

/// <summary>
/// The engine's pipeline (docs/m4/07, "The engine"; docs/m5a/04, "The loop"): translates VIR units, admits their
/// declarations in dependency order into one fork of the bundle, proves theorems, and classifies every unit's outcome
/// independently of the others.
/// </summary>
public static class Pipeline
{
    private static readonly Name BoolFalse = Name.Parse("Bool.false");
    private static readonly Name EqName = Name.Parse("Eq");
    private static readonly Name LtName = Name.Parse("LT.lt");
    private static readonly Name LeName = Name.Parse("LE.le");

    /// <summary>Runs the engine over a set of units, with the default options except for the kernel's limits.</summary>
    /// <param name="units">
    /// The units, typically in extraction order. A unit whose dependency is missing, cannot be translated or is rejected by
    /// the kernel fails, and the units depending on it are skipped; the others proceed.
    /// </param>
    /// <param name="bundle">The checked, frozen semantics bundle.</param>
    /// <param name="limits">The fuel for every kernel call; <see cref="KernelLimits.Corpus"/> when null.</param>
    /// <returns>One outcome per unit, in input order, and the environment the run admitted into.</returns>
    /// <exception cref="ArgumentException">Two units have the same key.</exception>
    public static EngineResult Run(IEnumerable<EngineUnit> units, SemanticsBundle bundle, KernelLimits? limits = null) =>
        Run(units, bundle, EngineOptions.Default with { Kernel = limits ?? KernelLimits.Corpus });

    /// <summary>Runs the engine over a set of units.</summary>
    /// <param name="units">
    /// The units, typically in extraction order. A unit whose dependency is missing, cannot be translated or is rejected by
    /// the kernel fails, and the units depending on it are skipped; the others proceed.
    /// </param>
    /// <param name="bundle">The checked, frozen semantics bundle.</param>
    /// <param name="options">The budgets and the attribute sidecar.</param>
    /// <returns>One outcome per unit, in input order, and the environment the run admitted into.</returns>
    /// <exception cref="ArgumentException">Two units have the same key.</exception>
    public static EngineResult Run(IEnumerable<EngineUnit> units, SemanticsBundle bundle, EngineOptions options)
    {
        ArgumentNullException.ThrowIfNull(units);
        ArgumentNullException.ThrowIfNull(bundle);
        ArgumentNullException.ThrowIfNull(options);
        var inputs = units.ToList();
        var byKey = new Dictionary<string, EngineUnit>(StringComparer.Ordinal);
        foreach (var input in inputs)
        {
            if (!byKey.TryAdd(input.Unit.Key, input))
            {
                throw new ArgumentException($"The unit {input.Unit.Key} is given twice.", nameof(units));
            }
        }
        var run = new RunState(bundle, byKey, options);
        KernelThread.Run(run.Execute);
        return new EngineResult(
            bundle,
            run.Env,
            [.. inputs.Select(u => run.Outcomes[u.Unit.Key])],
            [.. run.Admitted]);
    }

    /// <summary>
    /// One theorem's budgets (R13): the project's, overridden by the theorem's <c>[Theorem(...)]</c> arguments where they
    /// are not zero, with one deadline for Meta and the kernel.
    /// </summary>
    private sealed class TheoremBudget
    {
        public TheoremBudget(EngineOptions options, VirBudget? overrides)
        {
            Timeout = overrides is { TimeoutSeconds: > 0 } ? TimeSpan.FromSeconds(overrides.TimeoutSeconds) : options.Timeout;
            var deadline = DateTimeOffset.UtcNow + Timeout;
            Kernel = options.Kernel with { Fuel = overrides is { KernelFuel: > 0 } ? overrides.KernelFuel : options.Kernel.Fuel, Deadline = deadline };
            Meta = new MetaLimits(overrides is { TacticFuel: > 0 } ? overrides.TacticFuel : options.TacticFuel) { Deadline = deadline };
        }

        public TimeSpan Timeout { get; }

        public KernelLimits Kernel { get; }

        public MetaLimits Meta { get; }

        /// <summary>Which budget a resource exception exhausted, for WRT0006's message.</summary>
        public string Exhausted(Exception ex)
        {
            if (ex.Message.Contains("deadline", StringComparison.Ordinal) || DateTimeOffset.UtcNow >= Kernel.Deadline)
            {
                return string.Create(CultureInfo.InvariantCulture, $"the time limit of {Timeout.TotalSeconds:0.###} s was reached");
            }
            return ex switch
            {
                MetaResourceException => string.Create(CultureInfo.InvariantCulture, $"tactic fuel ran out ({Meta.Fuel:N0} steps)"),
                KernelResourceException when ex.Message.StartsWith("kernel fuel", StringComparison.Ordinal) =>
                    string.Create(CultureInfo.InvariantCulture, $"kernel fuel ran out ({Kernel.Fuel:N0} steps)"),
                _ => $"the kernel ran out of resources: {ex.Message}",
            };
        }
    }

    private sealed class RunState(SemanticsBundle bundle, Dictionary<string, EngineUnit> units, EngineOptions options)
    {
        private readonly KernelLimits limits = options.Kernel;
        private NotationNames _names = new();

        public KernelEnvironment Env { get; } = bundle.Env.Fork();

        /// <summary>The attribute sidecar with this run's entries for the declarations it generates (KTD8, KTD9).</summary>
        public Sidecar Attributes { get; } = options.Attributes.Fork();

        public Dictionary<string, UnitOutcome> Outcomes { get; } = new(StringComparer.Ordinal);

        public List<KernelDeclaration> Admitted { get; } = [];

        public void Execute()
        {
            var translation = Translate();
            _names = Names(translation);
            foreach (var unit in translation.Units)
            {
                Outcomes.Add(unit.Key, Skip(units[unit.Key]) ?? Admit(unit));
            }
        }

        /// <summary>
        /// Translates every unit that translates: a unit translation rejects fails, the units depending on it are skipped, and
        /// translation runs again without them.
        /// </summary>
        private Translation Translate()
        {
            var remaining = units.Values.ToList();
            while (true)
            {
                try
                {
                    return Translator.Translate(
                        remaining.Select(u => u.Unit),
                        bundle.Env,
                        remaining.Where(u => u.DisplayName is not null).ToDictionary(u => u.Unit.Key, u => u.DisplayName!, StringComparer.Ordinal));
                }
                catch (TranslationException ex) when (ex.Key is { } key && units.TryGetValue(key, out var failed) && !Outcomes.ContainsKey(key))
                {
                    Outcomes.Add(key, new FailedOutcome(key, failed.Unit.Kind, Display(failed), Assumptions(failed), ex.Message));
                    bool changed = true;
                    while (changed)
                    {
                        changed = false;
                        foreach (var unit in remaining.Where(u => !Outcomes.ContainsKey(u.Unit.Key)))
                        {
                            if (Skip(unit) is { } skipped)
                            {
                                Outcomes.Add(unit.Unit.Key, skipped);
                                changed = true;
                            }
                        }
                    }
                    remaining = [.. remaining.Where(u => !Outcomes.ContainsKey(u.Unit.Key))];
                }
            }
        }

        /// <summary>
        /// How goals and messages name translated constants and record fields (KTD7): a unit by its C# short name
        /// (<c>Increment</c>), a member of a type under the type's short name (<c>PaymentResult.Valid</c>), a field by its C#
        /// name.
        /// </summary>
        private NotationNames Names(Translation translation)
        {
            var byName = translation.Units.ToDictionary(u => u.Name, u => u);
            var fields = translation.Units
                .Where(u => units[u.Key].Unit.Definition is RecordDefinition)
                .ToDictionary(u => u.Name, u => ((RecordDefinition)units[u.Key].Unit.Definition!).Fields.Select(f => f.Name).ToArray());
            return new NotationNames(
                name =>
                {
                    if (byName.TryGetValue(name, out var unit))
                    {
                        return OutcomeText.ShortName(unit.DisplayName);
                    }
                    if (!translation.DisplayNames.TryGetValue(name, out var display))
                    {
                        return null;
                    }
                    return name.Prefix is { } prefix && byName.TryGetValue(prefix, out var owner)
                        ? display.Replace(owner.DisplayName, OutcomeText.ShortName(owner.DisplayName), StringComparison.Ordinal)
                        : display;
                },
                (type, i) => fields.TryGetValue(type, out var names) && i < names.Length ? names[i] : null);
        }

        /// <summary>
        /// The skip outcome of a unit that depends on a unit that was not admitted (it failed or was skipped, or it is a
        /// theorem that was not proved); null if it has none.
        /// </summary>
        private SkippedOutcome? Skip(EngineUnit unit)
        {
            foreach (var dep in unit.Unit.Deps)
            {
                if (Outcomes.GetValueOrDefault(dep) is { } outcome and not (TranslatedOutcome or ProvedOutcome))
                {
                    return new SkippedOutcome(
                        unit.Unit.Key, unit.Unit.Kind, Display(unit), Assumptions(unit), dep, $"it depends on {Display(units[dep])}, which was not admitted.");
                }
            }
            return null;
        }

        private UnitOutcome Admit(TranslatedUnit translated)
        {
            var unit = units[translated.Key];
            var display = translated.DisplayName;
            var assumptions = Assumptions(unit);
            if (translated.Theorem is { } shell)
            {
                var budget = new TheoremBudget(options, shell.Budget);
                return shell.Script is null && shell.Statement.Instance is not null
                    ? Compute(unit, shell, display, assumptions, budget)
                    : RunScript(unit, shell, display, assumptions, budget);
            }
            var admitted = new List<KernelDeclaration>();
            foreach (var declaration in translated.Declarations)
            {
                try
                {
                    AddDeclaration(declaration, admitted);
                    if (declaration is InductiveDecl inductive)
                    {
                        // KTD8: casesOn and ctorIdx, which Lean's elaborator would have made, each built after the last is admitted.
                        foreach (var construction in Constructions.For(Env, inductive))
                        {
                            AddDeclaration(construction, admitted);
                            Constructions.Register(Attributes, construction.Value);
                        }
                    }
                }
                catch (KernelException ex)
                {
                    return new FailedOutcome(unit.Unit.Key, unit.Unit.Kind, display, assumptions, ex.Message);
                }
            }
            return new TranslatedOutcome(unit.Unit.Key, unit.Unit.Kind, display, assumptions, [.. admitted]);
        }

        private void AddDeclaration(KernelDeclaration declaration, List<KernelDeclaration> admitted)
        {
            Kernel.Kernel.Add(Env, declaration, limits);
            Admitted.Add(declaration);
            admitted.Add(declaration);
        }

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
                catch (KernelException)
                {
                    continue;
                }
                if (!ProofTerms.IsAdmittedAs(Env, shell))
                {
                    return new FailedOutcome(key, unit.Unit.Kind, display, assumptions, $"the kernel admitted {shell.Name} with a type other than its statement.");
                }
                Admitted.Add(declaration);
                return new ProvedOutcome(key, unit.Unit.Kind, display, assumptions, kind, declaration);
            }

            Expr decided;
            try
            {
                decided = new TypeChecker(Env, limits: budget.Kernel).Whnf(Operators.Decide(shell.Statement));
            }
            catch (KernelResourceException ex)
            {
                return new UndecidedOutcome(key, unit.Unit.Kind, display, assumptions, $"the kernel ran out of resources deciding the claim: {budget.Exhausted(ex)}.");
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
        private UnitOutcome RunScript(EngineUnit unit, TheoremShell shell, string display, ImmutableArray<UnitAssumption> assumptions, TheoremBudget budget)
        {
            var key = unit.Unit.Key;
            var kind = unit.Unit.Kind;
            var meta = new MetaM(Env, budget.Meta) { Attributes = Attributes, DisplayNames = _names };
            var printer = new GoalPrinter(Env, _names);
            var tactics = new TacticM(meta, []);
            var runner = new TacticRunner(tactics, unit);

            UnitOutcome NotProved(string message, IEnumerable<MVarId> goals, TacticNode? at) => new NotProvedOutcome(
                key, kind, display, assumptions, message, printer.PpGoals(meta.MCtx, goals), at is null ? null : runner.SpanOf(at),
                Counterexample.Search(Env, unit.Unit, shell, Definitions()));

            Expr proof;
            try
            {
                var goal = meta.MkFreshExprSyntheticOpaqueMVar(shell.Type);
                tactics.Goals = [goal.Id];
                var parameters = unit.Unit.Params ?? VirList<VirParam>.Empty;
                if (parameters.Count > 0)
                {
                    tactics.LiftMetaTactic1(g => meta.IntroN(g, parameters.Count, [.. parameters.Select(p => Name.From(p.Name))]).Goal);
                }
                foreach (var node in shell.Script ?? VirList<TacticNode>.Empty)
                {
                    runner.Run(node);
                }
                if (tactics.GetUnsolvedGoals() is { IsEmpty: false } unsolved)
                {
                    return NotProved("unsolved goals", unsolved, null);
                }
                proof = meta.InstantiateMVars(goal);
            }
            catch (TacticUnavailableException ex)
            {
                return NotProved(ex.Message, tactics.GetUnsolvedGoals(), runner.FailedAt);
            }
            catch (MetaResourceException ex)
            {
                return new UndecidedOutcome(key, kind, display, assumptions, $"{budget.Exhausted(ex)} while running the proof script.");
            }
            catch (KernelResourceException ex)
            {
                return new UndecidedOutcome(key, kind, display, assumptions, $"{budget.Exhausted(ex)} while running the proof script.");
            }
            catch (InsufficientExecutionStackException)
            {
                return new UndecidedOutcome(key, kind, display, assumptions, "the proof script ran out of stack.");
            }
            catch (MetaException ex) when (runner.FailedAt is { } failedAt)
            {
                var goals = ex is TacticException { Goal: { } g } && meta.MCtx.FindDecl(g) is not null ? [g] : tactics.GetUnsolvedGoals();
                return NotProved(ex.Message, goals, failedAt);
            }
#pragma warning disable CA1031 // KTD19: an unexpected failure in Meta ends this theorem as Warrant's bug, not the whole run.
            catch (Exception ex)
#pragma warning restore CA1031
            {
                return new InternalErrorOutcome(key, kind, display, assumptions, $"Meta failed unexpectedly: {ex.GetType().Name}: {ex.Message}");
            }

            if (options.TamperWithProof is { } tamper)
            {
                proof = tamper(proof);
            }
            if (proof.HasExprMVar || proof.HasLevelMVar || proof.HasFVar)
            {
                return new InternalErrorOutcome(key, kind, display, assumptions, "the proof script closed every goal, but the proof term still has a hole or a free variable.");
            }
            var declaration = shell.WithProof(proof);
            try
            {
                Kernel.Kernel.Add(Env, declaration, budget.Kernel);
            }
            catch (KernelResourceException ex)
            {
                return new UndecidedOutcome(key, kind, display, assumptions, $"{budget.Exhausted(ex)} while the kernel checked the proof.");
            }
            catch (KernelException ex)
            {
                return new InternalErrorOutcome(key, kind, display, assumptions, $"the kernel rejected the proof Warrant built: {ex.Message}");
            }
            if (!ProofTerms.IsAdmittedAs(Env, shell))
            {
                return new FailedOutcome(key, kind, display, assumptions, $"the kernel admitted {shell.Name} with a type other than its statement.");
            }
            Admitted.Add(declaration);
            return new ProvedOutcome(key, kind, display, assumptions, ProofKind.Script, declaration);
        }

        /// <summary>The definitions of the run's type units, by key.</summary>
        private Dictionary<string, VirDefinition> Definitions() =>
            units.Values.Where(u => u.Unit.Definition is not null).ToDictionary(u => u.Unit.Key, u => u.Unit.Definition!, StringComparer.Ordinal);

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
                VirSpan? span = null;
                unit.Spans?.TryGetSpan(id, out span);
                var value = term is null || operands is not { } o
                    ? new UnknownValue("the comparison's operands are not read back")
                    : ReadBack.Core(Env, term, o.Type, limits);
                return new ReadBackSide(id, span, value);
            }

            return [Side(compare.L, operands?.Left), Side(compare.R, operands?.Right)];
        }

        /// <summary>A unit's own assumptions; a theorem's also include those of every unit it depends on, transitively.</summary>
        private ImmutableArray<UnitAssumption> Assumptions(EngineUnit unit)
        {
            var result = unit.Unit.Assumptions.Select(a => new UnitAssumption(unit.Unit.Key, a)).ToList();
            if (unit.Unit.Kind != VirUnitKind.Theorem)
            {
                return [.. result];
            }
            var seen = new SortedSet<string>(StringComparer.Ordinal);
            var work = new Stack<string>(unit.Unit.Deps);
            while (work.Count > 0)
            {
                var key = work.Pop();
                if (string.Equals(key, unit.Unit.Key, StringComparison.Ordinal) || !seen.Add(key) || !units.TryGetValue(key, out var dep))
                {
                    continue;
                }
                foreach (var next in dep.Unit.Deps)
                {
                    work.Push(next);
                }
            }
            foreach (var key in seen)
            {
                if (units.TryGetValue(key, out var dep))
                {
                    result.AddRange(dep.Unit.Assumptions.Select(a => new UnitAssumption(key, a)));
                }
            }
            return [.. result];
        }

        private static string Display(EngineUnit unit) => unit.DisplayName ?? LeanNames.FallbackDisplay(unit.Unit.Key);
    }
}
