using System.Collections.Immutable;
using Warrant.Cic;
using Warrant.Kernel;
using Warrant.Semantics;
using Warrant.Vir;

namespace Warrant.Engine;

/// <summary>
/// The engine's pipeline (docs/m4/07, "The engine"): translates VIR units, admits their declarations in dependency order
/// into one fork of the bundle, proves theorems, and classifies every unit's outcome independently of the others.
/// </summary>
public static class Pipeline
{
    private static readonly Name BoolFalse = Name.Parse("Bool.false");
    private static readonly Name EqName = Name.Parse("Eq");
    private static readonly Name LtName = Name.Parse("LT.lt");
    private static readonly Name LeName = Name.Parse("LE.le");

    /// <summary>Runs the engine over a set of units.</summary>
    /// <param name="units">
    /// The units, typically in extraction order. A unit whose dependency is missing, cannot be translated or is rejected by
    /// the kernel fails, and the units depending on it are skipped; the others proceed.
    /// </param>
    /// <param name="bundle">The checked, frozen semantics bundle.</param>
    /// <param name="limits">The fuel for every kernel call; <see cref="KernelLimits.Corpus"/> when null.</param>
    /// <returns>One outcome per unit, in input order, and the environment the run admitted into.</returns>
    /// <exception cref="ArgumentException">Two units have the same key.</exception>
    public static EngineResult Run(IEnumerable<EngineUnit> units, SemanticsBundle bundle, KernelLimits? limits = null)
    {
        ArgumentNullException.ThrowIfNull(units);
        ArgumentNullException.ThrowIfNull(bundle);
        var inputs = units.ToList();
        var byKey = new Dictionary<string, EngineUnit>(StringComparer.Ordinal);
        foreach (var input in inputs)
        {
            if (!byKey.TryAdd(input.Unit.Key, input))
            {
                throw new ArgumentException($"The unit {input.Unit.Key} is given twice.", nameof(units));
            }
        }
        var run = new RunState(bundle, byKey, limits ?? KernelLimits.Corpus);
        KernelThread.Run(run.Execute);
        return new EngineResult(
            bundle,
            run.Env,
            [.. inputs.Select(u => run.Outcomes[u.Unit.Key])],
            [.. run.Admitted]);
    }

    private sealed class RunState(SemanticsBundle bundle, Dictionary<string, EngineUnit> units, KernelLimits limits)
    {
        public KernelEnvironment Env { get; } = bundle.Env.Fork();

        public Dictionary<string, UnitOutcome> Outcomes { get; } = new(StringComparer.Ordinal);

        public List<KernelDeclaration> Admitted { get; } = [];

        public void Execute()
        {
            foreach (var unit in Translate().Units)
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

        /// <summary>The skip outcome of a unit that depends on a unit that failed or was skipped; null if it has none.</summary>
        private SkippedOutcome? Skip(EngineUnit unit)
        {
            foreach (var dep in unit.Unit.Deps)
            {
                if (Outcomes.GetValueOrDefault(dep) is FailedOutcome or SkippedOutcome)
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
                return Prove(unit, shell, display, assumptions);
            }
            foreach (var declaration in translated.Declarations)
            {
                try
                {
                    Kernel.Kernel.Add(Env, declaration, limits);
                }
                catch (KernelException ex)
                {
                    return new FailedOutcome(unit.Unit.Key, unit.Unit.Kind, display, assumptions, ex.Message);
                }
                Admitted.Add(declaration);
            }
            return new TranslatedOutcome(unit.Unit.Key, unit.Unit.Kind, display, assumptions, translated.Declarations);
        }

        /// <summary>Tries <c>rfl</c>, then <c>decide</c>; if neither is admitted, reduces <c>decide P D</c> to tell false from undecided (KTD12).</summary>
        private UnitOutcome Prove(EngineUnit unit, TheoremShell shell, string display, ImmutableArray<UnitAssumption> assumptions)
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
                    Kernel.Kernel.Add(Env, declaration, limits);
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

            if (shell.Statement.Instance is null)
            {
                return new UndecidedOutcome(key, unit.Unit.Kind, display, assumptions, "the claim is quantified, so it cannot be decided, and proof scripts are not run yet.");
            }
            Expr decided;
            try
            {
                decided = new TypeChecker(Env, limits: limits).Whnf(Operators.Decide(shell.Statement));
            }
            catch (KernelResourceException ex)
            {
                return new UndecidedOutcome(key, unit.Unit.Kind, display, assumptions, $"the kernel ran out of resources deciding the claim: {ex.Message}");
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
