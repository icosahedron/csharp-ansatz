using System.Collections.Immutable;
using System.Diagnostics;
using System.Globalization;
using Warrant.Cic;
using Warrant.Kernel;
using Warrant.Semantics;
using Warrant.Vir;

namespace Warrant.Engine;

/// <summary>
/// The counterexample search a failed theorem gets (M5a KTD25, R4): for a theorem whose parameters are <c>int</c>,
/// <c>long</c>, <c>bool</c> or enums and whose claim is decidable, it evaluates <c>decide</c> of the claim in the kernel at
/// combinations of boundary values and returns the first that computes to <c>false</c>.
/// </summary>
/// <remarks>
/// The search is untrusted and diagnostic only: a value it finds upgrades the message of WRT0001, never its meaning. It
/// runs outside the theorem's budgets, with <see cref="FuelPerCombination"/> kernel steps per combination and
/// <see cref="TimeLimit"/> overall; a combination that runs out is skipped, so the search cannot turn WRT0001 into WRT0006.
/// </remarks>
internal static class Counterexample
{
    /// <summary>The kernel fuel for one combination.</summary>
    public const long FuelPerCombination = 1_000_000;

    /// <summary>The time the whole search may take.</summary>
    public static readonly TimeSpan TimeLimit = TimeSpan.FromSeconds(2);

    private static readonly Name BoolFalse = Name.Parse("Bool.false");

    /// <summary>The <c>int</c> values tried, simplest first: the differential tests' boundaries (KTD26).</summary>
    private static readonly int[] Int32Values = [0, 1, -1, int.MaxValue, int.MinValue, int.MaxValue - 1, int.MinValue + 1];

    /// <summary>The <c>long</c> values tried, as <see cref="Int32Values"/>.</summary>
    private static readonly long[] Int64Values = [0, 1, -1, long.MaxValue, long.MinValue, long.MaxValue - 1, long.MinValue + 1];

    /// <summary>Searches for parameter values that falsify the theorem's claim.</summary>
    /// <param name="env">The run's environment, holding every definition the claim uses.</param>
    /// <param name="unit">The theorem.</param>
    /// <param name="shell">Its statement.</param>
    /// <param name="definitions">The definitions of the run's type units, by key, for enum members.</param>
    /// <returns>The values in parameter order, or empty when none was found or the parameters cannot be enumerated.</returns>
    public static ImmutableArray<CounterexampleValue> Search(
        KernelEnvironment env, VirUnit unit, TheoremShell shell, IReadOnlyDictionary<string, VirDefinition> definitions)
    {
        var parameters = unit.Params ?? VirList<VirParam>.Empty;
        if (shell.Claim is not { Instance: { } instance } claim || parameters.Count == 0)
        {
            return [];
        }
        var candidates = new List<(Expr Term, string Text)[]>();
        foreach (var p in parameters)
        {
            if (Candidates(p.Type, definitions) is not { } values)
            {
                return [];
            }
            candidates.Add(values);
        }

        var stopwatch = Stopwatch.StartNew();
        var limits = new KernelLimits(FuelPerCombination, KernelLimits.Interactive.MaxNatBytes) { Deadline = DateTimeOffset.UtcNow + TimeLimit };
        var index = new int[candidates.Count];
        while (stopwatch.Elapsed < TimeLimit)
        {
            var args = index.Select((v, i) => candidates[i][v].Term).ToArray();
            var decide = Operators.Decide(new Condition(Expr.App(claim.Prop, args), Expr.App(instance, args)));
            try
            {
                if (new TypeChecker(env, limits: limits).Whnf(decide) is ConstExpr { Name: var b } && b == BoolFalse)
                {
                    return [.. parameters.Select((p, i) => new CounterexampleValue(p.Name, candidates[i][index[i]].Text))];
                }
            }
            catch (KernelException)
            {
                // Out of fuel or stuck: skip this combination.
            }
            catch (InsufficientExecutionStackException)
            {
                // Too deep: skip this combination.
            }
            int k = index.Length - 1;
            while (k >= 0 && ++index[k] == candidates[k].Length)
            {
                index[k--] = 0;
            }
            if (k < 0)
            {
                break;
            }
        }
        return [];
    }

    /// <summary>The values tried for a parameter of type <paramref name="type"/>, or null when it is not enumerable.</summary>
    private static (Expr Term, string Text)[]? Candidates(VirType type, IReadOnlyDictionary<string, VirDefinition> definitions) => type switch
    {
        PrimitiveType { Kind: VirPrimitive.Int32 } =>
            [.. Int32Values.Select(v => (Literals.Int32(v), v.ToString(CultureInfo.InvariantCulture)))],
        PrimitiveType { Kind: VirPrimitive.Int64 } =>
            [.. Int64Values.Select(v => (Literals.Int64(v), v.ToString(CultureInfo.InvariantCulture)))],
        PrimitiveType { Kind: VirPrimitive.Bool } =>
            [(Literals.Bool(false), "false"), (Literals.Bool(true), "true")],
        RefType { Key: var key } when definitions.GetValueOrDefault(key) is EnumDefinition e =>
            [.. e.Members.Select(m => Member(key, m.Name))],
        RefType { Key: var key } when definitions.GetValueOrDefault(key) is ClosedDefinition c =>
            [.. c.Members.Select(m => Member(key, m.Name))],
        _ => null,
    };

    private static (Expr, string) Member(string typeKey, string member) =>
        (Expr.Const(LeanNames.Member(typeKey, member)), $"{typeKey[(typeKey.LastIndexOfAny(['.', ':']) + 1)..]}.{member}");
}
