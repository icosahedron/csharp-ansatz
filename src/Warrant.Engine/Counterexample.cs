using System.Collections.Immutable;
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
/// runs outside the theorem's budgets, with <see cref="FuelPerCombination"/> kernel steps per combination, at most
/// <see cref="MaxCombinations"/> combinations and <see cref="TotalFuel"/> steps in all; a combination that runs out is skipped, so the search cannot turn WRT0001
/// into WRT0006. It reads no clock (M5b KTD32): what it finds depends only on the theorem, never on the machine's load,
/// so the server, the in-process path and the cache agree. Only a cancellation of the run stops it early.
/// </remarks>
internal static class Counterexample
{
    /// <summary>The kernel fuel for one combination.</summary>
    public const long FuelPerCombination = 1_000_000;

    /// <summary>
    /// The most combinations the search tries (M5b KTD32, replacing M5a KTD25's two seconds): every combination of up to
    /// three <c>int</c> parameters, 7^3 = 343, and the first 512 of more. Measured in M5b U5, a combination of the M5a
    /// corpus's claims costs 1 to 5 ms (<c>Clamp</c>'s about 1.3 ms, <c>RankIsSmall</c>'s about 5 ms), and 512 of a
    /// four-parameter claim over <c>Clamp</c> took 0.8 s, so the worst case stays near two seconds.
    /// </summary>
    public const int MaxCombinations = 512;

    /// <summary>
    /// The kernel fuel the whole search may spend (M5b KTD32): deterministic like <see cref="MaxCombinations"/>, and a
    /// bound on its time whatever the claim. U5 measured about 1M steps a second, so this keeps the worst case near the two
    /// seconds of M5a KTD25; without it, 512 combinations that each exhaust their fuel would take minutes.
    /// </summary>
    public const long TotalFuel = 2_000_000;

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
    /// <param name="cancellationToken">The run's token, which every combination's kernel limits carry.</param>
    /// <returns>The values in parameter order, or empty when none was found or the parameters cannot be enumerated.</returns>
    /// <exception cref="OperationCanceledException">The run was cancelled; the search does not count it as a failed combination.</exception>
    public static ImmutableArray<CounterexampleValue> Search(
        KernelEnvironment env, VirUnit unit, TheoremShell shell, IReadOnlyDictionary<string, VirDefinition> definitions, CancellationToken cancellationToken = default)
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

        var index = new int[candidates.Count];
        long remaining = TotalFuel;
        for (int tried = 0; tried < MaxCombinations && remaining > 0; tried++)
        {
            cancellationToken.ThrowIfCancellationRequested();
            var args = index.Select((v, i) => candidates[i][v].Term).ToArray();
            var decide = Operators.Decide(new Condition(Expr.App(claim.Prop, args), Expr.App(instance, args)));
            var limits = new KernelLimits(Math.Min(FuelPerCombination, remaining), KernelLimits.Interactive.MaxNatBytes) { CancellationToken = cancellationToken };
            var checker = new TypeChecker(env, limits: limits);
            try
            {
                if (checker.Whnf(decide) is ConstExpr { Name: var b } && b == BoolFalse)
                {
                    return [.. parameters.Select((p, i) => new CounterexampleValue(p.Name, candidates[i][index[i]].Text))];
                }
            }
            catch (KernelException) when (!cancellationToken.IsCancellationRequested)
            {
            }
            catch (KernelException ex)
            {
                throw new OperationCanceledException("The run was cancelled during the counterexample search.", ex, cancellationToken);
            }
            catch (InsufficientExecutionStackException)
            {
            }
            remaining -= checker.FuelUsed;
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
