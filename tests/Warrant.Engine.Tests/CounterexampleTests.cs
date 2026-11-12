using System.Globalization;
using System.Text;

namespace Warrant.Engine.Tests;

/// <summary>
/// The counterexample search's deterministic bounds (M5b KTD32): it tries at most <see cref="Counterexample.MaxCombinations"/>
/// combinations and spends at most <see cref="Counterexample.TotalFuel"/> kernel steps in all, whatever the claim.
/// </summary>
public sealed class CounterexampleTests(EngineFixture engine) : IClassFixture<EngineFixture>
{
    [Fact]
    public void TheSearchStopsAfterMaxCombinations()
    {
        // Four int parameters have 7^4 = 2401 combinations; the last varies fastest. Combination 511, the last one tried, is
        // a = 1, b = c = int.MaxValue, d = 0; combination 512 differs only in d = 1. Each claim is true everywhere else.
        Assert.Equal(512, Counterexample.MaxCombinations);
        Assert.Equal(
            "a = 1, b = 2147483647, c = 2147483647, d = 0",
            Search("a != 1 || b != int.MaxValue || c != int.MaxValue || d != 0"));
        Assert.Equal("", Search("a != 1 || b != int.MaxValue || c != int.MaxValue || d != 1"));
    }

    [Fact]
    public void TheSearchStopsWhenItHasSpentTotalFuel()
    {
        // Every combination but the one the claim is false at runs A20, which exhausts FuelPerCombination; after two of
        // them TotalFuel is spent. The values are tried in the order 0, 1, -1, int.MaxValue, int.MinValue, ...
        Assert.Equal(2, Counterexample.TotalFuel / Counterexample.FuelPerCombination);
        Assert.Equal("a = 1", Search("a != 1 && A20(a) > unchecked(a - 1)", Chain(20)));
        Assert.Equal("", Search("a != int.MinValue && A20(a) > unchecked(a - 1)", Chain(20)));
    }

    /// <summary>The counterexample of a theorem with no script over <paramref name="claim"/>, as <c>p = v, ...</c>.</summary>
    private string Search(string claim, string? members = null)
    {
        var parameters = string.Join(", ", new[] { "a", "b", "c", "d" }.Where(p => claim.Contains(p + " ", StringComparison.Ordinal)).Select(p => "int " + p));
        var source = $$"""
            public static class S
            {
            {{members}}
                [Theorem] static Proof T({{parameters}}) => Prove.That({{claim}});
            }
            """;
        var result = Pipeline.Run(EngineCorpus.Inputs(EngineCorpus.Inline(source)), engine.Bundle, engine.Options);
        var outcome = Assert.IsType<NotProvedOutcome>(Assert.Single(result.Units, u => u.Key.StartsWith("M:S.T(", StringComparison.Ordinal)));
        return string.Join(", ", outcome.Counterexample.Select(v => $"{v.Parameter} = {v.Value}"));
    }

    /// <summary><c>A0(x) = x + 1</c> and <c>A{k}(x) = A{k-1}(A{k-1}(x))</c>, which adds 2^k.</summary>
    private static string Chain(int depth)
    {
        var source = new StringBuilder("    [Verified] public static int A0(int x) => x + 1;\n");
        for (int k = 1; k <= depth; k++)
        {
            source.Append(CultureInfo.InvariantCulture, $"    [Verified] public static int A{k}(int x) => A{k - 1}(A{k - 1}(x));\n");
        }
        return source.ToString();
    }
}
