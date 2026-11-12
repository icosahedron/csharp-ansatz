using Warrant.Kernel;

namespace Warrant.Engine.Tests;

/// <summary>
/// Budgets for every unit (M5b plan U2, KTD11, R5): a definition, a decrease proof or an equation lemma that runs out of
/// kernel fuel, tactic fuel or the time limit is undecided (WRT0006) naming the budget, never an internal error.
/// </summary>
public sealed class BudgetTests(EngineFixture engine) : IClassFixture<EngineFixture>
{
    private const string Inc = """
        public static class S
        {
            [Verified] public static int Inc(int x) => x + 1;
        }
        """;

    private const string Sum = """
        public static class S
        {
            [Verified]
            public static int Sum(int n)
            {
                Spec.Decreases(n);
                if (n <= 0) return 0;
                return n + Sum(n - 1);
            }
        }
        """;

    [Fact]
    public void ADefinitionThatNeedsMoreKernelFuelReportsKernelFuel()
    {
        var result = Run(Inc, engine.Options with { Kernel = KernelLimits.Corpus with { Fuel = 1 } });
        var outcome = Assert.IsType<UndecidedOutcome>(result.Find("M:S.Inc(System.Int32)"));
        Assert.Equal("WRT0006", UndecidedOutcome.Code);
        Assert.Equal("kernel fuel ran out (1 steps) while the kernel checked the definition.", outcome.Reason);
    }

    [Fact]
    public void ADecreaseProofOverATacticFuelOfOneReportsTacticFuel()
    {
        var result = Run(Sum, engine.Options with { TacticFuel = 1 });
        var outcome = Assert.IsType<UndecidedOutcome>(result.Find("M:S.Sum(System.Int32)"));
        Assert.Equal("tactic fuel ran out (1 steps) while proving the decrease of recursive call 1 of S.Sum(int).", outcome.Reason);
    }

    [Fact]
    public void ADefinitionCheckedPastItsDeadlineReportsTheTimeLimit()
    {
        var result = Run(Inc, engine.Options with { Timeout = TimeSpan.Zero });
        var outcome = Assert.IsType<UndecidedOutcome>(result.Find("M:S.Inc(System.Int32)"));
        Assert.Equal("the time limit of 0 s was reached while the kernel checked the definition.", outcome.Reason);
    }

    [Fact]
    public void ARecursiveDefinitionCheckedPastItsDeadlineReportsTheTimeLimit()
    {
        var result = Run(Sum, engine.Options with { Timeout = TimeSpan.Zero });
        var outcome = Assert.IsType<UndecidedOutcome>(result.Find("M:S.Sum(System.Int32)"));
        Assert.Equal("the time limit of 0 s was reached while proving the decrease of recursive call 1 of S.Sum(int).", outcome.Reason);
    }

    [Fact]
    public void ATheoremWhoseProofTheKernelChecksPastItsFuelReportsKernelFuel()
    {
        // The script closes the goal (omega's kernel calls fit in 1,000 steps); checking the whole proof term does not.
        var result = Run("""
            public static class S
            {
                [Verified] public static int Inc(int x) => x + 1;
                [Theorem(KernelFuel = 1000)] static Proof Starved(int x) => Prove.That(Inc(x) == unchecked(x + 1)).By(Tactic.Unfold(nameof(Inc)), Tactic.Omega());
                [Theorem] static Proof Fed(int x) => Prove.That(Inc(x) == unchecked(x + 1)).By(Tactic.Unfold(nameof(Inc)), Tactic.Omega());
            }
            """, engine.Options);
        var outcome = Assert.IsType<UndecidedOutcome>(result.Find("M:S.Starved(System.Int32)"));
        Assert.Equal("kernel fuel ran out (1,000 steps) while the kernel checked the proof.", outcome.Reason);
        Assert.IsType<ProvedOutcome>(result.Find("M:S.Fed(System.Int32)"));
    }

    private EngineResult Run(string source, EngineOptions options) =>
        Pipeline.Run(EngineCorpus.Inputs(EngineCorpus.Inline(source)), engine.Bundle, options);
}
