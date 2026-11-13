using System.Diagnostics;
using System.Globalization;
using System.Text;
using Warrant.Engine.Reports;
using Warrant.Kernel;

namespace Warrant.Engine.Tests;

/// <summary>
/// Cancelling a run (M5b plan U3, KTD12, R6): no unit starts once the token is cancelled, the unit it interrupts ends as
/// <see cref="CancelledOutcome"/>, never as a verdict, and units that finished before keep their outcomes.
/// </summary>
public sealed class CancellationTests(EngineFixture engine) : IClassFixture<EngineFixture>
{
    private const string Fast = """
        public static class S
        {
            [Verified] public static int Inc(int x) => unchecked(x + 1);
            [Theorem] static Proof Larger() => Prove.That(Inc(41) > 41);
            [Theorem] static Proof Scripted(int a) => Prove.That(a == a).By(Tactic.Exact(Lean.Const("rfl")));
        }
        """;

    [Fact]
    public void ARunCancelledBeforeItStartsCancelsEveryUnit()
    {
        using var cts = new CancellationTokenSource();
        cts.Cancel();
        var result = Run(Fast, engine.Options with { CancellationToken = cts.Token });

        Assert.All(result.Units, u => Assert.IsType<CancelledOutcome>(u));
        Assert.Empty(result.Admitted);
        Assert.Equal("cancelled", AssumptionReports.OutcomeName(result.Units[0]));

        using var live = new CancellationTokenSource();
        var control = Run(Fast, engine.Options with { CancellationToken = live.Token });
        Assert.IsType<TranslatedOutcome>(control.Find("M:S.Inc(System.Int32)"));
        Assert.IsType<ProvedOutcome>(control.Find("M:S.Larger"));
        Assert.IsType<ProvedOutcome>(control.Find("M:S.Scripted(System.Int32)"));
    }

    [Fact]
    public void ARunCancelledMidwayKeepsTheFinishedUnitsAndCancelsTheRest()
    {
        // A{k}(x) = A{k-1}(A{k-1}(x)) adds 2^k to x, and deciding A30(0) > 0 takes the kernel far longer than the two
        // seconds before the cancel; with unlimited kernel fuel and time, only the token stops it. The engine runs Early
        // before Slow and Then after it (units in key order).
        var source = new StringBuilder("public static class S\n{\n    [Verified] public static int A0(int x) => unchecked(x + 1);\n");
        for (int k = 1; k <= 30; k++)
        {
            source.Append(CultureInfo.InvariantCulture, $"    [Verified] public static int A{k}(int x) => A{k - 1}(A{k - 1}(x));\n");
        }
        source.Append("""
                [Theorem] static Proof Early() => Prove.That(A1(0) == 2);
                [Theorem] static Proof Slow() => Prove.That(A30(0) > 0);
                [Theorem] static Proof Then() => Prove.That(A0(0) == 1);
            }
            """);
        var options = engine.Options with
        {
            Kernel = KernelLimits.Corpus with { Fuel = long.MaxValue },
            Timeout = TimeSpan.FromHours(1),
        };
        var inputs = EngineCorpus.Inputs(EngineCorpus.Inline(source.ToString()));

        using var cts = new CancellationTokenSource();
        var stopwatch = Stopwatch.StartNew();
        TimeSpan? cancelledAt = null;
        using var registration = cts.Token.Register(() => cancelledAt = stopwatch.Elapsed);
        cts.CancelAfter(TimeSpan.FromSeconds(2));
        var result = Pipeline.Run(inputs, engine.Bundle, options with { CancellationToken = cts.Token });
        var stoppedAt = stopwatch.Elapsed;

        Assert.NotNull(cancelledAt);
        Assert.True(stoppedAt - cancelledAt < TimeSpan.FromSeconds(1), $"the run stopped {stoppedAt - cancelledAt} after the cancel");
        Assert.IsType<TranslatedOutcome>(result.Find("M:S.A30(System.Int32)"));
        Assert.IsType<ProvedOutcome>(result.Find("M:S.Early"));
        Assert.IsType<CancelledOutcome>(result.Find("M:S.Slow"));
        Assert.IsType<CancelledOutcome>(result.Find("M:S.Then"));
    }

    private EngineResult Run(string source, EngineOptions options) =>
        Pipeline.Run(EngineCorpus.Inputs(EngineCorpus.Inline(source)), engine.Bundle, options);
}
