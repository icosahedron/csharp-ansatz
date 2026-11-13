using Warrant.Engine.Service;

namespace Warrant.Engine.Tests;

/// <summary>
/// The tactic trace behind <c>warrant explain</c> (M5b U16, KTD24): each step of a proof script with the goals before and
/// after it or why it failed, nested steps under the step that ran them, and no use of the result cache.
/// </summary>
public sealed class TraceTests(EngineFixture engine) : IClassFixture<EngineFixture>, IDisposable
{
    private const string Source = """
        public static class S
        {
            [Verified] public static int Inc(int x) => unchecked(x + 1);

            [Verified] public static bool Flip(bool b) => !b;

            [Theorem]
            static Proof IncBelowMax(int x) =>
                Prove.That(Spec.Implies(x < int.MaxValue, Inc(x) > x))
                     .By(Tactic.Unfold(nameof(Inc)), Tactic.Simp(), Tactic.Omega());

            [Theorem]
            static Proof AlwaysLarger(int x) =>
                Prove.That(Inc(x) > x).By(Tactic.Unfold(nameof(Inc)), Tactic.Omega());

            [Theorem]
            static Proof FlipTwice(bool b) =>
                Prove.That(Flip(Flip(b)) == b)
                     .By(Tactic.Unfold(nameof(Flip)), Tactic.Cases("b"), Tactic.AllGoals(Tactic.Try(Tactic.Exact("h"))), Tactic.AllGoals(Tactic.Simp()));
        }
        """;

    private static readonly BundleHashes Hashes =
        new(AttributeSidecarFixture.BundleSha256, Reports.OutcomeText.FileSha256(TestData.Path(AttributeSidecarFixture.FileName)));

    private readonly string _cache = Path.Combine(Path.GetTempPath(), "warrant-trace-" + Guid.NewGuid().ToString("N")[..12]);

    private readonly List<VerificationService> _services = [];

    public void Dispose()
    {
        foreach (var service in _services)
        {
            service.Dispose();
        }
        if (Directory.Exists(_cache))
        {
            Directory.Delete(_cache, recursive: true);
        }
    }

    private ExplainResponse Explain(string unitKey)
    {
        var service = new VerificationService(engine.Bundle, EngineFixture.SharedSidecar.Value, workers: 2, Hashes);
        _services.Add(service);
        var units = EngineCorpus.Inputs(EngineCorpus.Inline(Source));
        // A cache directory on the request: explain must ignore it.
        var request = ServiceTests.Request(units, engine.Options) with { CacheDirectory = _cache };
        return service.Explain(new ExplainRequest(request, unitKey));
    }

    [Fact]
    public void AProvedScriptRecordsEachTacticWithTheGoalsBeforeAndAfterIt()
    {
        var response = Explain("M:S.IncBelowMax(System.Int32)");

        Assert.Equal(["unfold", "simp", "omega"], response.Steps.Select(s => s.Tactic));
        Assert.All(response.Steps, s => Assert.Equal(0, s.Depth));
        Assert.All(response.Steps, s => Assert.Null(s.Failure));
        Assert.All(response.Steps, s => Assert.NotNull(s.Node));
        Assert.Contains("⊢ x < 2147483647 → Inc x > x", response.Steps[0].Before, StringComparison.Ordinal);
        Assert.DoesNotContain("Inc x", response.Steps[0].After, StringComparison.Ordinal);
        Assert.Equal(response.Steps[0].After, response.Steps[1].Before);
        // omega closed the last goal.
        Assert.Equal("", response.Steps[2].After);
        Assert.Equal(OutcomeKind.Proved, response.Response.Units.Single(u => u.Outcome.Key == "M:S.IncBelowMax(System.Int32)").Outcome.Kind);
    }

    [Fact]
    public void AFailedTacticRecordsWhyAndTheStepsAfterItDoNotRun()
    {
        var response = Explain("M:S.AlwaysLarger(System.Int32)");

        Assert.Equal(["unfold", "omega"], response.Steps.Select(s => s.Tactic));
        Assert.Contains("⊢ x + 1 > x", response.Steps[1].Before, StringComparison.Ordinal);
        Assert.Null(response.Steps[1].After);
        Assert.StartsWith("omega could not prove the goal", response.Steps[1].Failure, StringComparison.Ordinal);
        var outcome = response.Response.Units.Single(u => u.Outcome.Key == "M:S.AlwaysLarger(System.Int32)").Outcome;
        Assert.Equal(OutcomeKind.NotProved, outcome.Kind);
        Assert.Equal(outcome.Node, response.Steps[1].Node);
    }

    [Fact]
    public void StepsInsideAllGoalsAndTryAreNestedUnderThemAndAFailureInsideTryIsRecordedAndRecoveredFrom()
    {
        var response = Explain("M:S.FlipTwice(System.Boolean)");
        var steps = response.Steps.Select(s => (s.Depth, s.Tactic)).ToList();

        // all_goals runs try on each of the two cases, and try runs exact "h", which fails both times: there is no h.
        Assert.Equal(
            [
                (0, "unfold"), (0, "cases"),
                (0, "all_goals"), (1, "try"), (2, "exact"), (1, "try"), (2, "exact"),
                (0, "all_goals"), (1, "simp"), (1, "simp"),
            ],
            steps);
        Assert.All(response.Steps.Where(s => s.Tactic == "exact"), s => Assert.NotNull(s.Failure));
        // The case split shows as two goals after cases, and each try starts on one of them.
        Assert.Contains("case false", response.Steps[1].After, StringComparison.Ordinal);
        Assert.Contains("case true", response.Steps[1].After, StringComparison.Ordinal);
        Assert.StartsWith("case false", response.Steps[3].Before, StringComparison.Ordinal);
        Assert.StartsWith("case true", response.Steps[5].Before, StringComparison.Ordinal);
        Assert.All(response.Steps.Where(s => s.Tactic == "try"), s => Assert.Null(s.Failure));
        Assert.Equal("", response.Steps[^1].After);
        Assert.Equal(OutcomeKind.Proved, response.Response.Units.Single(u => u.Outcome.Key == "M:S.FlipTwice(System.Boolean)").Outcome.Kind);
    }

    [Fact]
    public void ExplainNeverReadsOrWritesTheCacheAndOnlyTheNamedUnitIsTraced()
    {
        var response = Explain("M:S.Inc(System.Int32)");

        Assert.Empty(response.Steps);
        Assert.All(response.Response.Units, u => Assert.False(u.FromCache));
        Assert.False(Directory.Exists(_cache) && Directory.EnumerateFileSystemEntries(_cache).Any(), "explain wrote to the cache");
    }

    [Fact]
    public void ARequestWithoutTheUnitIsRefused()
    {
        Assert.Throws<ArgumentException>(() => Explain("M:S.Nothing"));
    }
}
