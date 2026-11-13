using System.Diagnostics;
using System.Text.Json;
using System.Text.RegularExpressions;
using Warrant.Engine;
using Warrant.Engine.Service;
using Warrant.Engine.Service.Cache;
using Warrant.TestSupport;
using Warrant.Vir;

namespace Warrant.Cli.Tests;

/// <summary>
/// M5b's exit criterion (design §11's M5b row, the plan's Success Criteria; plan U17, docs/m5b/08), one test per item, so a
/// failure names the item. Every item runs <c>warrant verify</c> against a <c>warrant-server</c> process of its own, on a
/// unique endpoint (<see cref="TestServer"/>, which the CLI starts with <c>WARRANT_SERVER_ENDPOINT</c> set), and checks
/// once the server is shut down that its process is gone (KTD29). <c>dotnet test --filter M5bExit</c> runs them.
/// </summary>
/// <remarks>
/// Covered elsewhere, and not repeated here:
/// <list type="bullet">
/// <item>Analyzer output identical across 20 concurrent runs (R18): <c>Warrant.Analyzers.Tests.AnalyzerTests.TwentyConcurrentRunsGiveByteIdenticalDiagnosticsAndTheAnalyzerNeverThrows</c>,
/// in a project of its own because this one must not reference the analyzers.</item>
/// <item>The build samples through the server, a second build from the cache, a recheck build and <c>dotnet clean</c>:
/// <c>Warrant.Build.Tests.BuildIntegrationTests</c>, opt-in with <c>WARRANT_BUILD_INTEGRATION=1</c>.</item>
/// <item>Byte-identical output through the server and in-process (R3, KTD28): <see cref="ParityTests"/>.</item>
/// </list>
/// </remarks>
[Collection(ServerProcesses.Name)]
public sealed class M5bExitTests : IDisposable
{
    private static readonly string Corpus = Path.Combine(AppContext.BaseDirectory, "corpus", "m5a");

    private static readonly string[] Compilations = ["accepted", "refuted", "rejected"];

    private readonly string _caches = Path.Combine(Path.GetTempPath(), "warrant-m5b-exit-" + Guid.NewGuid().ToString("N")[..12]);

    public void Dispose()
    {
        if (Directory.Exists(_caches))
        {
            Directory.Delete(_caches, recursive: true);
        }
    }

    [Fact]
    public Task TheM5aExitCorpusVerifiesThroughTheServerWithM5aExpectedOutcomes() => WithServer(server =>
    {
        using var expectedFile = JsonDocument.Parse(File.ReadAllText(Path.Combine(Corpus, "expected.json")));
        var mismatches = new List<string>();
        int members = 0;
        foreach (var compilation in Compilations)
        {
            var directory = Path.Combine(Corpus, compilation);
            var (code, output) = server.Verify([directory, "--server", "auto"]);
            Assert.EndsWith(" [server]\n", output, StringComparison.Ordinal);
            Assert.DoesNotContain("verification server unavailable", output, StringComparison.Ordinal);
            Assert.Equal(compilation == "accepted" ? 0 : 1, code);
            // The server keeps the run's assumption report, with each unit's outcome under its documentation-comment ID.
            var (reportCode, reportText) = server.Command("report", directory);
            Assert.True(reportCode == 0, reportText);
            using var report = JsonDocument.Parse(reportText);
            var units = report.RootElement.GetProperty("units").EnumerateArray().ToDictionary(u => u.GetProperty("key").GetString()!, u => u.Clone());

            var expected = expectedFile.RootElement.GetProperty("members").GetProperty(compilation);
            var rejections = new Dictionary<string, int>();
            foreach (var member in expected.EnumerateObject())
            {
                members++;
                mismatches.AddRange(Compare(member.Name, member.Value, units.TryGetValue(member.Name, out var unit) ? unit : null, output));
                if (member.Value.TryGetProperty("diagnostics", out var diagnostics))
                {
                    foreach (var id in diagnostics.EnumerateArray().Select(d => d.GetProperty("id").GetString()!))
                    {
                        rejections[id] = rejections.GetValueOrDefault(id) + 1;
                    }
                }
            }
            mismatches.AddRange(units.Keys.Where(k => !expected.TryGetProperty(k, out _)).Select(k => $"{k}: not in expected.json"));
            foreach (var (id, count) in rejections)
            {
                int reported = Regex.Count(output, $@"(?m)^.+: error {id}: ");
                if (reported != count)
                {
                    mismatches.Add($"{compilation}: expected {count} {id} diagnostic(s), got {reported}");
                }
            }
        }
        Assert.True(mismatches.Count == 0, string.Join("\n", mismatches));
        Assert.Equal(33, members);
        return Task.CompletedTask;
    });

    [Fact]
    public Task ASecondVerifyComesFromTheCacheWithNoTacticRuns() => WithServer(async server =>
    {
        foreach (var compilation in Compilations)
        {
            var cache = CacheDirectory(compilation);
            string[] args = [Path.Combine(Corpus, compilation), "--server", "auto", "--cache-dir", cache, "--timings"];
            int start = await TacticRunsSoFar(server);
            var (coldCode, cold) = server.Verify(args);
            var before = (await server.StatusAsync()).Counters;

            var (warmCode, warm) = server.Verify(args);

            var after = (await server.StatusAsync()).Counters;
            Assert.Equal(before.TacticRuns, after.TacticRuns);
            Assert.Equal(coldCode, warmCode);
            Assert.Equal(Diagnostics(cold), Diagnostics(warm));
            // The cache holds an entry for every theorem, recursive method and method with an obligation (accepted: seven,
            // three, and Increment, whose Spec.Requires bounds its x + 1 since #244; refuted: one and one; rejected: none),
            // and each is reported from it.
            int entries = Directory.Exists(cache) ? Directory.GetFiles(cache, "*.json").Length : 0;
            Assert.Equal(compilation switch { "accepted" => 11, "refuted" => 2, _ => 0 }, entries);
            if (entries > 0)
            {
                Assert.True(before.TacticRuns > start, "the first verify ran no tactics, so the counter proves nothing");
            }
            var timings = Timings(warm);
            Assert.Equal(entries, timings.Count(t => t.Source == "cache"));
            Assert.Equal(entries, after.Hits - before.Hits);
            Assert.All(UnitLines(warm).Where(u => u.Outcome.StartsWith("proved", StringComparison.Ordinal) || u.Outcome == "unproved"),
                u => Assert.Equal("cache", timings.Single(t => t.Name == u.Name).Source));
            if (entries > 0)
            {
                Assert.Contains($"({entries} from cache)", Summary(warm), StringComparison.Ordinal);
            }
        }
    });

    [Fact]
    public Task ARecheckVerifyReportsEveryProvedUnitRecheckedWithNoTacticRuns() => WithServer(async server =>
    {
        var cache = CacheDirectory("accepted");
        string[] args = [Path.Combine(Corpus, "accepted"), "--server", "auto", "--cache-dir", cache, "--timings"];
        int start = await TacticRunsSoFar(server);
        var (_, cold) = server.Verify(args);
        var before = (await server.StatusAsync()).Counters;
        Assert.True(before.TacticRuns > start, "the first verify ran no tactics, so the counter proves nothing");

        var (code, recheck) = server.Verify([.. args, "--recheck"]);

        var after = (await server.StatusAsync()).Counters;
        Assert.Equal(0, code);
        Assert.Equal(before.TacticRuns, after.TacticRuns);
        Assert.Equal(Diagnostics(cold), Diagnostics(recheck));
        var timings = Timings(recheck);
        var proved = UnitLines(recheck).Where(u => u.Outcome.StartsWith("proved", StringComparison.Ordinal)).Select(u => u.Name).ToList();
        Assert.Equal(7, proved.Count);
        Assert.All(proved, name => Assert.Equal("rechecked", timings.Single(t => t.Name == name).Source));
        // The recursive methods' decrease proofs and Increment's contract (#244) come from the cache and are checked again too.
        int rechecked = timings.Count(t => t.Source == "rechecked");
        Assert.Equal(11, rechecked);
        Assert.Equal(rechecked, after.Rechecked - before.Rechecked);
        Assert.Contains($"{rechecked} rechecked", Summary(recheck), StringComparison.Ordinal);
    });

    [Fact]
    public Task ARecheckRejectsACachedProofSwappedForAnotherTheoremsWithWrt0010ForThatUnitOnly() => WithServer(async server =>
    {
        var cache = CacheDirectory("accepted");
        string[] args = [Path.Combine(Corpus, "accepted"), "--server", "auto", "--cache-dir", cache, "--timings"];
        Assert.Equal(0, server.Verify(args).Code);
        var proved = Directory.GetFiles(cache, "*.json")
            .Select(f => CacheEntry.FromFile(File.ReadAllBytes(f), Path.GetFileNameWithoutExtension(f), Toolchain.Identity))
            .Where(e => e.Outcome.UnitKind == VirUnitKind.Theorem && e.Outcome.Kind == OutcomeKind.Proved)
            .OrderBy(e => e.Outcome.Key, StringComparer.Ordinal)
            .ToList();
        var (tampered, donor) = (proved[0], proved[1]);
        Assert.NotEqual(tampered.Certificate, donor.Certificate);
        Assert.True(new FileResultCache().Write(cache, tampered with { Certificate = donor.Certificate }));
        var before = (await server.StatusAsync()).Counters;

        var (code, recheck) = server.Verify([.. args, "--recheck"]);

        Assert.Equal(1, code);
        Assert.Contains("timings (server): connected to the running server in ", recheck, StringComparison.Ordinal);
        var rejected = Assert.Single(Regex.Matches(recheck, @"(?m)^.+: error WRT0010: .*$"));
        Assert.Contains($"cached certificate for '{tampered.Outcome.DisplayName}' was rejected by the kernel: ", rejected.Value, StringComparison.Ordinal);
        Assert.Empty(Regex.Matches(recheck, @"(?m)^.+: error (?!WRT0010)"));
        var timings = Timings(recheck);
        Assert.All(
            UnitLines(recheck).Where(u => u.Outcome.StartsWith("proved", StringComparison.Ordinal)),
            u => Assert.Equal("rechecked", timings.Single(t => t.Name == u.Name).Source));
        Assert.Equal(6, UnitLines(recheck).Count(u => u.Outcome.StartsWith("proved", StringComparison.Ordinal)));
        Assert.Equal(before.TacticRuns, (await server.StatusAsync()).Counters.TacticRuns);
        Assert.False(File.Exists(FileResultCache.PathOf(cache, tampered.Key)), "the rejected entry was kept");
    });

    [Fact]
    public Task ServerCancelStopsALongDecideWithinASecondAndTheNextRequestSucceeds() => WithServer(async server =>
    {
        using var fast = new SourceDirectory(SourceDirectory.Fast);
        using var slow = new SourceDirectory(SourceDirectory.Slow());
        Assert.Equal(0, server.Verify([fast.Path, "--server", "auto"]).Code);
        // Deciding A30(0) > 0 needs far more than this fuel and time allow to finish: only the cancel ends it.
        using var abandon = new CancellationTokenSource();
        var run = Task.Run(() => server.Verify(
            [slow.Path, "--server", "auto", "--kernel-fuel", "100000000000", "--timeout", "120"], cancellationToken: abandon.Token));
        var running = await server.WaitForStatusAsync(s => s.ActiveRequests.Length == 1);
        await Task.Delay(1000);
        Assert.False(run.IsCompleted, "the request finished before it was cancelled");

        var cancelled = Stopwatch.StartNew();
        var (cancelCode, cancelOutput) = server.Command("cancel", running.ActiveRequests[0].RequestId);
        int code;
        string output;
        try
        {
            // A cancel that does not work fails here within seconds, rather than waiting for the request's own limit.
            (code, output) = await run.WaitAsync(TimeSpan.FromSeconds(10));
        }
        finally
        {
            await abandon.CancelAsync();
        }
        cancelled.Stop();

        Assert.Equal((0, $"Cancelled request {running.ActiveRequests[0].RequestId}.\n"), (cancelCode, cancelOutput));
        Assert.True(cancelled.Elapsed <= TimeSpan.FromSeconds(1), $"the request took {cancelled.Elapsed.TotalMilliseconds:0} ms to stop");
        Assert.Equal(1, code);
        Assert.Matches(@"(?m)^  S\.Slow\(\) +cancelled$", output);
        Assert.Matches(@"(?m)^  S\.Early\(\) +proved \(", output);
        Assert.DoesNotContain("verification server unavailable", output, StringComparison.Ordinal);

        var (nextCode, next) = server.Verify([fast.Path, "--server", "auto"]);
        Assert.True(nextCode == 0, next);
        Assert.EndsWith("Warrant: 2 verified units, 1 theorems proved, 0 not proved. [server]\n", next, StringComparison.Ordinal);
        var status = await server.StatusAsync();
        Assert.Equal(running.ProcessId, status.ProcessId);
        Assert.Empty(status.ActiveRequests);
    });

    [Fact]
    public Task ATheoremADefinitionAndADecreaseProofEachOverABudgetReportWrt0006() => WithServer(server =>
    {
        using var definition = new SourceDirectory("""
            public static class S
            {
                [Verified] public static int Inc(int x) => unchecked(x + 1);
            }
            """);
        using var recursive = new SourceDirectory("""
            public static class S
            {
                [Verified]
                public static int Sum(int n)
                {
                    Spec.Decreases(n);
                    if (n <= 0) return 0;
                    return unchecked(n + Sum(n - 1));
                }
            }
            """);
        using var theorem = new SourceDirectory(SourceDirectory.Slow());

        var (definitionCode, definitionOutput) = server.Verify([definition.Path, "--server", "auto", "--kernel-fuel", "1"]);
        var (recursiveCode, recursiveOutput) = server.Verify([recursive.Path, "--server", "auto", "--tactic-fuel", "1"]);
        var (theoremCode, theoremOutput) = server.Verify([theorem.Path, "--server", "auto", "--timeout", "1"]);

        Assert.Equal((1, 1, 1), (definitionCode, recursiveCode, theoremCode));
        Assert.Matches(@"(?m)error WRT0006: Member 'S\.Inc\(int\)' was not verified: kernel fuel ran out \(1 steps\) while the kernel checked the definition\.$", definitionOutput);
        Assert.Matches(
            @"(?m)error WRT0006: Member 'S\.Sum\(int\)' was not verified: tactic fuel ran out \(1 steps\) while proving the decrease of recursive call 1 of S\.Sum\(int\)\.$",
            recursiveOutput);
        Assert.Matches(@"(?m)error WRT0006: Theorem 'S\.Slow\(\)' was not decided: the time limit of 1 s was reached while ", theoremOutput);
        Assert.Single(Regex.Matches(theoremOutput, "error WRT0006"));
        foreach (var output in new[] { definitionOutput, recursiveOutput, theoremOutput })
        {
            Assert.EndsWith(" [server]\n", output, StringComparison.Ordinal);
        }
        return Task.CompletedTask;
    });

    /// <summary>The bundle-only store; the test is <see cref="StoreCommandTests"/>'s, run here so the filter selects it.</summary>
    [Fact]
    public void TheBundleStorePassesCheckStore()
    {
        using var tests = new StoreCommandTests();
        tests.ImportingTheBundleVerifiedThenCheckingTheStoreAcceptsEveryConstant();
    }

    /// <summary>Lean 4.35.0's Init and the bundle, verified, then <c>check-store</c> (R14): <see cref="StoreCommandTests"/>'s test.</summary>
    [FactRequiringEnv("WARRANT_INIT_EXPORT")]
    public void TheInitAndSemanticsStorePassesCheckStore()
    {
        using var tests = new StoreCommandTests();
        tests.AStoreOfInitAndTheBundlePassesCheckStore();
    }

    [Fact]
    public async Task NoServerProcessRemainsOnItsEndpointOnceTheServerIsShutDown()
    {
        int pid;
        var server = new TestServer();
        await using (server)
        {
            using var source = new SourceDirectory(SourceDirectory.Fast);
            Assert.Equal(0, server.Verify([source.Path, "--server", "auto"]).Code);
            pid = (await server.StatusAsync()).ProcessId;
            Assert.True(IsRunning(pid));
        }

        Assert.False(IsRunning(pid), $"the server (process {pid}) is still running");
        Assert.Null(await server.ConnectAsync());
    }

    /// <summary>
    /// Runs an item against a server of its own, then shuts the server down and checks that its process exited and that
    /// nothing answers on its endpoint.
    /// </summary>
    /// <summary>The server's tactic counter, or 0 before the first verify has started a server.</summary>
    private static async Task<int> TacticRunsSoFar(TestServer server)
    {
        try
        {
            return (await server.StatusAsync()).Counters.TacticRuns;
        }
        catch (InvalidOperationException)
        {
            return 0;
        }
    }

    private static async Task WithServer(Func<TestServer, Task> item)
    {
        var server = new TestServer();
        int? pid = null;
        await using (server)
        {
            await item(server);
            using var client = await server.ConnectAsync();
            pid = client?.Hello?.ProcessId;
        }
        if (pid is { } id)
        {
            Assert.False(IsRunning(id), $"the server (process {id}) is still running");
        }
        Assert.Null(await server.ConnectAsync());
    }

    /// <summary>
    /// Whether a process runs with that ID. The server runs in the <c>dotnet</c> host, so its process is known by the ID it
    /// reports, not by a name.
    /// </summary>
    private static bool IsRunning(int pid)
    {
        try
        {
            using var process = Process.GetProcessById(pid);
            return !process.HasExited;
        }
        catch (ArgumentException)
        {
            return false;
        }
    }

    private string CacheDirectory(string compilation) => Path.Combine(_caches, compilation, "obj", "warrant", "cache");

    /// <summary>The ways one member's outcome in the server's report differs from its expected.json entry.</summary>
    private static IEnumerable<string> Compare(string key, JsonElement expected, JsonElement? unit, string output)
    {
        var outcome = expected.GetProperty("outcome").GetString()!;
        if (outcome == "rejected")
        {
            if (unit is not null)
            {
                yield return $"{key}: expected rejected, the server verified it";
            }
            yield break;
        }
        if (unit is not { } u)
        {
            yield return $"{key}: expected {outcome}, not in the server's report";
            yield break;
        }
        var actual = u.GetProperty("outcome").GetString();
        if (actual != outcome)
        {
            yield return $"{key}: expected {outcome}, got {actual}";
            yield break;
        }
        if (expected.TryGetProperty("by", out var by) && u.GetProperty("by").GetString() != by.GetString())
        {
            yield return $"{key}: expected proved by {by.GetString()}, got {u.GetProperty("by")}";
        }
        if (expected.TryGetProperty("code", out var code) && u.GetProperty("detail").GetString()?.Contains($"({code.GetString()})", StringComparison.Ordinal) != true)
        {
            yield return $"{key}: expected {code.GetString()}, got '{u.GetProperty("detail")}'";
        }
        if (expected.TryGetProperty("goal", out var goal))
        {
            var block = string.Join("\n", goal.GetString()!.Split('\n').Select(l => "  " + l));
            if (!output.Contains(block + "\n", StringComparison.Ordinal))
            {
                yield return $"{key}: the goal\n{block}\nis not in the output";
            }
        }
        if (expected.TryGetProperty("counterexample", out var counterexample))
        {
            var values = string.Join(", ", counterexample.EnumerateObject().Select(p => $"{p.Name} = {p.Value.GetString()}"));
            if (!output.Contains($"Counterexample: {values}.", StringComparison.Ordinal))
            {
                yield return $"{key}: the counterexample {values} is not in the output";
            }
        }
    }

    /// <summary>The unit lines of a text run: each unit's display name and outcome.</summary>
    private static List<(string Name, string Outcome)> UnitLines(string output) =>
        [.. Regex.Matches(output, @"(?m)^  (\S.*?)  +(\S.*)$").Select(m => (m.Groups[1].Value, m.Groups[2].Value))];

    /// <summary>The <c>--timings</c> lines: each unit's display name and where its result came from.</summary>
    private static List<(string Name, string Source)> Timings(string output) =>
        [.. Regex.Matches(output, @"(?m)^ +\d+\.\d ms  (\S+) +(.+)$").Select(m => (m.Groups[2].Value, m.Groups[1].Value))];

    /// <summary>Every line before the summary, which alone says where results came from: the unit lines and the diagnostics.</summary>
    private static List<string> Diagnostics(string output) =>
        [.. output.Split('\n').TakeWhile(l => !l.StartsWith("Warrant: ", StringComparison.Ordinal))];

    private static string Summary(string output) => output.Split('\n').Single(l => l.StartsWith("Warrant: ", StringComparison.Ordinal));
}
