using System.Diagnostics;
using System.Text.Json;
using StreamJsonRpc;
using Warrant.Engine.Service;

namespace Warrant.Server.Tests;

/// <summary>
/// The server (M5b plan U8; KTD1 to KTD4, KTD12, KTD26; R1, R2, R6, R17), hosted in the test process on an endpoint of
/// its own and driven by a client built on StreamJsonRpc.
/// </summary>
[Collection(ServerGroup.Name)]
public sealed class ServerTests(ServiceFixture fixture)
{
    private static readonly TimeSpan Long = TimeSpan.FromSeconds(30);

    private VerificationService Service => fixture.Service;

    [Fact]
    public async Task TwoClientsVerifyDifferentProjectsConcurrentlyAndGetTheInProcessResults()
    {
        await using var server = HostedServer.Start(Service);
        await using var first = await TestClient.ConnectAsync(server.Endpoint);
        await using var second = await TestClient.ConnectAsync(server.Endpoint);
        Assert.Equal(VerificationService.ProtocolVersion, (await first.HelloAsync()).ProtocolVersion);
        Assert.Equal(Toolchain.Identity, (await second.HelloAsync()).ToolchainIdentity);
        var fast = Requests.For(Requests.Fast, "fast", project: "projects/fast");
        var refuted = Requests.For(Requests.Refuted, "refuted", project: "projects/refuted");

        var responses = await Task.WhenAll(first.VerifyAsync(fast), second.VerifyAsync(refuted));

        Assert.Equal("fast", responses[0].RequestId);
        Assert.Equal(OutcomeKind.Proved, responses[0].Outcome("M:S.Larger").Kind);
        Assert.Equal(OutcomeKind.Translated, responses[0].Outcome("M:S.Inc(System.Int32)").Kind);
        Assert.Equal("refuted", responses[1].RequestId);
        var grows = responses[1].Outcome("M:R.Grows(System.Int32)");
        Assert.Equal(OutcomeKind.NotProved, grows.Kind);
        Assert.Equal("2147483647", grows.Counterexample.Single().Value);
        // The same outcomes, field for field, as the service gives in-process (R3).
        Assert.Equal(Texts(Service.Verify(fast)), Texts(responses[0]));
        Assert.Equal(Texts(Service.Verify(refuted)), Texts(responses[1]));
    }

    [Fact]
    public async Task CancelByIdFromAnotherConnectionStopsARunningVerifyWithinASecond()
    {
        await using var server = HostedServer.Start(Service);
        await using var first = await TestClient.ConnectAsync(server.Endpoint);
        await using var second = await TestClient.ConnectAsync(server.Endpoint);
        var running = first.VerifyAsync(Requests.For(Requests.Slow(), "slow-cancel", Requests.Unbounded));
        await second.WaitForStatusAsync(s => s.ActiveRequests.Any(r => r.RequestId == "slow-cancel"), Long);
        await Task.Delay(TimeSpan.FromSeconds(1));
        Assert.False(running.IsCompleted);

        var stopwatch = Stopwatch.StartNew();
        Assert.True(await second.CancelAsync("slow-cancel"));
        var response = await running.WaitAsync(Long);
        var stoppedAfter = stopwatch.Elapsed;

        Assert.True(stoppedAfter < TimeSpan.FromSeconds(1), $"the verify stopped {stoppedAfter} after the cancel");
        Assert.Equal(OutcomeKind.Proved, response.Outcome("M:S.Early").Kind);
        Assert.Equal(OutcomeKind.Cancelled, response.Outcome("M:S.Slow").Kind);
        Assert.False(await second.CancelAsync("slow-cancel"));
        // The server keeps serving, and the next verify on the same connection succeeds.
        var next = await first.VerifyAsync(Requests.For(Requests.Fast, "after-cancel"));
        Assert.Equal(OutcomeKind.Proved, next.Outcome("M:S.Larger").Kind);
    }

    [Fact]
    public async Task CancellingTheVerifyCallSendsCancelRequestWhichStopsItsWorkWithinASecond()
    {
        await using var server = HostedServer.Start(Service);
        await using var watcher = await TestClient.ConnectAsync(server.Endpoint);
        await using var client = await TestClient.ConnectAsync(server.Endpoint);
        using var interrupt = new CancellationTokenSource();
        var running = client.VerifyAsync(Requests.For(Requests.Slow(), "slow-rpc-cancel", Requests.Unbounded), interrupt.Token);
        await watcher.WaitForStatusAsync(s => s.ActiveRequests.Any(r => r.RequestId == "slow-rpc-cancel"), Long);
        await Task.Delay(TimeSpan.FromSeconds(1));

        var stopwatch = Stopwatch.StartNew();
        await interrupt.CancelAsync();
        var response = await running.WaitAsync(Long);
        var stoppedAfter = stopwatch.Elapsed;

        Assert.True(stoppedAfter < TimeSpan.FromSeconds(1), $"the verify stopped {stoppedAfter} after $/cancelRequest");
        Assert.Equal(OutcomeKind.Proved, response.Outcome("M:S.Early").Kind);
        Assert.Equal(OutcomeKind.Cancelled, response.Outcome("M:S.Slow").Kind);
        Assert.Empty((await watcher.StatusAsync()).ActiveRequests);
    }

    [Fact]
    public async Task ClosingTheConnectionMidVerifyCancelsThatRequestsWork()
    {
        await using var server = HostedServer.Start(Service);
        await using var watcher = await TestClient.ConnectAsync(server.Endpoint);
        var client = await TestClient.ConnectAsync(server.Endpoint);
        _ = client.VerifyAsync(Requests.For(Requests.Slow(), "slow-disconnect", Requests.Unbounded));
        await watcher.WaitForStatusAsync(s => s.ActiveRequests.Any(r => r.RequestId == "slow-disconnect"), Long);
        await Task.Delay(TimeSpan.FromSeconds(1));

        var stopwatch = Stopwatch.StartNew();
        await client.DisposeAsync();
        await watcher.WaitForStatusAsync(s => s.ActiveRequests.IsEmpty, Long);

        Assert.True(stopwatch.Elapsed < TimeSpan.FromSeconds(1.5), $"the request's work stopped {stopwatch.Elapsed} after the client left");
        Assert.Contains("verified slow-disconnect", await File.ReadAllTextAsync(server.LogPath), StringComparison.Ordinal);
        Assert.Contains("(cancelled)", await File.ReadAllTextAsync(server.LogPath), StringComparison.Ordinal);
    }

    [Fact]
    public async Task AMismatchedHelloIsAnErrorAndTheServerExitsAfterItsRunningRequests()
    {
        await using var server = HostedServer.Start(Service);
        await using var first = await TestClient.ConnectAsync(server.Endpoint);
        await using var second = await TestClient.ConnectAsync(server.Endpoint);
        // Slow has a 3-second limit: the request runs about 3 s and then ends on its own, as undecided.
        var running = first.VerifyAsync(Requests.For(Requests.Slow(slowSeconds: 3), "running", Requests.Unbounded));
        await second.WaitForStatusAsync(s => s.ActiveRequests.Any(r => r.RequestId == "running"), Long);

        var error = await Assert.ThrowsAsync<RemoteInvocationException>(() => second.HelloAsync(VerificationService.ProtocolVersion + 1));
        Assert.Equal(ServerProtocol.ProtocolMismatchError, error.ErrorCode);
        Assert.True(server.Host.IsDraining);
        await Task.Delay(TimeSpan.FromSeconds(1));
        Assert.False(server.Run.IsCompleted, "the server stopped before its running request ended");

        var response = await running.WaitAsync(Long);
        Assert.Equal(OutcomeKind.Undecided, response.Outcome("M:S.Slow").Kind);
        Assert.Equal(OutcomeKind.Proved, response.Outcome("M:S.Then").Kind);
        await server.Run.WaitAsync(TimeSpan.FromSeconds(5));
    }

    [Fact]
    public async Task ASecondServerOnTheSameEndpointExitsAndTheFirstKeepsServing()
    {
        await using var server = HostedServer.Start(Service);

        var log = new ServerLog(server.LogPath);
        Assert.Null(ServerHost.TryAcquire(server.Endpoint, log, ServerHost.DefaultIdleTimeout));

        // The real executable, pointed at the same name: it exits at once with 0, before it loads anything.
        var start = new ProcessStartInfo("dotnet") { UseShellExecute = false, RedirectStandardError = true };
        start.ArgumentList.Add(Path.Combine(AppContext.BaseDirectory, "warrant-server.dll"));
        start.Environment[ServerEndpoint.EnvironmentVariable] = server.Endpoint.Name;
        using (var process = Process.Start(start)!)
        {
            var stderr = process.StandardError.ReadToEndAsync();
            Assert.True(process.WaitForExit(TimeSpan.FromSeconds(30)), "the second server did not exit");
            Assert.Equal(0, process.ExitCode);
            Assert.Equal("", await stderr);
        }

        await using var client = await TestClient.ConnectAsync(server.Endpoint);
        await client.HelloAsync();
        Assert.Equal(OutcomeKind.Proved, (await client.VerifyAsync(Requests.For(Requests.Fast, "still-serving"))).Outcome("M:S.Larger").Kind);
        Assert.False(server.Run.IsCompleted);
    }

    [Fact]
    public async Task WithATwoSecondIdleSettingTheServerExitsTwoSecondsAfterTheLastClientLeavesAndNotWhileARequestRuns()
    {
        await using var server = HostedServer.Start(Service, idle: TimeSpan.FromSeconds(2));
        var client = await TestClient.ConnectAsync(server.Endpoint);
        // About 3 s of work, longer than the idle period.
        var response = await client.VerifyAsync(Requests.For(Requests.Slow(slowSeconds: 3), "idle", Requests.Unbounded));
        Assert.Equal(OutcomeKind.Undecided, response.Outcome("M:S.Slow").Kind);
        Assert.False(server.Run.IsCompleted, "the server left while a request ran");

        var stopwatch = Stopwatch.StartNew();
        await client.DisposeAsync();
        await server.Run.WaitAsync(TimeSpan.FromSeconds(10));

        Assert.InRange(stopwatch.Elapsed, TimeSpan.FromSeconds(1.9), TimeSpan.FromSeconds(4));
        Assert.Contains("draining: idle for 2 s", await File.ReadAllTextAsync(server.LogPath), StringComparison.Ordinal);
    }

    [Fact]
    public async Task StatusReportsARunningRequestsIdAndTheCountersAfterItEnds()
    {
        await using var server = HostedServer.Start(Service);
        await using var client = await TestClient.ConnectAsync(server.Endpoint);
        await using var watcher = await TestClient.ConnectAsync(server.Endpoint);
        var before = await watcher.StatusAsync();
        Assert.Equal(Environment.ProcessId, before.ProcessId);
        Assert.Equal(server.Endpoint.Address, before.Endpoint);
        Assert.Equal(Toolchain.Identity, before.ToolchainIdentity);
        Assert.Equal(AttributeSidecarFixture.BundleSha256, before.BundleSha256);
        Assert.True(before.GcHeapBytes > 0);
        Assert.True(before.WorkingSetBytes > 0);
        Assert.True(before.Uptime > TimeSpan.Zero);
        Assert.Empty(before.ActiveRequests);

        var running = client.VerifyAsync(Requests.For(Requests.Slow(), "status-slow", Requests.Unbounded, project: "projects/slow"));
        var during = await watcher.WaitForStatusAsync(s => !s.ActiveRequests.IsEmpty, Long);
        var active = Assert.Single(during.ActiveRequests);
        Assert.Equal("status-slow", active.RequestId);
        Assert.Equal("projects/slow", active.ProjectDirectory);
        Assert.Equal(34, active.Units);
        Assert.True(await watcher.CancelAsync("status-slow"));
        var cancelled = await running.WaitAsync(Long);

        // The fast request twice through a cache: the second run's theorem comes from the cache and runs no tactic.
        var cache = Path.Combine(Path.GetTempPath(), $"warrant-server-cache-{Guid.NewGuid():N}");
        try
        {
            var cold = await client.VerifyAsync(Requests.For(Requests.Fast, "status-cold", cacheDirectory: cache));
            var warm = await client.VerifyAsync(Requests.For(Requests.Fast, "status-warm", cacheDirectory: cache));
            Assert.Equal(0, cold.Counters.Hits);
            Assert.Equal(1, cold.Counters.TacticRuns);
            Assert.True(warm.Outcome("M:S.Larger") is { Kind: OutcomeKind.Proved });
            Assert.True(warm.Units.Single(u => u.Outcome.Key == "M:S.Larger").FromCache);
            Assert.Equal(0, warm.Counters.TacticRuns);

            var after = await watcher.StatusAsync();
            Assert.Empty(after.ActiveRequests);
            var responses = new[] { cancelled, cold, warm };
            Assert.Equal(before.Counters.Hits + responses.Sum(r => r.Counters.Hits), after.Counters.Hits);
            Assert.Equal(before.Counters.Misses + responses.Sum(r => r.Counters.Misses), after.Counters.Misses);
            Assert.Equal(before.Counters.TacticRuns + responses.Sum(r => r.Counters.TacticRuns), after.Counters.TacticRuns);
            Assert.True(after.Counters.Hits > before.Counters.Hits);
        }
        finally
        {
            Directory.Delete(cache, recursive: true);
        }
    }

    [Fact]
    public async Task ShutdownLetsTheRunningRequestFinishThenStops()
    {
        await using var server = HostedServer.Start(Service);
        await using var first = await TestClient.ConnectAsync(server.Endpoint);
        await using var second = await TestClient.ConnectAsync(server.Endpoint);
        var running = first.VerifyAsync(Requests.For(Requests.Slow(slowSeconds: 2), "draining", Requests.Unbounded));
        await second.WaitForStatusAsync(s => !s.ActiveRequests.IsEmpty, Long);

        await second.ShutdownAsync();
        var refused = await Assert.ThrowsAsync<RemoteInvocationException>(() => second.VerifyAsync(Requests.For(Requests.Fast, "late")));
        Assert.Equal(ServerProtocol.ShuttingDownError, refused.ErrorCode);
        Assert.Equal(OutcomeKind.Undecided, (await running.WaitAsync(Long)).Outcome("M:S.Slow").Kind);
        await server.Run.WaitAsync(TimeSpan.FromSeconds(5));
    }

    private static List<string> Texts(VerifyResponse response) =>
        [.. response.Units.Select(u => JsonSerializer.Serialize(u.Outcome, ServiceJsonContext.Default.OutcomeDto))];
}
