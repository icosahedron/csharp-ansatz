using System.Globalization;
using System.IO.Pipes;
using System.Net.Sockets;
using System.Text;
using System.Text.Json;
using StreamJsonRpc;
using Warrant.Engine;
using Warrant.Engine.Service;
using Warrant.Kernel;
using Warrant.Vir;

namespace Warrant.Server.Tests;

/// <summary>One verification service for every server test, over the test data's bundle and sidecar, with four workers.</summary>
public sealed class ServiceFixture : IDisposable
{
    public VerificationService Service { get; } =
        new(TestData.Path(SemanticsBundleFixture.FileName), TestData.Path(AttributeSidecarFixture.FileName), workers: 4);

    public void Dispose() => Service.Dispose();
}

/// <summary>The server tests share one service and run one at a time, because several of them time things.</summary>
[CollectionDefinition(Name)]
public sealed class ServerGroup : ICollectionFixture<ServiceFixture>
{
    public const string Name = "server";
}

/// <summary>A server hosted in the test process on an endpoint of its own (KTD29).</summary>
internal sealed class HostedServer : IAsyncDisposable
{
    private HostedServer(ServerHost host, Task run, string logPath)
    {
        Host = host;
        Run = run;
        LogPath = logPath;
    }

    public ServerHost Host { get; }

    /// <summary>Ends when the server has stopped.</summary>
    public Task Run { get; }

    public string LogPath { get; }

    public ServerEndpoint Endpoint => Host.Endpoint;

    public static HostedServer Start(VerificationService service, TimeSpan? idle = null, ServerEndpoint? endpoint = null)
    {
        var logPath = Path.Combine(Path.GetTempPath(), $"warrant-server-test-{Guid.NewGuid():N}.log");
        var host = ServerHost.TryAcquire(endpoint ?? UniqueEndpoint(), new ServerLog(logPath), idle ?? ServerHost.DefaultIdleTimeout)
            ?? throw new InvalidOperationException("the unique endpoint is held");
        return new HostedServer(host, host.RunAsync(service), logPath);
    }

    /// <summary>A fresh endpoint name, short enough for any socket path.</summary>
    public static ServerEndpoint UniqueEndpoint() => ServerEndpoint.Named("wt" + Guid.NewGuid().ToString("N")[..16]);

    public async ValueTask DisposeAsync()
    {
        Host.Drain("test ended");
        await Run.WaitAsync(TimeSpan.FromSeconds(30));
        Host.Dispose();
        File.Delete(LogPath);
    }
}

/// <summary>A protocol client built directly on StreamJsonRpc, independent of the server's own wiring.</summary>
internal sealed class TestClient : IAsyncDisposable
{
    private readonly JsonRpc _rpc;

    private TestClient(JsonRpc rpc) => _rpc = rpc;

    public Task Completion => _rpc.Completion;

    public static async Task<TestClient> ConnectAsync(ServerEndpoint endpoint)
    {
        Stream stream;
        if (endpoint.SocketDirectory is null)
        {
            var pipe = new NamedPipeClientStream(".", endpoint.Address, PipeDirection.InOut, PipeOptions.Asynchronous | PipeOptions.CurrentUserOnly);
            await pipe.ConnectAsync(5000);
            stream = pipe;
        }
        else
        {
            var socket = new Socket(AddressFamily.Unix, SocketType.Stream, ProtocolType.Unspecified);
            await socket.ConnectAsync(new UnixDomainSocketEndPoint(endpoint.Address));
            stream = new NetworkStream(socket, ownsSocket: true);
        }
        var formatter = new SystemTextJsonFormatter { JsonSerializerOptions = ServerProtocol.CreateSerializerOptions() };
        var rpc = new JsonRpc(new HeaderDelimitedMessageHandler(stream, stream, formatter));
        rpc.StartListening();
        return new TestClient(rpc);
    }

    public Task<HelloResponse> HelloAsync(int protocol = VerificationService.ProtocolVersion) =>
        _rpc.InvokeWithCancellationAsync<HelloResponse>("hello", [protocol], CancellationToken.None);

    public Task<VerifyResponse> VerifyAsync(VerifyRequest request, CancellationToken cancellationToken = default) =>
        _rpc.InvokeWithCancellationAsync<VerifyResponse>("verify", [request], cancellationToken);

    public Task<bool> CancelAsync(string id) => _rpc.InvokeWithCancellationAsync<bool>("cancel", [id], CancellationToken.None);

    public Task<ServerStatus> StatusAsync() => _rpc.InvokeWithCancellationAsync<ServerStatus>("status", [], CancellationToken.None);

    public Task ShutdownAsync() => _rpc.InvokeWithCancellationAsync("shutdown", [], CancellationToken.None);

    /// <summary>Polls <c>status</c> until a condition holds; fails after <paramref name="timeout"/>.</summary>
    public async Task<ServerStatus> WaitForStatusAsync(Func<ServerStatus, bool> condition, TimeSpan timeout)
    {
        var deadline = DateTime.UtcNow + timeout;
        while (true)
        {
            var status = await StatusAsync();
            if (condition(status))
            {
                return status;
            }
            Assert.True(DateTime.UtcNow < deadline, "the server's status never reached the expected state");
            await Task.Delay(20);
        }
    }

    public ValueTask DisposeAsync()
    {
        _rpc.Dispose();
        return ValueTask.CompletedTask;
    }
}

/// <summary>Requests compiled from inline C# (test-only: the server never sees Roslyn).</summary>
internal static class Requests
{
    /// <summary>The corpus budgets: the default budgets with the corpus kernel fuel.</summary>
    public static VerifyBudgets Corpus { get; } = VerifyBudgets.From(EngineOptions.Default with { Kernel = KernelLimits.Corpus });

    /// <summary>Unlimited kernel fuel and an hour's time: only a cancel stops a long kernel <c>decide</c>.</summary>
    public static VerifyBudgets Unbounded { get; } = Corpus with { KernelFuel = long.MaxValue, Timeout = TimeSpan.FromHours(1) };

    /// <summary>
    /// A{k}(x) = A{k-1}(A{k-1}(x)) adds 2^k to x; the kernel takes far longer than any test to decide <c>A30(0) &gt; 0</c>.
    /// Early is proved at once, Slow runs until stopped (or for <paramref name="slowSeconds"/> when given), and Then is
    /// proved at once.
    /// </summary>
    public static string Slow(int? slowSeconds = null)
    {
        var source = new StringBuilder("public static class S\n{\n    [Verified] public static int A0(int x) => x + 1;\n");
        for (int k = 1; k <= 30; k++)
        {
            source.Append(CultureInfo.InvariantCulture, $"    [Verified] public static int A{k}(int x) => A{k - 1}(A{k - 1}(x));\n");
        }
        var limit = slowSeconds is { } s ? string.Create(CultureInfo.InvariantCulture, $"(TimeoutSeconds = {s})") : "";
        source.Append(CultureInfo.InvariantCulture, $"""
                [Theorem] static Proof Early() => Prove.That(A1(0) == 2);
                [Theorem{limit}] static Proof Slow() => Prove.That(A30(0) > 0);
                [Theorem] static Proof Then() => Prove.That(A0(0) == 1);

            """);
        source.Append('}');
        return source.ToString();
    }

    public const string Fast = """
        public static class S
        {
            [Verified] public static int Inc(int x) => x + 1;
            [Theorem] static Proof Larger() => Prove.That(Inc(41) > 41);
        }
        """;

    public const string Refuted = """
        public static class R
        {
            [Verified] public static int Inc(int x) => x + 1;
            [Theorem] static Proof Grows(int x) => Prove.That(Inc(x) > x).By(Tactic.Unfold(nameof(Inc)), Tactic.Omega());
        }
        """;

    public static VerifyRequest For(string source, string requestId, VerifyBudgets? budgets = null, string project = "project", string? cacheDirectory = null)
    {
        var extraction = CorpusCompilations.Inline(source);
        return new VerifyRequest(
            VerificationService.ProtocolVersion,
            requestId,
            project,
            cacheDirectory,
            budgets ?? Corpus,
            Recheck: false,
            Priority: 0,
            [.. extraction.Units.Select(u => new RequestUnit(u.Unit.Key, u.Unit.Kind, u.DisplayName, VirWriter.Write(u.Unit)))]);
    }

    public static OutcomeDto Outcome(this VerifyResponse response, string key) => response.Units.Single(u => u.Outcome.Key == key).Outcome;
}
