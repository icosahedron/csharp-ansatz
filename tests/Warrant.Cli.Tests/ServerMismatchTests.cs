using System.Collections.Immutable;
using System.Diagnostics;
using System.IO.Pipes;
using System.Net.Sockets;
using StreamJsonRpc;
using Warrant.Engine;
using Warrant.Engine.Service;
using Warrant.Vir;

namespace Warrant.Cli.Tests;

/// <summary>
/// A server that speaks the protocol but answers as a test tells it to: another toolchain identity in <c>hello</c>,
/// another bundle or sidecar hash in <c>status</c>, or a <c>verify</c> answer whose units do not match the request. It
/// listens on an endpoint of its own name, as the real server would, and holds no semantics bundle. A wedged stub stops
/// answering anything once it is asked to verify.
/// </summary>
internal sealed class StubServer : IAsyncDisposable
{
    private readonly CancellationTokenSource _stop = new();
    private readonly Task _accepting;
    private readonly Socket? _socket;

    public StubServer(Answers answers)
    {
        Endpoint = ServerEndpoint.Named("ws" + Guid.NewGuid().ToString("N")[..16]);
        if (Endpoint.SocketDirectory is { } directory)
        {
            Assert.True(ServerEndpoint.TryPrepareDirectory(directory, out var problem), problem);
            _socket = new Socket(AddressFamily.Unix, SocketType.Stream, ProtocolType.Unspecified);
            _socket.Bind(new UnixDomainSocketEndPoint(Endpoint.Address));
            _socket.Listen(8);
        }
        _accepting = AcceptAsync(new Target(answers, Calls));
    }

    public ServerEndpoint Endpoint { get; }

    /// <summary>The methods each connection has called, in order.</summary>
    public List<string> Calls { get; } = [];

    /// <summary>What the stub says, beside the real answers of a matching server.</summary>
    internal sealed record Answers
    {
        public string ToolchainIdentity { get; init; } = Toolchain.Identity;

        public string? BundleSha256 { get; init; } = TestServer.Hashes.Bundle;

        public string? SidecarSha256 { get; init; } = TestServer.Hashes.Sidecar;

        /// <summary>The units a verify answer carries, from the request's.</summary>
        public Func<ImmutableArray<RequestUnit>, IEnumerable<RequestUnit>> Units { get; init; } = units => units;

        /// <summary>Whether <c>verify</c> and every <c>status</c> after it hang until the client goes away.</summary>
        public bool Wedged { get; init; }
    }

    public async ValueTask DisposeAsync()
    {
        await _stop.CancelAsync();
        _socket?.Dispose();
        try
        {
            await _accepting;
        }
        catch (OperationCanceledException)
        {
        }
        _stop.Dispose();
        if (_socket is not null)
        {
            File.Delete(Endpoint.Address);
        }
    }

    private async Task AcceptAsync(Target target)
    {
        var connections = new List<Task>();
        try
        {
            while (!_stop.IsCancellationRequested)
            {
                Stream stream;
                if (_socket is null)
                {
                    var pipe = new NamedPipeServerStream(
                        Endpoint.Address, PipeDirection.InOut, NamedPipeServerStream.MaxAllowedServerInstances, PipeTransmissionMode.Byte,
                        PipeOptions.Asynchronous | PipeOptions.CurrentUserOnly);
                    try
                    {
                        await pipe.WaitForConnectionAsync(_stop.Token);
                    }
                    catch
                    {
                        await pipe.DisposeAsync();
                        throw;
                    }
                    stream = pipe;
                }
                else
                {
                    stream = new NetworkStream(await _socket.AcceptAsync(_stop.Token), ownsSocket: true);
                }
                connections.Add(ServeAsync(stream, target));
            }
        }
        catch (Exception ex) when (ex is OperationCanceledException or ObjectDisposedException or SocketException && _stop.IsCancellationRequested)
        {
        }
        await Task.WhenAll(connections);
    }

    private async Task ServeAsync(Stream stream, Target target)
    {
        var formatter = new SystemTextJsonFormatter { JsonSerializerOptions = ServerProtocol.CreateSerializerOptions() };
        using var rpc = new JsonRpc(new HeaderDelimitedMessageHandler(stream, stream, formatter));
        rpc.AddLocalRpcTarget(target);
        rpc.StartListening();
        using (_stop.Token.Register(rpc.Dispose))
        {
            try
            {
                await rpc.Completion;
            }
            catch (Exception)
            {
                // The client hung up or the stub stopped.
            }
        }
        await stream.DisposeAsync();
    }

    /// <summary>The protocol's methods; a class, not a record, so it has no public members but these.</summary>
    private sealed class Target(Answers answers, List<string> calls)
    {
        private volatile bool _wedged;
        [JsonRpcMethod(ServerProtocol.Hello)]
        public HelloResponse Hello(int protocol)
        {
            Record(ServerProtocol.Hello);
            // A process id no process has, so nothing waits on it.
            return new HelloResponse(protocol, answers.ToolchainIdentity, int.MaxValue);
        }

        [JsonRpcMethod(ServerProtocol.Status)]
        public async Task<ServerStatus> Status(CancellationToken cancellationToken)
        {
            Record(ServerProtocol.Status);
            if (_wedged)
            {
                await Task.Delay(Timeout.Infinite, cancellationToken);
            }
            return new ServerStatus(
                int.MaxValue, "stub", answers.ToolchainIdentity, TimeSpan.Zero, answers.BundleSha256, answers.SidecarSha256, 0, 0, new VerifyCounters(0, 0, 0, 0), []);
        }

        /// <summary>Every unit it is given proved or translated, without looking at any of them.</summary>
        [JsonRpcMethod(ServerProtocol.Verify)]
        public async Task<VerifyResponse> Verify(VerifyRequest request, CancellationToken cancellationToken)
        {
            Record(ServerProtocol.Verify);
            if (answers.Wedged)
            {
                _wedged = true;
                await Task.Delay(Timeout.Infinite, cancellationToken);
            }
            return new VerifyResponse(
                request.ProtocolVersion,
                request.RequestId,
                [
                    .. answers.Units(request.Units).Select(u => new UnitResult(
                        new OutcomeDto(u.Kind == VirUnitKind.Theorem ? OutcomeKind.Proved : OutcomeKind.Translated, u.Key, u.Kind, u.DisplayName ?? u.Key, [])
                        {
                            By = u.Kind == VirUnitKind.Theorem ? ProofKind.Script : null,
                        },
                        FromCache: false, Rechecked: false, TimeSpan.Zero)),
                ],
                new VerifyCounters(0, 0, 0, 0),
                TimeSpan.Zero);
        }

        [JsonRpcMethod(ServerProtocol.Shutdown)]
        public void Shutdown() => Record(ServerProtocol.Shutdown);

        private void Record(string method)
        {
            lock (calls)
            {
                calls.Add(method);
            }
        }
    }
}

/// <summary>
/// The CLI never takes an answer from a server that is not the one it asked for (M5b R4, KTD5): a server of another
/// toolchain, one that loaded another semantics bundle or attribute sidecar, and an answer whose units are not the
/// request's each make <c>warrant verify --server auto</c> say why once and verify in-process.
/// </summary>
[Collection(ServerProcesses.Name)]
public sealed class ServerMismatchTests
{
    private const string FallbackPrefix = "Warrant: verification server unavailable (";

    private const string InProcessSummary = "Warrant: 2 verified units, 1 theorems proved, 0 not proved. [in-process]\n";

    [Fact]
    public async Task AServerOfAnotherToolchainIsNotUsed()
    {
        var other = new string('0', 64);
        var output = await VerifyAgainst(new StubServer.Answers { ToolchainIdentity = other }, out var calls);

        AssertFellBackOnce(output, $"the server runs toolchain {other}, not {Toolchain.Identity}");
        Assert.DoesNotContain(ServerProtocol.Verify, calls);
    }

    [Fact]
    public async Task AServerThatLoadedAnotherBundleIsNotUsed()
    {
        var other = new string('b', 64);
        var output = await VerifyAgainst(new StubServer.Answers { BundleSha256 = other }, out var calls);

        AssertFellBackOnce(output, $"the server loaded another semantics bundle ({other}, not {TestServer.Hashes.Bundle})");
        Assert.DoesNotContain(ServerProtocol.Verify, calls);
    }

    [Fact]
    public async Task AServerThatLoadedAnotherSidecarIsNotUsed()
    {
        var other = new string('c', 64);
        var output = await VerifyAgainst(new StubServer.Answers { SidecarSha256 = other }, out var calls);

        AssertFellBackOnce(output, $"the server loaded another attribute sidecar ({other}, not {TestServer.Hashes.Sidecar})");
        Assert.DoesNotContain(ServerProtocol.Verify, calls);
    }

    [Theory]
    [InlineData("reordered")]
    [InlineData("missing")]
    [InlineData("extra")]
    public async Task AnAnswerWhoseUnitsAreNotTheRequestsIsNotUsed(string change)
    {
        Func<ImmutableArray<RequestUnit>, IEnumerable<RequestUnit>> units = change switch
        {
            "reordered" => u => u.Reverse(),
            "missing" => u => u.Skip(1),
            _ => u => [.. u, u[0] with { Key = u[0].Key + "2" }],
        };
        var output = await VerifyAgainst(new StubServer.Answers { Units = units }, out var calls);

        AssertFellBackOnce(output, "the server's answer does not match the request");
        Assert.Contains(ServerProtocol.Verify, calls);
    }

    [Fact]
    public async Task AServerThatStopsAnsweringWhileItVerifiesIsAbandonedAfterTheHeartbeatTimeout()
    {
        var watch = Stopwatch.StartNew();
        var output = await VerifyAgainst(
            new StubServer.Answers { Wedged = true },
            out var calls,
            s => s with { HeartbeatInterval = TimeSpan.FromMilliseconds(100), HeartbeatTimeout = TimeSpan.FromSeconds(1) });

        AssertFellBackOnce(output, "the server stopped answering while it verified: the server did not answer status within 1 s");
        Assert.True(watch.Elapsed < TimeSpan.FromSeconds(30), $"the fallback took {watch.Elapsed}");
        lock (calls)
        {
            // hello, status, verify, then the heartbeat that was never answered.
            Assert.Equal([ServerProtocol.Hello, ServerProtocol.Status, ServerProtocol.Verify, ServerProtocol.Status], calls);
        }
    }

    /// <summary><c>warrant verify --server auto</c> with the stub on the endpoint; the calls the stub saw.</summary>
    private static Task<string> VerifyAgainst(
        StubServer.Answers answers, out List<string> calls, Func<ServerSettings, ServerSettings>? configure = null)
    {
        var stub = new StubServer(answers);
        calls = stub.Calls;
        return Run(stub, configure);

        static async Task<string> Run(StubServer stub, Func<ServerSettings, ServerSettings>? configure)
        {
            // Disposed after the stub, so it finds no server to shut down and starts none.
            await using var server = new TestServer(endpointName: stub.Endpoint.Name);
            await using (stub)
            {
                using var source = new SourceDirectory(SourceDirectory.Fast);
                var (code, output) = server.Verify([source.Path, "--server", "auto"], configure: configure);
                Assert.True(code == 0, output);
                // The stub was the only server: the CLI never started one of its own.
                Assert.False(Directory.Exists(server.CopyRoot), "the CLI copied a server to start");
                return output;
            }
        }
    }

    private static void AssertFellBackOnce(string output, string reason)
    {
        Assert.Equal(1, CountOf(output, FallbackPrefix));
        Assert.Contains($"{FallbackPrefix}{reason}); verifying in-process.\n", output, StringComparison.Ordinal);
        Assert.Matches(@"(?m)^  S\.Larger\(\) +proved \(", output);
        Assert.EndsWith(InProcessSummary, output, StringComparison.Ordinal);
    }

    private static int CountOf(string text, string value)
    {
        int count = 0;
        for (int at = text.IndexOf(value, StringComparison.Ordinal); at >= 0; at = text.IndexOf(value, at + 1, StringComparison.Ordinal))
        {
            count++;
        }
        return count;
    }
}
