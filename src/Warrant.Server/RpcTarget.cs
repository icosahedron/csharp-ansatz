using System.Text.Json;
using StreamJsonRpc;
using Warrant.Engine.Service;

namespace Warrant.Server;

/// <summary>
/// The protocol's methods (M5b KTD2, KTD12, KTD26; docs/m5b/01), one instance per connection. Its public methods are
/// exactly the protocol's, each named by <see cref="JsonRpcMethodAttribute"/>, so nothing else is callable.
/// </summary>
internal sealed class RpcTarget(ServerHost host, VerificationService service)
{
    /// <summary>The wire's JSON options (<see cref="ServerProtocol.CreateSerializerOptions"/>).</summary>
    public static JsonSerializerOptions SerializerOptions { get; } = ServerProtocol.CreateSerializerOptions();

    /// <summary>
    /// Checks the client's protocol version. A mismatch is an error, and the server drains and exits, so the next client
    /// starts a server that speaks its version.
    /// </summary>
    /// <param name="protocol">The client's protocol version.</param>
    /// <returns>The server's protocol, toolchain identity and process id.</returns>
    /// <exception cref="LocalRpcException">The version is not <see cref="VerificationService.ProtocolVersion"/>.</exception>
    [JsonRpcMethod(ServerProtocol.Hello)]
    public HelloResponse Hello(int protocol)
    {
        if (protocol != VerificationService.ProtocolVersion)
        {
            host.Drain($"a client spoke protocol {protocol}");
            throw new LocalRpcException($"the server speaks protocol {VerificationService.ProtocolVersion}, not {protocol}; it is shutting down")
            {
                ErrorCode = ServerProtocol.ProtocolMismatchError,
            };
        }
        return new HelloResponse(VerificationService.ProtocolVersion, Toolchain.Identity, Environment.ProcessId);
    }

    /// <summary>
    /// Verifies a request on a thread of its own. Its work stops when the client sends <c>$/cancelRequest</c>, when the
    /// connection closes, or when any client calls <c>cancel</c> with its id (KTD12); units that finished keep their
    /// outcomes and the rest are cancelled.
    /// </summary>
    /// <param name="request">The request.</param>
    /// <param name="cancellationToken">The RPC's token.</param>
    /// <returns>The response.</returns>
    /// <exception cref="LocalRpcException">The server is draining, or another running request has the id.</exception>
    [JsonRpcMethod(ServerProtocol.Verify)]
    public async Task<VerifyResponse> VerifyAsync(VerifyRequest request, CancellationToken cancellationToken)
    {
        ArgumentNullException.ThrowIfNull(request);
        using var running = host.Begin(request, cancellationToken);
        host.Log.Write($"verify {request.RequestId}: {request.Units.Length} units of {request.ProjectDirectory}");
        var response = await Task.Factory.StartNew(
            () => service.Verify(request, running.Token), CancellationToken.None, TaskCreationOptions.LongRunning, TaskScheduler.Default).ConfigureAwait(false);
        host.Log.Write($"verified {request.RequestId} in {response.Elapsed.TotalMilliseconds:0} ms{(running.Token.IsCancellationRequested ? " (cancelled)" : "")}");
        return response;
    }

    /// <summary>
    /// Verifies one unit and its closure with a trace of its proof script (KTD24), without the cache, on a thread of its
    /// own; it is cancelled as <see cref="VerifyAsync"/> is.
    /// </summary>
    /// <param name="request">The request and the unit to trace.</param>
    /// <param name="cancellationToken">The RPC's token.</param>
    /// <returns>The response and the steps.</returns>
    /// <exception cref="LocalRpcException">The server is draining, or another running request has the id.</exception>
    [JsonRpcMethod(ServerProtocol.Explain)]
    public Task<ExplainResponse> ExplainAsync(ExplainRequest request, CancellationToken cancellationToken)
    {
        ArgumentNullException.ThrowIfNull(request);
        return RunAsync(request.Request, "explain", token => service.Explain(request, token), r => r.Response, cancellationToken);
    }

    /// <summary>Verifies a request without the cache and returns the certificate file of what it admitted (KTD25).</summary>
    /// <param name="request">The request.</param>
    /// <param name="cancellationToken">The RPC's token.</param>
    /// <returns>The response and the certificates.</returns>
    /// <exception cref="LocalRpcException">The server is draining, or another running request has the id.</exception>
    [JsonRpcMethod(ServerProtocol.Export)]
    public Task<ExportResponse> ExportAsync(VerifyRequest request, CancellationToken cancellationToken)
    {
        ArgumentNullException.ThrowIfNull(request);
        return RunAsync(request, "export", token => service.Export(request, token), r => r.Response, cancellationToken);
    }

    /// <summary>The JSON assumption report of a project directory's last verify that asked for one (KTD25).</summary>
    /// <param name="projectDirectory">The directory, as the request named it.</param>
    /// <returns>The report, or null when there is none.</returns>
    [JsonRpcMethod(ServerProtocol.Report)]
    public string? Report(string projectDirectory) => service.Report(projectDirectory);

    private async Task<T> RunAsync<T>(VerifyRequest request, string verb, Func<CancellationToken, T> work, Func<T, VerifyResponse> response, CancellationToken cancellationToken)
    {
        using var running = host.Begin(request, cancellationToken);
        host.Log.Write($"{verb} {request.RequestId}: {request.Units.Length} units of {request.ProjectDirectory}");
        var result = await Task.Factory.StartNew(
            () => work(running.Token), CancellationToken.None, TaskCreationOptions.LongRunning, TaskScheduler.Default).ConfigureAwait(false);
        host.Log.Write($"{verb} {request.RequestId} done in {response(result).Elapsed.TotalMilliseconds:0} ms{(running.Token.IsCancellationRequested ? " (cancelled)" : "")}");
        return result;
    }

    /// <summary>Cancels the running request with an id, whichever connection sent it.</summary>
    /// <param name="id">The request's id.</param>
    /// <returns>Whether such a request was running.</returns>
    [JsonRpcMethod(ServerProtocol.Cancel)]
    public bool Cancel(string id) => host.Cancel(id);

    /// <summary>What the server holds and runs (KTD26).</summary>
    /// <returns>The status.</returns>
    [JsonRpcMethod(ServerProtocol.Status)]
    public ServerStatus Status() => new(
        Environment.ProcessId,
        host.Endpoint.Address,
        Toolchain.Identity,
        host.Uptime,
        service.Hashes?.Bundle,
        service.Hashes?.Sidecar,
        GC.GetGCMemoryInfo().HeapSizeBytes,
        Environment.WorkingSet,
        service.Totals,
        host.ActiveRequests());

    /// <summary>Lets the running requests finish, then exits.</summary>
    [JsonRpcMethod(ServerProtocol.Shutdown)]
    public void Shutdown() => host.Drain("shutdown requested");
}
