using System.Text.Json;
using StreamJsonRpc;
using Warrant.Engine.Service;

namespace Warrant.Server;

/// <summary>
/// The protocol's methods (M5b KTD2, KTD12, KTD26; docs/m5b/01), one instance per connection. Its public methods are
/// exactly the protocol's, each named by <see cref="JsonRpcMethodAttribute"/>, so nothing else is callable.
/// </summary>
/// <remarks><c>explain</c>, <c>export</c> and <c>report</c> arrive with plan unit U16 and are not registered yet.</remarks>
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
