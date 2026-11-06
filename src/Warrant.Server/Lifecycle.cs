using System.Collections.Immutable;
using System.Diagnostics;
using StreamJsonRpc;
using Warrant.Engine.Service;

namespace Warrant.Server;

/// <summary>
/// A server's lifecycle (M5b KTD4, docs/m5b/01): it holds the endpoint, accepts connections and gives each its own
/// <see cref="JsonRpc"/> (KTD2), tracks the running requests by id, leaves when no connection and no work has been there
/// for the idle period, and drains on <c>shutdown</c> or a mismatched <c>hello</c>: no new request starts, the running
/// ones finish, then it exits.
/// </summary>
internal sealed class ServerHost : IDisposable
{
    /// <summary>How long a server waits after its last connection closes and its work ends: Roslyn's compiler server's 10 minutes.</summary>
    public static readonly TimeSpan DefaultIdleTimeout = TimeSpan.FromMinutes(10);

    /// <summary>The environment variable that sets the idle period in seconds.</summary>
    public const string IdleEnvironmentVariable = "WARRANT_SERVER_IDLE_SECONDS";

    /// <summary>How long a drained server lets its clients hang up, so every answer it sent is read, before it closes them.</summary>
    private static readonly TimeSpan HangUpGrace = TimeSpan.FromSeconds(1);

    private readonly EndpointListener _listener;
    private readonly Stopwatch _uptime = Stopwatch.StartNew();
    private readonly CancellationTokenSource _stopAccepting = new();
    private readonly TaskCompletionSource _drained = new(TaskCreationOptions.RunContinuationsAsynchronously);
    private readonly Lock _lock = new();
    private readonly Dictionary<string, Running> _running = new(StringComparer.Ordinal);
    private readonly HashSet<JsonRpc> _connections = [];
    private CancellationTokenSource? _idle;
    private bool _draining;

    private ServerHost(EndpointListener listener, ServerLog log, TimeSpan idleTimeout)
    {
        _listener = listener;
        Log = log;
        IdleTimeout = idleTimeout;
    }

    /// <summary>The endpoint the server holds.</summary>
    public ServerEndpoint Endpoint => _listener.Endpoint;

    /// <summary>The log.</summary>
    public ServerLog Log { get; }

    /// <summary>How long the server stays with no connection and no work.</summary>
    public TimeSpan IdleTimeout { get; }

    /// <summary>The time since the endpoint was acquired.</summary>
    public TimeSpan Uptime => _uptime.Elapsed;

    /// <summary>Whether the server is draining: it starts no new request and exits once the running ones end.</summary>
    public bool IsDraining
    {
        get
        {
            lock (_lock)
            {
                return _draining;
            }
        }
    }

    /// <summary>Acquires an endpoint: null, after a line in the log, when another server holds it.</summary>
    /// <param name="endpoint">The endpoint.</param>
    /// <param name="log">The log.</param>
    /// <param name="idleTimeout">How long to stay with no connection and no work.</param>
    /// <returns>The host, which has not started serving.</returns>
    /// <exception cref="EndpointRefusedException">The socket directory failed KTD3's checks.</exception>
    public static ServerHost? TryAcquire(ServerEndpoint endpoint, ServerLog log, TimeSpan idleTimeout)
    {
        ArgumentNullException.ThrowIfNull(endpoint);
        ArgumentNullException.ThrowIfNull(log);
        if (EndpointListener.TryAcquire(endpoint) is not { } listener)
        {
            log.Write($"endpoint {endpoint.Address} is held by another server; exiting");
            return null;
        }
        log.Write($"acquired endpoint {endpoint.Address}");
        return new ServerHost(listener, log, idleTimeout);
    }

    /// <summary>The idle period: <see cref="IdleEnvironmentVariable"/> when it holds a whole number of seconds, else the default.</summary>
    /// <returns>The period.</returns>
    public static TimeSpan IdleTimeoutFromEnvironment() =>
        int.TryParse(Environment.GetEnvironmentVariable(IdleEnvironmentVariable), System.Globalization.NumberStyles.None, System.Globalization.CultureInfo.InvariantCulture, out int seconds)
            ? TimeSpan.FromSeconds(seconds)
            : DefaultIdleTimeout;

    /// <summary>Serves connections until the server is idle or drained, then closes them and releases the endpoint.</summary>
    /// <param name="service">The service requests run on; the caller owns it.</param>
    /// <returns>A task that ends when the server has stopped.</returns>
    public async Task RunAsync(VerificationService service)
    {
        ArgumentNullException.ThrowIfNull(service);
        Log.Write($"serving {Endpoint.Address} (toolchain {Toolchain.Identity}, {service.Workers} workers, idle {IdleTimeout.TotalSeconds:0} s)");
        UpdateIdle();
        var connections = new List<Task>();
        try
        {
            while (true)
            {
                Stream stream;
                try
                {
                    stream = await _listener.AcceptAsync(_stopAccepting.Token).ConfigureAwait(false);
                }
                catch (OperationCanceledException)
                {
                    break;
                }
                catch (ConnectionDroppedException ex)
                {
                    Log.Write($"a client hung up before its connection was accepted: {ex.Message}");
                    continue;
                }
                catch (Exception ex)
                {
                    Log.Write($"stopped accepting connections: {ex.Message}");
                    throw;
                }
                connections.Add(ServeAsync(stream, service));
                connections.RemoveAll(c => c.IsCompleted);
            }
        }
        finally
        {
            _listener.Dispose();
        }
        await _drained.Task.ConfigureAwait(false);
        JsonRpc[] open;
        lock (_lock)
        {
            open = [.. _connections];
        }
        await Task.WhenAny(Task.WhenAll(open.Select(c => c.Completion.ContinueWith(_ => { }, TaskScheduler.Default))), Task.Delay(HangUpGrace)).ConfigureAwait(false);
        foreach (var connection in open)
        {
            connection.Dispose();
        }
        await Task.WhenAll(connections).ConfigureAwait(false);
        Log.Write("stopped");
    }

    /// <summary>Starts draining: no new request starts, and the server exits once the running ones end.</summary>
    /// <param name="reason">Why, for the log.</param>
    public void Drain(string reason) => TryDrain(reason, onlyIfIdle: false);

    private void TryDrain(string reason, bool onlyIfIdle)
    {
        bool drained;
        lock (_lock)
        {
            if (_draining || (onlyIfIdle && (_connections.Count > 0 || _running.Count > 0)))
            {
                return;
            }
            _draining = true;
            _idle?.Cancel();
            drained = _running.Count == 0;
        }
        Log.Write($"draining: {reason}");
        _stopAccepting.Cancel();
        if (drained)
        {
            _drained.TrySetResult();
        }
    }

    /// <summary>Registers a request as running, linking its token to the RPC's (which <c>$/cancelRequest</c> and the connection closing cancel) and to <see cref="Cancel"/>.</summary>
    /// <param name="request">The request.</param>
    /// <param name="rpcToken">The RPC's token.</param>
    /// <returns>The running request, which the caller disposes when the request ends.</returns>
    /// <exception cref="LocalRpcException">The server is draining, or another running request has the id.</exception>
    public Running Begin(VerifyRequest request, CancellationToken rpcToken)
    {
        ArgumentNullException.ThrowIfNull(request);
        lock (_lock)
        {
            if (_draining)
            {
                throw new LocalRpcException("the server is shutting down") { ErrorCode = ServerProtocol.ShuttingDownError };
            }
            if (_running.ContainsKey(request.RequestId))
            {
                throw new LocalRpcException($"a request with id '{request.RequestId}' is already running") { ErrorCode = ServerProtocol.RequestIdInUseError };
            }
            var running = new Running(this, request, CancellationTokenSource.CreateLinkedTokenSource(rpcToken));
            _running.Add(request.RequestId, running);
            _idle?.Cancel();
            return running;
        }
    }

    /// <summary>Cancels the running request with an id, whichever connection sent it.</summary>
    /// <param name="requestId">The id.</param>
    /// <returns>Whether such a request was running.</returns>
    public bool Cancel(string requestId)
    {
        ArgumentNullException.ThrowIfNull(requestId);
        Running? running;
        lock (_lock)
        {
            _running.TryGetValue(requestId, out running);
        }
        if (running is null)
        {
            return false;
        }
        Log.Write($"cancel {requestId}");
        try
        {
            running.CancelSource.Cancel();
        }
        catch (ObjectDisposedException)
        {
            // It ended meanwhile.
        }
        return true;
    }

    /// <summary>The requests running now, oldest first.</summary>
    /// <returns>The requests.</returns>
    public ImmutableArray<ActiveRequest> ActiveRequests()
    {
        lock (_lock)
        {
            return [.. _running.Values.OrderByDescending(r => r.Elapsed.Elapsed).Select(r => new ActiveRequest(r.Request.RequestId, r.Request.ProjectDirectory, r.Request.Units.Length, r.Elapsed.Elapsed))];
        }
    }

    /// <summary>Releases the endpoint if <see cref="RunAsync"/> never ran.</summary>
    public void Dispose()
    {
        Drain("disposed");
        _listener.Dispose();
        _stopAccepting.Dispose();
    }

    private async Task ServeAsync(Stream stream, VerificationService service)
    {
        var formatter = new SystemTextJsonFormatter { JsonSerializerOptions = RpcTarget.SerializerOptions };
        var rpc = new JsonRpc(new HeaderDelimitedMessageHandler(stream, stream, formatter))
        {
            SynchronizationContext = null,
            CancelLocallyInvokedMethodsWhenConnectionIsClosed = true,
        };
        rpc.AddLocalRpcTarget(new RpcTarget(this, service), new JsonRpcTargetOptions { AllowNonPublicInvocation = false });
        lock (_lock)
        {
            _connections.Add(rpc);
            _idle?.Cancel();
        }
        try
        {
            rpc.StartListening();
            await rpc.Completion.ConfigureAwait(false);
        }
        catch (Exception ex)
        {
            Log.Write($"a connection ended with an error: {ex.Message}");
        }
        finally
        {
            rpc.Dispose();
            await stream.DisposeAsync().ConfigureAwait(false);
            lock (_lock)
            {
                _connections.Remove(rpc);
            }
            UpdateIdle();
        }
    }

    private void End(Running running)
    {
        bool drained;
        lock (_lock)
        {
            _running.Remove(running.Request.RequestId);
            drained = _draining && _running.Count == 0;
        }
        if (drained)
        {
            _drained.TrySetResult();
        }
        UpdateIdle();
    }

    /// <summary>Starts the idle timer when there is no connection and no work, and the server is not draining.</summary>
    private void UpdateIdle()
    {
        CancellationTokenSource idle;
        lock (_lock)
        {
            if (_draining || _connections.Count > 0 || _running.Count > 0 || _idle is { IsCancellationRequested: false })
            {
                return;
            }
            _idle = idle = new CancellationTokenSource();
        }
        _ = IdleAsync(idle.Token);
    }

    private async Task IdleAsync(CancellationToken cancellationToken)
    {
        try
        {
            await Task.Delay(IdleTimeout, cancellationToken).ConfigureAwait(false);
        }
        catch (OperationCanceledException)
        {
            return;
        }
        // A connection that arrived as the delay ended keeps the server.
        TryDrain($"idle for {IdleTimeout.TotalSeconds:0} s", onlyIfIdle: true);
    }

    /// <summary>A running request: its cancellation source, linked to the RPC's token, and its age.</summary>
    internal sealed class Running(ServerHost host, VerifyRequest request, CancellationTokenSource cancelSource) : IDisposable
    {
        /// <summary>The request.</summary>
        public VerifyRequest Request { get; } = request;

        /// <summary>Cancels the request's work.</summary>
        public CancellationTokenSource CancelSource { get; } = cancelSource;

        /// <summary>The time since it arrived.</summary>
        public Stopwatch Elapsed { get; } = Stopwatch.StartNew();

        /// <summary>The token the request's work runs under.</summary>
        public CancellationToken Token => CancelSource.Token;

        /// <summary>Removes the request from the running set.</summary>
        public void Dispose()
        {
            host.End(this);
            CancelSource.Dispose();
        }
    }
}
