using System.IO.Pipes;
using System.Net.Sockets;
using System.Runtime.InteropServices;
using StreamJsonRpc;
using Warrant.Engine.Service;

/// <summary>
/// The CLI's connection to a verification server (M5b KTD2, KTD3, KTD5; docs/m5b/01, 02). It checks that the server is
/// the current user's before saying anything to it: on Windows the pipe is opened with <c>CurrentUserOnly</c>; on Unix
/// the socket directory must be a real directory owned by the user with mode 0700, and the connected peer must run as
/// the user. Every failure is a <see cref="ServerUnavailableException"/>, which makes the CLI verify in-process.
/// </summary>
internal sealed class ServerClient : IDisposable
{
    private readonly JsonRpc _rpc;

    private ServerClient(JsonRpc rpc, ServerEndpoint endpoint)
    {
        _rpc = rpc;
        Endpoint = endpoint;
    }

    /// <summary>The endpoint connected to.</summary>
    public ServerEndpoint Endpoint { get; }

    /// <summary>The server's answer to <c>hello</c>.</summary>
    public HelloResponse? Hello { get; private set; }

    /// <summary>
    /// Connects to the server for the given toolchain files, starting one detached when none answers (KTD4), and says
    /// <c>hello</c>. A running server has <see cref="ServerSettings.ConnectTimeout"/> to accept the connection; a started
    /// one has <see cref="ServerSettings.StartTimeout"/>, which also bounds every <c>hello</c>, because a server answers it
    /// only once its bundle is loaded.
    /// </summary>
    /// <param name="settings">The settings.</param>
    /// <param name="hashes">The SHA-256 of the bundle and sidecar the CLI verifies with; the server must have loaded the same bundle and sidecar.</param>
    /// <param name="bundlePath">The bundle a started server loads.</param>
    /// <param name="sidecarPath">The sidecar a started server loads.</param>
    /// <param name="cancellationToken">Stops waiting.</param>
    /// <returns>The client, after a successful <c>hello</c> with the same toolchain, bundle and sidecar.</returns>
    /// <exception cref="ServerUnavailableException">No usable server could be reached or started.</exception>
    /// <exception cref="OperationCanceledException"><paramref name="cancellationToken"/> was cancelled.</exception>
    public static async Task<ServerClient> ConnectOrStartAsync(
        ServerSettings settings, BundleHashes hashes, string bundlePath, string sidecarPath, CancellationToken cancellationToken)
    {
        var directory = ServerLauncher.CopyDirectory(settings, hashes);
        var endpoint = Resolve(settings, directory);
        var client = await TryConnectAsync(endpoint, settings.ConnectTimeout, waitForStart: false, cancellationToken).ConfigureAwait(false);
        bool started = client is null;
        client ??= await StartAsync(settings, directory, endpoint, bundlePath, sidecarPath, cancellationToken).ConfigureAwait(false);
        try
        {
            await client.HelloAsync(settings.StartTimeout, cancellationToken).ConfigureAwait(false);
            var status = await WithTimeout(t => client.StatusAsync(t), settings.StartTimeout, "status", cancellationToken).ConfigureAwait(false);
            if (!string.Equals(status.BundleSha256, hashes.Bundle, StringComparison.Ordinal))
            {
                throw new ServerUnavailableException($"the server loaded another semantics bundle ({status.BundleSha256 ?? "unknown"}, not {hashes.Bundle})");
            }
            // The computed name covers the sidecar through the copy's directory; an overridden name does not.
            if (!string.Equals(status.SidecarSha256, hashes.Sidecar, StringComparison.Ordinal))
            {
                throw new ServerUnavailableException($"the server loaded another attribute sidecar ({status.SidecarSha256 ?? "unknown"}, not {hashes.Sidecar})");
            }
            ServerLauncher.MarkUsed(directory);
            return client;
        }
        catch (ServerUnavailableException ex)
        {
            client.Dispose();
            if (started)
            {
                // A server that started but never said hello, such as one that crashed loading the bundle, failed to start.
                ServerLauncher.RecordStartFailure(directory, ex.Message);
            }
            throw;
        }
        catch
        {
            client.Dispose();
            throw;
        }
    }

    /// <summary>
    /// Starts the server and connects to it, unless a start failed within <see cref="ServerSettings.StartRetryDelay"/>; a
    /// failure is recorded so that the builds after this one fall back at once instead of waiting for the start again.
    /// </summary>
    private static async Task<ServerClient> StartAsync(
        ServerSettings settings, string directory, ServerEndpoint endpoint, string bundlePath, string sidecarPath, CancellationToken cancellationToken)
    {
        ServerLauncher.ThrowIfStartFailedRecently(settings, directory);
        try
        {
            ServerLauncher.Start(settings, directory, endpoint, bundlePath, sidecarPath);
            return await TryConnectAsync(endpoint, settings.StartTimeout, waitForStart: true, cancellationToken).ConfigureAwait(false)
                ?? throw new ServerUnavailableException($"the server did not start within {settings.StartTimeout.TotalSeconds:0} s");
        }
        catch (ServerUnavailableException ex)
        {
            ServerLauncher.RecordStartFailure(directory, ex.Message);
            throw;
        }
    }

    /// <summary>Connects to a running server for the given toolchain files, without starting one, and says <c>hello</c>.</summary>
    /// <param name="settings">The settings.</param>
    /// <param name="hashes">The SHA-256 of the bundle and sidecar a build would use.</param>
    /// <param name="cancellationToken">Stops waiting.</param>
    /// <returns>The client, or null when no server is running.</returns>
    /// <exception cref="ServerUnavailableException">A server is there but cannot be used.</exception>
    public static async Task<ServerClient?> ConnectRunningAsync(ServerSettings settings, BundleHashes hashes, CancellationToken cancellationToken)
    {
        var endpoint = Resolve(settings, ServerLauncher.CopyDirectory(settings, hashes));
        var client = await TryConnectAsync(endpoint, settings.ConnectTimeout, waitForStart: false, cancellationToken).ConfigureAwait(false);
        if (client is null)
        {
            return null;
        }
        try
        {
            await client.HelloAsync(settings.StartTimeout, cancellationToken).ConfigureAwait(false);
            return client;
        }
        catch
        {
            client.Dispose();
            throw;
        }
    }

    /// <summary>The endpoint a build computes: <see cref="ServerSettings.Endpoint"/>, with a bad override as a reason.</summary>
    public static ServerEndpoint Resolve(ServerSettings settings, string serverDirectory)
    {
        try
        {
            return settings.Endpoint(serverDirectory);
        }
        catch (ArgumentException ex)
        {
            var name = settings.EndpointName ?? Environment.GetEnvironmentVariable(ServerEndpoint.EnvironmentVariable);
            throw new ServerUnavailableException($"the endpoint name '{name}' is not a plain file name", ex);
        }
    }

    /// <summary>
    /// Verifies a request on the server. Cancelling the token sends <c>$/cancelRequest</c> (KTD12). While the server
    /// works, the client asks for its <c>status</c> every <paramref name="heartbeatInterval"/>; a server that does not
    /// answer within <paramref name="heartbeatTimeout"/> is wedged, and the request is abandoned (and cancelled on the
    /// server, should it recover) so the CLI can verify in-process instead of waiting forever.
    /// </summary>
    /// <param name="request">The request.</param>
    /// <param name="heartbeatInterval">How often to check that the server answers.</param>
    /// <param name="heartbeatTimeout">How long each check waits.</param>
    /// <param name="cancellationToken">Cancels the request on the server.</param>
    /// <returns>The response, with one result per unit in the request's order.</returns>
    /// <exception cref="ServerUnavailableException">The connection was lost, the server failed the request or stopped answering, or its answer does not match the request.</exception>
    /// <exception cref="OperationCanceledException">The request was cancelled and the server answered with a cancellation.</exception>
    public async Task<VerifyResponse> VerifyAsync(VerifyRequest request, TimeSpan heartbeatInterval, TimeSpan heartbeatTimeout, CancellationToken cancellationToken)
    {
        VerifyResponse response;
        using var abandon = CancellationTokenSource.CreateLinkedTokenSource(cancellationToken);
        var call = _rpc.InvokeWithCancellationAsync<VerifyResponse>(ServerProtocol.Verify, [request], abandon.Token);
        while (!cancellationToken.IsCancellationRequested
            && await Task.WhenAny(call, Task.Delay(heartbeatInterval, cancellationToken)).ConfigureAwait(false) != call)
        {
            if (cancellationToken.IsCancellationRequested)
            {
                break;
            }
            try
            {
                await WithTimeout(t => StatusAsync(t), heartbeatTimeout, "status", cancellationToken).ConfigureAwait(false);
            }
            catch (ServerUnavailableException ex)
            {
                await abandon.CancelAsync().ConfigureAwait(false);
                // The abandoned call ends cancelled or with the lost connection; nobody waits for it.
                _ = call.ContinueWith(t => _ = t.Exception, CancellationToken.None, TaskContinuationOptions.OnlyOnFaulted, TaskScheduler.Default);
                throw new ServerUnavailableException($"the server stopped answering while it verified: {ex.Message}", ex);
            }
        }
        try
        {
            response = await call.ConfigureAwait(false);
        }
        catch (OperationCanceledException) when (cancellationToken.IsCancellationRequested)
        {
            throw;
        }
        catch (Exception ex) when (ex is ConnectionLostException or ObjectDisposedException or IOException or OperationCanceledException)
        {
            throw new ServerUnavailableException($"the connection to the server was lost: {ex.Message}", ex);
        }
        catch (RemoteInvocationException ex)
        {
            throw new ServerUnavailableException($"the server failed the request: {ex.Message}", ex);
        }
        if (response is null || response.Units.Length != request.Units.Length
            || !response.Units.Select(u => u.Outcome.Key).SequenceEqual(request.Units.Select(u => u.Key), StringComparer.Ordinal))
        {
            throw new ServerUnavailableException("the server's answer does not match the request");
        }
        return response;
    }

    /// <summary><c>status()</c>.</summary>
    public Task<ServerStatus> StatusAsync(CancellationToken cancellationToken = default) =>
        _rpc.InvokeWithCancellationAsync<ServerStatus>(ServerProtocol.Status, [], cancellationToken);

    /// <summary><c>cancel(id)</c>: whether a request with that id was running.</summary>
    public Task<bool> CancelAsync(string requestId, CancellationToken cancellationToken = default) =>
        _rpc.InvokeWithCancellationAsync<bool>(ServerProtocol.Cancel, [requestId], cancellationToken);

    /// <summary><c>shutdown()</c>: the server finishes its running requests, then exits.</summary>
    public Task ShutdownAsync(CancellationToken cancellationToken = default) =>
        _rpc.InvokeWithCancellationAsync(ServerProtocol.Shutdown, [], cancellationToken);

    /// <summary>Closes the connection; a request still running on the server is cancelled.</summary>
    public void Dispose() => _rpc.Dispose();

    private async Task HelloAsync(TimeSpan timeout, CancellationToken cancellationToken)
    {
        var hello = await WithTimeout(
            t => _rpc.InvokeWithCancellationAsync<HelloResponse>(ServerProtocol.Hello, [VerificationService.ProtocolVersion], t),
            timeout, "hello", cancellationToken).ConfigureAwait(false);
        // The endpoint's name covers the toolchain, but an overridden name does not: a server running other code must
        // not answer for this one (M5b R4).
        if (!string.Equals(hello.ToolchainIdentity, Toolchain.Identity, StringComparison.Ordinal))
        {
            throw new ServerUnavailableException($"the server runs toolchain {hello.ToolchainIdentity}, not {Toolchain.Identity}");
        }
        Hello = hello;
    }

    private static async Task<T> WithTimeout<T>(Func<CancellationToken, Task<T>> call, TimeSpan timeout, string method, CancellationToken cancellationToken)
    {
        using var limit = CancellationTokenSource.CreateLinkedTokenSource(cancellationToken);
        limit.CancelAfter(timeout);
        try
        {
            return await call(limit.Token).ConfigureAwait(false);
        }
        catch (OperationCanceledException) when (cancellationToken.IsCancellationRequested)
        {
            throw;
        }
        catch (OperationCanceledException ex)
        {
            throw new ServerUnavailableException($"the server did not answer {method} within {timeout.TotalSeconds:0} s", ex);
        }
        catch (RemoteInvocationException ex)
        {
            throw new ServerUnavailableException($"the server refused {method}: {ex.Message}", ex);
        }
        catch (Exception ex) when (ex is ConnectionLostException or ObjectDisposedException or IOException)
        {
            throw new ServerUnavailableException($"the connection to the server was lost: {ex.Message}", ex);
        }
    }

    /// <summary>
    /// Connects to an endpoint. Null means no server is running there: no pipe or socket, a stale socket, or, when
    /// <paramref name="waitForStart"/>, none appeared within the timeout.
    /// </summary>
    private static async Task<ServerClient?> TryConnectAsync(ServerEndpoint endpoint, TimeSpan timeout, bool waitForStart, CancellationToken cancellationToken)
    {
        var stream = endpoint.SocketDirectory is null
            ? await ConnectPipeAsync(endpoint, timeout, waitForStart, cancellationToken).ConfigureAwait(false)
            : await ConnectSocketAsync(endpoint, timeout, waitForStart, cancellationToken).ConfigureAwait(false);
        if (stream is null)
        {
            return null;
        }
        var formatter = new SystemTextJsonFormatter { JsonSerializerOptions = ServerProtocol.CreateSerializerOptions() };
        var rpc = new JsonRpc(new HeaderDelimitedMessageHandler(stream, stream, formatter));
        rpc.StartListening();
        return new ServerClient(rpc, endpoint);
    }

    private static async Task<Stream?> ConnectPipeAsync(ServerEndpoint endpoint, TimeSpan timeout, bool waitForStart, CancellationToken cancellationToken)
    {
        if (!waitForStart && !PipeExists(endpoint.Address))
        {
            return null;
        }
        // CurrentUserOnly: the connection fails unless the pipe's owner is the current user (KTD3).
        var pipe = new NamedPipeClientStream(".", endpoint.Address, PipeDirection.InOut, PipeOptions.Asynchronous | PipeOptions.CurrentUserOnly);
        try
        {
            await pipe.ConnectAsync(timeout, cancellationToken).ConfigureAwait(false);
            return pipe;
        }
        catch (TimeoutException) when (waitForStart)
        {
            await pipe.DisposeAsync().ConfigureAwait(false);
            return null;
        }
        catch (Exception ex)
        {
            await pipe.DisposeAsync().ConfigureAwait(false);
            throw ex switch
            {
                OperationCanceledException => ex,
                TimeoutException => new ServerUnavailableException($"connecting to the server timed out after {timeout.TotalSeconds:0} s", ex),
                UnauthorizedAccessException => new ServerUnavailableException($"the pipe '{endpoint.Address}' is not the current user's: {ex.Message}", ex),
                IOException => new ServerUnavailableException($"the pipe '{endpoint.Address}' could not be opened: {ex.Message}", ex),
                _ => ex,
            };
        }
    }

    /// <summary>Whether a pipe of the name exists, by listing the pipe namespace, which, unlike opening it, never takes an instance.</summary>
    private static bool PipeExists(string name)
    {
        try
        {
            return Directory.EnumerateFiles(@"\\.\pipe\", name).Any();
        }
        catch (Exception ex) when (ex is IOException or UnauthorizedAccessException or ArgumentException)
        {
            // Unlisted: try to connect, as to a running server.
            return true;
        }
    }

    private static async Task<Stream?> ConnectSocketAsync(ServerEndpoint endpoint, TimeSpan timeout, bool waitForStart, CancellationToken cancellationToken)
    {
        var deadline = DateTime.UtcNow + timeout;
        while (true)
        {
            if (await TryConnectSocketOnceAsync(endpoint, timeout, cancellationToken).ConfigureAwait(false) is { } stream)
            {
                return stream;
            }
            if (!waitForStart || DateTime.UtcNow >= deadline)
            {
                return null;
            }
            await Task.Delay(50, cancellationToken).ConfigureAwait(false);
        }
    }

    private static async Task<Stream?> TryConnectSocketOnceAsync(ServerEndpoint endpoint, TimeSpan timeout, CancellationToken cancellationToken)
    {
        var directory = endpoint.SocketDirectory!;
        var info = new DirectoryInfo(directory);
        if (!info.Exists && info.LinkTarget is null)
        {
            // The first server creates the directory: none has run. A link, even a dangling one, fails the check below.
            return null;
        }
        if (!ServerEndpoint.CheckDirectory(directory, out var problem))
        {
            throw new ServerUnavailableException(problem!);
        }
        if (!File.Exists(endpoint.Address))
        {
            return null;
        }
        var socket = new Socket(AddressFamily.Unix, SocketType.Stream, ProtocolType.Unspecified);
        try
        {
            using (var limit = CancellationTokenSource.CreateLinkedTokenSource(cancellationToken))
            {
                limit.CancelAfter(timeout);
                try
                {
                    await socket.ConnectAsync(new UnixDomainSocketEndPoint(endpoint.Address), limit.Token).ConfigureAwait(false);
                }
                catch (OperationCanceledException ex) when (!cancellationToken.IsCancellationRequested)
                {
                    throw new ServerUnavailableException($"connecting to the server timed out after {timeout.TotalSeconds:0} s", ex);
                }
            }
            uint peer = PeerUserId(socket);
            uint user = ServerEndpoint.EffectiveUserId();
            if (peer != user)
            {
                throw new ServerUnavailableException($"the socket '{endpoint.Address}' is served by user {peer}, not {user}");
            }
            return new NetworkStream(socket, ownsSocket: true);
        }
        catch (SocketException ex) when (ex.SocketErrorCode is SocketError.ConnectionRefused or SocketError.AddressNotAvailable or SocketError.AddressFamilyNotSupported)
        {
            // A socket file a dead server left: nobody serves it.
            socket.Dispose();
            return null;
        }
        catch (SocketException ex)
        {
            socket.Dispose();
            throw new ServerUnavailableException($"the socket '{endpoint.Address}' could not be connected: {ex.Message}", ex);
        }
        catch
        {
            socket.Dispose();
            throw;
        }
    }

    /// <summary>The user id of the process at the other end of a connected Unix socket.</summary>
    private static uint PeerUserId(Socket socket)
    {
        bool added = false;
        var handle = socket.SafeHandle;
        try
        {
            handle.DangerousAddRef(ref added);
            if (Unix.GetPeerId(handle.DangerousGetHandle(), out uint uid) != 0)
            {
                throw new ServerUnavailableException("the server's user could not be determined");
            }
            return uid;
        }
        finally
        {
            if (added)
            {
                handle.DangerousRelease();
            }
        }
    }

    /// <summary>The runtime's own System.Native shim: <c>SO_PEERCRED</c> or <c>getpeereid</c>, as <c>NamedPipeServerStream</c> uses it.</summary>
    private static class Unix
    {
        private const string SystemNative = "libSystem.Native";

        [DllImport(SystemNative, EntryPoint = "SystemNative_GetPeerID")]
        [DefaultDllImportSearchPaths(DllImportSearchPath.SafeDirectories)]
        public static extern int GetPeerId(IntPtr socket, out uint euid);
    }
}
