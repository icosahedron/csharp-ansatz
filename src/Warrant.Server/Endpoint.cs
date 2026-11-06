using System.IO.Pipes;
using System.Net.Sockets;
using Warrant.Engine.Service;

namespace Warrant.Server;

/// <summary>The endpoint's socket directory failed KTD3's checks, so the server refuses to start.</summary>
/// <param name="message">Why.</param>
internal sealed class EndpointRefusedException(string message) : Exception(message);

/// <summary>A client left before its connection was accepted; the listener is ready for the next one.</summary>
/// <param name="message">Why the connection failed.</param>
/// <param name="inner">The failure.</param>
internal sealed class ConnectionDroppedException(string message, Exception inner) : IOException(message, inner);

/// <summary>
/// Holds a <see cref="ServerEndpoint"/> and accepts its connections (M5b KTD3). Holding the endpoint is what makes a
/// server the only one of its name: the first named-pipe instance on Windows, an exclusive lock file on Unix.
/// </summary>
internal abstract class EndpointListener : IDisposable
{
    /// <summary>The endpoint.</summary>
    public required ServerEndpoint Endpoint { get; init; }

    /// <summary>Acquires an endpoint: null when another server holds it.</summary>
    /// <param name="endpoint">The endpoint.</param>
    /// <returns>The listener, or null.</returns>
    /// <exception cref="EndpointRefusedException">The socket directory is not a real directory owned by the user with mode 0700.</exception>
    public static EndpointListener? TryAcquire(ServerEndpoint endpoint)
    {
        ArgumentNullException.ThrowIfNull(endpoint);
        return endpoint.SocketDirectory is null ? PipeListener.TryAcquirePipe(endpoint) : SocketListener.TryAcquireSocket(endpoint);
    }

    /// <summary>Waits for the next connection.</summary>
    /// <param name="cancellationToken">Stops waiting.</param>
    /// <returns>The connection's stream, which the caller disposes.</returns>
    /// <exception cref="ConnectionDroppedException">A client left before its connection was accepted; the caller waits again.</exception>
    public abstract Task<Stream> AcceptAsync(CancellationToken cancellationToken);

    /// <summary>Releases the endpoint; connections already accepted stay open.</summary>
    public abstract void Dispose();
}

/// <summary>
/// A named pipe opened with <c>CurrentUserOnly</c>; the first instance with <c>FirstPipeInstance</c>, so a second server
/// cannot open the name. A listening instance always exists while the server runs: the next one is created before an
/// accepted one is handed out, so the name is never free.
/// </summary>
internal sealed class PipeListener : EndpointListener
{
    private NamedPipeServerStream _listening;

    private PipeListener(NamedPipeServerStream first) => _listening = first;

    public static PipeListener? TryAcquirePipe(ServerEndpoint endpoint)
    {
        try
        {
            return new PipeListener(Create(endpoint.Address, first: true)) { Endpoint = endpoint };
        }
        catch (Exception ex) when (ex is UnauthorizedAccessException or IOException)
        {
            return null;
        }
    }

    public override async Task<Stream> AcceptAsync(CancellationToken cancellationToken)
    {
        try
        {
            await _listening.WaitForConnectionAsync(cancellationToken).ConfigureAwait(false);
        }
        catch (IOException ex)
        {
            // A client connected to the instance and hung up before the wait completed, which breaks the instance. A
            // fresh one replaces it, created before the broken one closes so the name is never free.
            var broken = _listening;
            _listening = Create(Endpoint.Address, first: false);
            await broken.DisposeAsync().ConfigureAwait(false);
            throw new ConnectionDroppedException(ex.Message, ex);
        }
        var connected = _listening;
        try
        {
            _listening = Create(Endpoint.Address, first: false);
        }
        catch
        {
            await connected.DisposeAsync().ConfigureAwait(false);
            throw;
        }
        return connected;
    }

    public override void Dispose() => _listening.Dispose();

    private static NamedPipeServerStream Create(string name, bool first) => new(
        name,
        PipeDirection.InOut,
        NamedPipeServerStream.MaxAllowedServerInstances,
        PipeTransmissionMode.Byte,
        PipeOptions.Asynchronous | PipeOptions.CurrentUserOnly | (first ? PipeOptions.FirstPipeInstance : PipeOptions.None));
}

/// <summary>
/// A Unix domain socket in the checked per-user directory, guarded by an exclusive lock on <see cref="ServerEndpoint.LockPath"/>:
/// the holder of the lock may remove a stale socket file and bind, and nobody else may.
/// </summary>
internal sealed class SocketListener : EndpointListener
{
    private readonly FileStream _lock;
    private readonly Socket _socket;
    private bool _disposed;

    private SocketListener(FileStream @lock, Socket socket)
    {
        _lock = @lock;
        _socket = socket;
    }

    public static SocketListener? TryAcquireSocket(ServerEndpoint endpoint)
    {
        var directory = endpoint.SocketDirectory!;
        if (!ServerEndpoint.TryPrepareDirectory(directory, out var problem))
        {
            throw new EndpointRefusedException(problem!);
        }
        FileStream @lock;
        try
        {
            // FileShare.None takes an exclusive advisory lock (flock) on Unix.
            @lock = new FileStream(endpoint.LockPath!, FileMode.OpenOrCreate, FileAccess.ReadWrite, FileShare.None);
        }
        catch (IOException)
        {
            return null;
        }
        var socket = new Socket(AddressFamily.Unix, SocketType.Stream, ProtocolType.Unspecified);
        try
        {
            // A socket file left by a server that died; the lock says nobody serves it.
            File.Delete(endpoint.Address);
            socket.Bind(new UnixDomainSocketEndPoint(endpoint.Address));
            socket.Listen(64);
            return new SocketListener(@lock, socket) { Endpoint = endpoint };
        }
        catch
        {
            socket.Dispose();
            @lock.Dispose();
            throw;
        }
    }

    public override async Task<Stream> AcceptAsync(CancellationToken cancellationToken)
    {
        var connection = await _socket.AcceptAsync(cancellationToken).ConfigureAwait(false);
        return new NetworkStream(connection, ownsSocket: true);
    }

    public override void Dispose()
    {
        if (_disposed)
        {
            // Once the lock is released, the path may be another server's socket.
            return;
        }
        _disposed = true;
        _socket.Dispose();
        try
        {
            // Removed while the lock is still held, so it is never another server's socket. The lock file stays: removing
            // it would let two servers lock two different files of the same name.
            File.Delete(Endpoint.Address);
        }
        catch (Exception ex) when (ex is IOException or UnauthorizedAccessException)
        {
        }
        _lock.Dispose();
    }
}
