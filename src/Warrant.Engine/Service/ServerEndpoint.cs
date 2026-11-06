using System.Runtime.InteropServices;
using System.Security.Cryptography;
using System.Text;

namespace Warrant.Engine.Service;

/// <summary>
/// Where a verification server listens (M5b KTD3, docs/m5b/01). A client computes the endpoint; it never asks anyone
/// where the server is. The name hashes the user, the elevation, the server's directory and the toolchain identity, so
/// a rebuilt or upgraded Warrant gets its own server. On Windows the endpoint is a named pipe of that name; elsewhere it
/// is a Unix domain socket in a directory only the user can enter, which the server and the client both check.
/// </summary>
/// <param name="Name">The endpoint's name.</param>
/// <param name="Address">The pipe name on Windows; the socket's path elsewhere.</param>
/// <param name="SocketDirectory">The socket's directory; null on Windows.</param>
public sealed record ServerEndpoint(string Name, string Address, string? SocketDirectory)
{
    /// <summary>
    /// The environment variable that replaces the computed name: tests set it, and the CLI sets it for a server it starts, so
    /// both use the name the CLI computed. The directory checks still apply.
    /// </summary>
    public const string EnvironmentVariable = "WARRANT_SERVER_ENDPOINT";

    /// <summary>The number of characters of the hash a name keeps: short enough for macOS's 104-byte socket paths.</summary>
    public const int NameLength = 24;

    private const int OwnerOnly = 0x1C0; // 0700

    /// <summary>The lock file that keeps one server per name on Unix; null on Windows, where the pipe itself does.</summary>
    public string? LockPath => SocketDirectory is null ? null : Path.Combine(SocketDirectory, Name + ".lock");

    /// <summary>
    /// The endpoint of the server whose files are in <paramref name="serverDirectory"/>, for the current user and
    /// elevation: <see cref="EnvironmentVariable"/>'s name when it is set, otherwise the hash of KTD3.
    /// </summary>
    /// <param name="serverDirectory">The directory the server runs from.</param>
    /// <returns>The endpoint.</returns>
    /// <exception cref="ArgumentException"><see cref="EnvironmentVariable"/> holds a name that is not a plain file name.</exception>
    public static ServerEndpoint For(string serverDirectory)
    {
        ArgumentNullException.ThrowIfNull(serverDirectory);
        var name = Environment.GetEnvironmentVariable(EnvironmentVariable) is { Length: > 0 } overridden
            ? overridden
            : NameFor(Environment.UserName, Environment.IsPrivilegedProcess, serverDirectory, Toolchain.Identity);
        return Named(name);
    }

    /// <summary>The endpoint of a given name, in <see cref="DefaultSocketDirectory"/> on Unix.</summary>
    /// <param name="name">The name.</param>
    /// <returns>The endpoint.</returns>
    /// <exception cref="ArgumentException">The name is empty or not a plain file name.</exception>
    public static ServerEndpoint Named(string name) => Named(name, OperatingSystem.IsWindows() ? null : DefaultSocketDirectory());

    /// <summary>The endpoint of a given name: a pipe when <paramref name="socketDirectory"/> is null, else a socket in it.</summary>
    /// <param name="name">The name.</param>
    /// <param name="socketDirectory">The socket's directory; null for a named pipe.</param>
    /// <returns>The endpoint.</returns>
    /// <exception cref="ArgumentException">The name is empty or not a plain file name.</exception>
    public static ServerEndpoint Named(string name, string? socketDirectory)
    {
        ArgumentException.ThrowIfNullOrEmpty(name);
        // A name that leaves the checked directory would escape KTD3's checks.
        if (name.IndexOfAny(['/', '\\']) >= 0 || name is "." or "..")
        {
            throw new ArgumentException($"The endpoint name '{name}' is not a plain file name.", nameof(name));
        }
        return socketDirectory is null
            ? new ServerEndpoint(name, name, null)
            : new ServerEndpoint(name, Path.Combine(socketDirectory, name + ".sock"), socketDirectory);
    }

    /// <summary>The first <see cref="NameLength"/> characters of base64url(SHA-256(user | elevation | directory | identity)).</summary>
    /// <param name="user">The user's name.</param>
    /// <param name="elevated">Whether the process is elevated (administrator or root).</param>
    /// <param name="serverDirectory">The directory the server runs from, made absolute and without a trailing separator.</param>
    /// <param name="toolchainIdentity">The toolchain identity.</param>
    /// <returns>The name.</returns>
    public static string NameFor(string user, bool elevated, string serverDirectory, string toolchainIdentity)
    {
        ArgumentNullException.ThrowIfNull(user);
        ArgumentNullException.ThrowIfNull(serverDirectory);
        ArgumentNullException.ThrowIfNull(toolchainIdentity);
        var directory = Path.TrimEndingDirectorySeparator(Path.GetFullPath(serverDirectory));
        var hash = SHA256.HashData(Encoding.UTF8.GetBytes($"{user}|{(elevated ? "elevated" : "normal")}|{directory}|{toolchainIdentity}"));
        return System.Buffers.Text.Base64Url.EncodeToString(hash)[..NameLength];
    }

    /// <summary>
    /// The user's Warrant state directory, which holds the server's log and its per-toolchain copies:
    /// <c>%LOCALAPPDATA%\warrant</c> on Windows, <c>$XDG_STATE_HOME/warrant</c> (by default
    /// <c>~/.local/state/warrant</c>) elsewhere.
    /// </summary>
    /// <returns>The directory.</returns>
    public static string StateDirectory()
    {
        string directory = OperatingSystem.IsWindows()
            ? Environment.GetFolderPath(Environment.SpecialFolder.LocalApplicationData)
            : Environment.GetEnvironmentVariable("XDG_STATE_HOME") is { Length: > 0 } state
                ? state
                : Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.UserProfile), ".local", "state");
        return Path.Combine(directory, "warrant");
    }

    /// <summary>The current process's effective user id; Unix only.</summary>
    /// <returns>The user id.</returns>
    public static uint EffectiveUserId() => Unix.EffectiveUserId();

    /// <summary>The per-user socket directory on Unix: <c>$XDG_RUNTIME_DIR/warrant</c> when that is set, else <c>/tmp/warrant-&lt;uid&gt;</c>.</summary>
    /// <returns>The directory.</returns>
    public static string DefaultSocketDirectory() =>
        Environment.GetEnvironmentVariable("XDG_RUNTIME_DIR") is { Length: > 0 } runtime
            ? Path.Combine(runtime, "warrant")
            : $"/tmp/warrant-{Unix.EffectiveUserId()}";

    /// <summary>
    /// Creates the socket directory with mode 0700 when it does not exist, then checks it as <see cref="CheckDirectory"/> does.
    /// </summary>
    /// <param name="directory">The directory.</param>
    /// <param name="problem">Why the directory cannot be used; null when it can.</param>
    /// <returns>Whether the directory can be used.</returns>
    public static bool TryPrepareDirectory(string directory, out string? problem)
    {
        ArgumentNullException.ThrowIfNull(directory);
        if (OperatingSystem.IsWindows())
        {
            problem = null;
            return true;
        }
        if (Unix.LStat(directory) is null)
        {
            try
            {
                Directory.CreateDirectory(directory, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
            }
            catch (Exception ex) when (ex is IOException or UnauthorizedAccessException)
            {
                problem = $"the socket directory '{directory}' could not be created: {ex.Message}";
                return false;
            }
        }
        return CheckDirectory(directory, out problem);
    }

    /// <summary>
    /// Whether a socket directory is safe (KTD3): <c>lstat</c> finds a real directory, not a link, owned by the current
    /// user, with mode 0700. Another local user could otherwise own the predictable path and answer every request.
    /// Always true on Windows, where the pipe's <c>CurrentUserOnly</c> does this job.
    /// </summary>
    /// <param name="directory">The directory.</param>
    /// <param name="problem">Why it is not safe; null when it is.</param>
    /// <returns>Whether it is safe.</returns>
    public static bool CheckDirectory(string directory, out string? problem)
    {
        ArgumentNullException.ThrowIfNull(directory);
        problem = null;
        if (OperatingSystem.IsWindows())
        {
            return true;
        }
        var status = Unix.LStat(directory);
        uint user = Unix.EffectiveUserId();
        if (status is not { } s)
        {
            problem = $"the socket directory '{directory}' does not exist";
        }
        else if (!s.IsDirectory)
        {
            problem = $"the socket directory '{directory}' is not a directory (a link or another file)";
        }
        else if (s.Uid != user)
        {
            problem = $"the socket directory '{directory}' is owned by user {s.Uid}, not {user}";
        }
        else if (s.Permissions != OwnerOnly)
        {
            problem = $"the socket directory '{directory}' has mode {Convert.ToString(s.Permissions, 8)}, not 700";
        }
        return problem is null;
    }

    /// <summary>The few POSIX calls .NET has no managed API for, through the runtime's own System.Native shim.</summary>
    private static class Unix
    {
        private const string SystemNative = "libSystem.Native";

        /// <summary>The current process's effective user id.</summary>
        public static uint EffectiveUserId() => GetEUid();

        /// <summary><c>lstat</c> of a path: null when it does not exist or cannot be read.</summary>
        public static Status? LStat(string path)
        {
            var buffer = new FileStatusPrefix();
            // A NUL-terminated UTF-8 path, as System.Native takes it.
            var bytes = Encoding.UTF8.GetBytes(path + "\0");
            return LStat(bytes, ref buffer) == 0 ? new Status(buffer.Mode, buffer.Uid) : null;
        }

        [DllImport(SystemNative, EntryPoint = "SystemNative_GetEUid")]
        [DefaultDllImportSearchPaths(DllImportSearchPath.SafeDirectories)]
        private static extern uint GetEUid();

        [DllImport(SystemNative, EntryPoint = "SystemNative_LStat")]
        [DefaultDllImportSearchPaths(DllImportSearchPath.SafeDirectories)]
        private static extern int LStat(byte[] path, ref FileStatusPrefix output);

        /// <summary>
        /// System.Native's <c>FileStatus</c>: <c>Flags</c>, <c>Mode</c> (with the file type in <c>S_IFMT</c>) and <c>Uid</c>
        /// lead it; the rest is padding that covers the whole struct, which is about 130 bytes.
        /// </summary>
        [StructLayout(LayoutKind.Explicit, Size = 512)]
        private struct FileStatusPrefix
        {
            [FieldOffset(0)] public int Flags;
            [FieldOffset(4)] public int Mode;
            [FieldOffset(8)] public uint Uid;
        }

        /// <summary>The fields of an <c>lstat</c> the checks need.</summary>
        public readonly record struct Status(int Mode, uint Uid)
        {
            /// <summary>Whether the path is a directory itself, not a link to one.</summary>
            public bool IsDirectory => (Mode & 0xF000) == 0x4000;

            /// <summary>The permission bits.</summary>
            public int Permissions => Mode & 0x1FF;
        }
    }
}
