using System.Collections;
using System.Reflection;
using System.Reflection.Metadata;
using System.Reflection.PortableExecutable;
using System.Runtime.InteropServices;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using Warrant.Engine;
using Warrant.Engine.Service;

/// <summary>Why the CLI cannot use a verification server; the build then verifies in-process and logs the reason (M5b KTD5).</summary>
/// <param name="reason">The reason, as the fallback message words it.</param>
/// <param name="inner">The exception behind it, if any.</param>
internal sealed class ServerUnavailableException(string reason, Exception? inner = null) : Exception(reason, inner);

/// <summary>
/// How the CLI finds, starts and talks to a verification server. The defaults are a build's; tests replace the endpoint
/// name, the per-user directory and the server's environment, so each test has a server of its own (M5b KTD29).
/// </summary>
internal sealed record ServerSettings
{
    /// <summary>The endpoint's name, overriding <see cref="ServerEndpoint.EnvironmentVariable"/>; null for the computed one.</summary>
    public string? EndpointName { get; init; }

    /// <summary>The per-user directory that holds a copy of the server's files per toolchain (KTD4).</summary>
    public string CopyRoot { get; init; } = ServerLauncher.DefaultCopyRoot();

    /// <summary>Where the server's files are copied from: beside <c>warrant.dll</c>.</summary>
    public string SourceDirectory { get; init; } = TranslateCommand.AppDirectory();

    /// <summary>Environment variables set for a server the CLI starts, on top of the CLI's own.</summary>
    public IReadOnlyDictionary<string, string> ServerEnvironment { get; init; } = new Dictionary<string, string>();

    /// <summary>How long the CLI waits for a server it started: its connection and its <c>hello</c> (KTD4).</summary>
    public TimeSpan StartTimeout { get; init; } = TimeSpan.FromSeconds(20);

    /// <summary>How long the CLI waits to connect to a server that is already running (KTD4).</summary>
    public TimeSpan ConnectTimeout { get; init; } = TimeSpan.FromSeconds(5);

    /// <summary>
    /// The service the in-process path uses instead of loading the bundle again; tests share one across runs. Null for a
    /// service of the run's own.
    /// </summary>
    public VerificationService? InProcessService { get; init; }

    /// <summary>The endpoint of the server whose files are in <paramref name="serverDirectory"/>.</summary>
    /// <exception cref="ArgumentException">The name is not a plain file name.</exception>
    public ServerEndpoint Endpoint(string serverDirectory) =>
        EndpointName is { } name ? ServerEndpoint.Named(name) : ServerEndpoint.For(serverDirectory);
}

/// <summary>
/// Starts a verification server detached from the CLI (M5b KTD4, docs/m5b/01), so that cancelling a build cannot kill it
/// and MSBuild never waits for it: on Windows through <c>CreateProcess</c> with no inherited handles, outside the CLI's
/// console, process group and (when allowed) job; on Unix through <c>posix_spawn</c> in a new session with the standard
/// streams on <c>/dev/null</c>. The server runs from a per-user copy of its files, so it never holds the package folder
/// or a repository's <c>bin/</c>, which a restore or a rebuild must overwrite.
/// </summary>
internal static class ServerLauncher
{
    /// <summary>The server's assembly.</summary>
    public const string ServerAssembly = "warrant-server.dll";

    /// <summary>
    /// The per-user root of the server copies: <c>%LOCALAPPDATA%\warrant\servers</c> on Windows,
    /// <c>$XDG_STATE_HOME/warrant/servers</c> (by default <c>~/.local/state/warrant/servers</c>) elsewhere, beside the
    /// server's log.
    /// </summary>
    public static string DefaultCopyRoot() => Path.Combine(ServerEndpoint.StateDirectory(), "servers");

    /// <summary>
    /// The directory a server for this toolchain runs from: under <see cref="ServerSettings.CopyRoot"/>, named by a hash of
    /// the toolchain identity (KTD9), the server assembly's module version ID and the bundle's and sidecar's SHA-256, so a
    /// copy is never shared by servers that would answer differently. Nothing is copied yet.
    /// </summary>
    /// <param name="settings">The settings.</param>
    /// <param name="hashes">The SHA-256 of the bundle and sidecar the server is to load.</param>
    /// <returns>The directory.</returns>
    /// <exception cref="ServerUnavailableException">The server's assembly is not beside the CLI.</exception>
    public static string CopyDirectory(ServerSettings settings, BundleHashes hashes)
    {
        var source = Path.Combine(settings.SourceDirectory, ServerAssembly);
        Guid mvid;
        try
        {
            using var pe = new PEReader(File.OpenRead(source));
            var metadata = pe.GetMetadataReader();
            mvid = metadata.GetGuid(metadata.GetModuleDefinition().Mvid);
        }
        catch (Exception ex) when (ex is IOException or UnauthorizedAccessException or BadImageFormatException or InvalidOperationException)
        {
            throw new ServerUnavailableException($"the server '{source}' could not be read: {ex.Message}", ex);
        }
        var hash = SHA256.HashData(Encoding.UTF8.GetBytes($"{Toolchain.Identity}|{mvid:N}|{hashes.Bundle}|{hashes.Sidecar}"));
        return Path.Combine(settings.CopyRoot, Convert.ToHexStringLower(hash)[..32]);
    }

    /// <summary>
    /// Makes sure the copy exists, then starts the server from it, detached. The copy is made once, under a temporary
    /// name, and renamed into place, so a server never starts from a half-copied directory; a CLI that loses the rename
    /// race uses the winner's copy.
    /// </summary>
    /// <remarks>
    /// The CLI does not start the server itself: it starts <c>warrant server launch</c>, which starts the server and exits
    /// at once. A build that is cancelled kills the CLI's process tree, found through each process's parent, and the
    /// operating system keeps naming a detached child's parent; with the launcher gone, the server's parent is a process
    /// that no longer exists, so the kill cannot reach it (KTD4).
    /// </remarks>
    /// <param name="settings">The settings.</param>
    /// <param name="directory">The copy's directory, from <see cref="CopyDirectory"/>.</param>
    /// <param name="bundlePath">The semantics bundle the server is to load.</param>
    /// <param name="sidecarPath">The attribute sidecar made for it.</param>
    /// <exception cref="ServerUnavailableException">The copy could not be made or the launcher could not be started.</exception>
    public static void Start(ServerSettings settings, string directory, string bundlePath, string sidecarPath)
    {
        try
        {
            EnsureCopy(settings.SourceDirectory, directory, bundlePath, sidecarPath);
        }
        catch (Exception ex) when (ex is IOException or UnauthorizedAccessException or JsonException or KeyNotFoundException or InvalidOperationException)
        {
            throw new ServerUnavailableException($"the server's files could not be copied to '{directory}': {ex.Message}", ex);
        }
        var environment = CurrentEnvironment();
        if (settings.EndpointName is { } name)
        {
            environment[ServerEndpoint.EnvironmentVariable] = name;
        }
        foreach (var (key, value) in settings.ServerEnvironment)
        {
            environment[key] = value;
        }
        var host = DotnetHost();
        var cli = typeof(ServerLauncher).Assembly.Location;
        Spawn(host, [host, cli, "server", LaunchVerb, directory], environment, directory);
    }

    /// <summary>The hidden <c>warrant server</c> verb that <see cref="Start"/> runs to start the server.</summary>
    public const string LaunchVerb = "launch";

    /// <summary>
    /// <c>warrant server launch &lt;directory&gt;</c>: starts the server in the copy <paramref name="directory"/>, detached,
    /// with this process's environment, which <see cref="Start"/> set; the caller then exits.
    /// </summary>
    /// <param name="directory">The copy's directory.</param>
    /// <exception cref="ServerUnavailableException">The server could not be started.</exception>
    public static void Launch(string directory)
    {
        var host = DotnetHost();
        Spawn(host, [host, Path.Combine(directory, ServerAssembly)], CurrentEnvironment(), directory);
    }

    private static Dictionary<string, string> CurrentEnvironment() =>
        Environment.GetEnvironmentVariables().Cast<DictionaryEntry>()
            .ToDictionary(e => (string)e.Key, e => (string?)e.Value ?? "", OperatingSystem.IsWindows() ? StringComparer.OrdinalIgnoreCase : StringComparer.Ordinal);

    private static void Spawn(string host, IReadOnlyList<string> arguments, IReadOnlyDictionary<string, string> environment, string directory)
    {
        if (OperatingSystem.IsWindows())
        {
            Windows.Spawn(host, arguments, environment, directory);
        }
        else
        {
            Unix.Spawn(host, arguments, environment);
        }
    }

    /// <summary>
    /// The <c>dotnet</c> host: <c>DOTNET_HOST_PATH</c> when it names a file (the SDK sets it for tools a build runs), else
    /// this process's own host when it is <c>dotnet</c>, else the one that owns the running runtime.
    /// </summary>
    private static string DotnetHost()
    {
        var name = OperatingSystem.IsWindows() ? "dotnet.exe" : "dotnet";
        if (Environment.GetEnvironmentVariable("DOTNET_HOST_PATH") is { Length: > 0 } hostPath && File.Exists(hostPath))
        {
            return hostPath;
        }
        if (Environment.ProcessPath is { } process && string.Equals(Path.GetFileName(process), name, StringComparison.OrdinalIgnoreCase))
        {
            return process;
        }
        // <root>/shared/Microsoft.NETCore.App/<version>/ holds the runtime; <root>/dotnet is its host.
        var root = Path.GetFullPath(Path.Combine(RuntimeEnvironment.GetRuntimeDirectory(), "..", "..", ".."));
        var candidate = Path.Combine(root, name);
        if (File.Exists(candidate))
        {
            return candidate;
        }
        throw new ServerUnavailableException("the dotnet host was not found to start the server");
    }

    private static void EnsureCopy(string sourceDirectory, string directory, string bundlePath, string sidecarPath)
    {
        if (File.Exists(Path.Combine(directory, ServerAssembly)))
        {
            return;
        }
        var files = ServerFiles(sourceDirectory);
        var temporary = directory + ".tmp-" + Guid.NewGuid().ToString("N")[..8];
        try
        {
            foreach (var (file, optional) in files)
            {
                var source = Path.Combine(sourceDirectory, file);
                if (optional && !File.Exists(source))
                {
                    continue;
                }
                var target = Path.Combine(temporary, file);
                Directory.CreateDirectory(Path.GetDirectoryName(target)!);
                File.Copy(source, target);
            }
            File.Copy(bundlePath, Path.Combine(temporary, SemanticsBundle.FileName));
            File.Copy(sidecarPath, Path.Combine(temporary, VerifyCommand.SidecarFileName));
            try
            {
                Directory.Move(temporary, directory);
            }
            catch (IOException) when (File.Exists(Path.Combine(directory, ServerAssembly)))
            {
                // Another CLI renamed its copy into place first; the copies are identical.
            }
        }
        finally
        {
            if (Directory.Exists(temporary))
            {
                Directory.Delete(temporary, recursive: true);
            }
        }
    }

    /// <summary>
    /// The server's files, relative to the CLI's directory: its assembly, its <c>deps.json</c> and <c>runtimeconfig.json</c>,
    /// and every runtime and resource assembly its <c>deps.json</c> names, where the host looks for them beside the app.
    /// Resource (satellite) assemblies are optional: only messages in other languages need them.
    /// </summary>
    private static List<(string File, bool Optional)> ServerFiles(string sourceDirectory)
    {
        const string name = "warrant-server";
        var files = new List<(string File, bool Optional)> { (name + ".dll", false), (name + ".deps.json", false), (name + ".runtimeconfig.json", false) };
        using var deps = JsonDocument.Parse(File.ReadAllBytes(Path.Combine(sourceDirectory, name + ".deps.json")));
        var target = deps.RootElement.GetProperty("runtimeTarget").GetProperty("name").GetString()
            ?? throw new InvalidOperationException("the server's deps.json names no runtime target");
        foreach (var library in deps.RootElement.GetProperty("targets").GetProperty(target).EnumerateObject())
        {
            if (library.Value.TryGetProperty("runtime", out var runtime))
            {
                files.AddRange(runtime.EnumerateObject().Select(asset => (Path.GetFileName(asset.Name), false)));
            }
            if (library.Value.TryGetProperty("resources", out var resources))
            {
                files.AddRange(resources.EnumerateObject().Select(asset =>
                    (Path.Combine(asset.Value.GetProperty("locale").GetString() ?? "", Path.GetFileName(asset.Name)), true)));
            }
        }
        return [.. files.DistinctBy(f => f.File, StringComparer.Ordinal)];
    }

    /// <summary><c>CreateProcess</c>, which .NET 10's <see cref="System.Diagnostics.Process"/> cannot call with these flags.</summary>
    private static class Windows
    {
        private const uint DetachedProcess = 0x00000008;
        private const uint CreateNewProcessGroup = 0x00000200;
        private const uint CreateUnicodeEnvironment = 0x00000400;
        private const uint CreateBreakawayFromJob = 0x01000000;
        private const uint CreateNoWindow = 0x08000000;
        private const int ErrorAccessDenied = 5;

        public static void Spawn(string program, IReadOnlyList<string> arguments, IReadOnlyDictionary<string, string> environment, string workingDirectory)
        {
            var commandLine = (string.Join(' ', arguments.Select(Quote)) + "\0").ToCharArray();
            // A Unicode environment block: NAME=value entries, each NUL-terminated, sorted by name, then one more NUL.
            var block = string.Concat(environment.OrderBy(e => e.Key, StringComparer.OrdinalIgnoreCase).Select(e => $"{e.Key}={e.Value}\0")) + "\0";
            var environmentBlock = Marshal.StringToHGlobalUni(block);
            try
            {
                var flags = CreateNoWindow | DetachedProcess | CreateNewProcessGroup | CreateUnicodeEnvironment;
                if (!TryCreate(flags | CreateBreakawayFromJob, out var info, out int error))
                {
                    // The CLI's job forbids breakaway: the server then lives as long as the job, which is all a build allows.
                    if (error != ErrorAccessDenied || !TryCreate(flags, out info, out error))
                    {
                        throw new ServerUnavailableException($"the server could not be started: CreateProcess failed with error {error}");
                    }
                }
                CloseHandle(info.Thread);
                CloseHandle(info.Process);
            }
            finally
            {
                Marshal.FreeHGlobal(environmentBlock);
            }

            bool TryCreate(uint creationFlags, out ProcessInformation info, out int error)
            {
                var startup = new StartupInfo { Size = Marshal.SizeOf<StartupInfo>() };
                var line = (char[])commandLine.Clone();
                bool created = CreateProcessW(program, line, IntPtr.Zero, IntPtr.Zero, inheritHandles: false, creationFlags, environmentBlock, workingDirectory, ref startup, out info);
                error = created ? 0 : Marshal.GetLastWin32Error();
                return created;
            }
        }

        /// <summary>An argument quoted for the C runtime's parser; the paths here hold no quotes.</summary>
        private static string Quote(string argument) => argument.Contains(' ', StringComparison.Ordinal) || argument.Length == 0 ? $"\"{argument}\"" : argument;

        [DllImport("kernel32.dll", CharSet = CharSet.Unicode, SetLastError = true)]
        [DefaultDllImportSearchPaths(DllImportSearchPath.System32)]
        [return: MarshalAs(UnmanagedType.Bool)]
        private static extern bool CreateProcessW(
            string applicationName,
            [In, Out] char[] commandLine,
            IntPtr processAttributes,
            IntPtr threadAttributes,
            [MarshalAs(UnmanagedType.Bool)] bool inheritHandles,
            uint creationFlags,
            IntPtr environment,
            string currentDirectory,
            ref StartupInfo startupInfo,
            out ProcessInformation processInformation);

        [DllImport("kernel32.dll", SetLastError = true)]
        [DefaultDllImportSearchPaths(DllImportSearchPath.System32)]
        [return: MarshalAs(UnmanagedType.Bool)]
        private static extern bool CloseHandle(IntPtr handle);

        [StructLayout(LayoutKind.Sequential)]
        private struct StartupInfo
        {
            public int Size;
            public IntPtr Reserved;
            public IntPtr Desktop;
            public IntPtr Title;
            public int X;
            public int Y;
            public int XSize;
            public int YSize;
            public int XCountChars;
            public int YCountChars;
            public int FillAttribute;
            public int Flags;
            public short ShowWindow;
            public short Reserved2Size;
            public IntPtr Reserved2;
            public IntPtr StdInput;
            public IntPtr StdOutput;
            public IntPtr StdError;
        }

        [StructLayout(LayoutKind.Sequential)]
        private struct ProcessInformation
        {
            public IntPtr Process;
            public IntPtr Thread;
            public int ProcessId;
            public int ThreadId;
        }
    }

    /// <summary><c>posix_spawn</c> with <c>POSIX_SPAWN_SETSID</c> (glibc 2.26 and later, macOS), from the C library.</summary>
    private static class Unix
    {
        private const string LibC = "libc";
        private const int ReadWrite = 2; // O_RDWR

        /// <summary>Generous room for <c>posix_spawnattr_t</c> and <c>posix_spawn_file_actions_t</c> (336 and 80 bytes on glibc x64; a pointer on macOS).</summary>
        private const int OpaqueSize = 1024;

        static Unix() => NativeLibrary.SetDllImportResolver(typeof(Unix).Assembly, Resolve);

        /// <summary>The C library: <c>libc.so.6</c> on Linux, where a bare <c>libc.so</c> may be a linker script.</summary>
        private static IntPtr Resolve(string library, Assembly assembly, DllImportSearchPath? searchPath) =>
            library == LibC && OperatingSystem.IsLinux() && NativeLibrary.TryLoad("libc.so.6", out var handle) ? handle : IntPtr.Zero;

        public static void Spawn(string program, IReadOnlyList<string> arguments, IReadOnlyDictionary<string, string> environment)
        {
            short setSid = (short)(OperatingSystem.IsMacOS() ? 0x0400 : 0x80);
            var allocated = new List<IntPtr>();
            IntPtr attributes = Allocate(allocated), actions = Allocate(allocated);
            bool attributesReady = false, actionsReady = false;
            try
            {
                Check(posix_spawnattr_init(attributes), "posix_spawnattr_init");
                attributesReady = true;
                Check(posix_spawnattr_setflags(attributes, setSid), "posix_spawnattr_setflags");
                Check(posix_spawn_file_actions_init(actions), "posix_spawn_file_actions_init");
                actionsReady = true;
                for (int fd = 0; fd <= 2; fd++)
                {
                    Check(posix_spawn_file_actions_addopen(actions, fd, CString("/dev/null"), ReadWrite, 0), "posix_spawn_file_actions_addopen");
                }
                var argv = Strings(arguments, allocated);
                var envp = Strings([.. environment.Select(e => $"{e.Key}={e.Value}")], allocated);
                Check(posix_spawn(out _, CString(program), actions, attributes, argv, envp), "posix_spawn");
            }
            finally
            {
                if (actionsReady)
                {
                    _ = posix_spawn_file_actions_destroy(actions);
                }
                if (attributesReady)
                {
                    _ = posix_spawnattr_destroy(attributes);
                }
                foreach (var pointer in allocated)
                {
                    Marshal.FreeHGlobal(pointer);
                }
            }
        }

        private static IntPtr Allocate(List<IntPtr> allocated)
        {
            var pointer = Marshal.AllocHGlobal(OpaqueSize);
            allocated.Add(pointer);
            Marshal.Copy(new byte[OpaqueSize], 0, pointer, OpaqueSize);
            return pointer;
        }

        /// <summary>A NUL-terminated UTF-8 string.</summary>
        private static byte[] CString(string value) => Encoding.UTF8.GetBytes(value + "\0");

        /// <summary>A NULL-terminated array of NUL-terminated UTF-8 strings.</summary>
        private static IntPtr[] Strings(IReadOnlyList<string> values, List<IntPtr> allocated)
        {
            var result = new IntPtr[values.Count + 1];
            for (int i = 0; i < values.Count; i++)
            {
                var bytes = CString(values[i]);
                result[i] = Marshal.AllocHGlobal(bytes.Length);
                allocated.Add(result[i]);
                Marshal.Copy(bytes, 0, result[i], bytes.Length);
            }
            return result;
        }

        private static void Check(int result, string call)
        {
            if (result != 0)
            {
                throw new ServerUnavailableException($"the server could not be started: {call} failed with error {result}");
            }
        }

        [DllImport(LibC)]
        [DefaultDllImportSearchPaths(DllImportSearchPath.SafeDirectories)]
        private static extern int posix_spawnattr_init(IntPtr attributes);

        [DllImport(LibC)]
        [DefaultDllImportSearchPaths(DllImportSearchPath.SafeDirectories)]
        private static extern int posix_spawnattr_setflags(IntPtr attributes, short flags);

        [DllImport(LibC)]
        [DefaultDllImportSearchPaths(DllImportSearchPath.SafeDirectories)]
        private static extern int posix_spawnattr_destroy(IntPtr attributes);

        [DllImport(LibC)]
        [DefaultDllImportSearchPaths(DllImportSearchPath.SafeDirectories)]
        private static extern int posix_spawn_file_actions_init(IntPtr actions);

        [DllImport(LibC)]
        [DefaultDllImportSearchPaths(DllImportSearchPath.SafeDirectories)]
        private static extern int posix_spawn_file_actions_addopen(
            IntPtr actions, int fd, byte[] path, int flags, int mode);

        [DllImport(LibC)]
        [DefaultDllImportSearchPaths(DllImportSearchPath.SafeDirectories)]
        private static extern int posix_spawn_file_actions_destroy(IntPtr actions);

        [DllImport(LibC)]
        [DefaultDllImportSearchPaths(DllImportSearchPath.SafeDirectories)]
        private static extern int posix_spawn(
            out int pid, byte[] path, IntPtr actions, IntPtr attributes, IntPtr[] argv, IntPtr[] envp);
    }
}
