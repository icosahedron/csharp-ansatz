using System.Globalization;
using System.Text;

namespace Warrant.Server;

/// <summary>
/// The server's size-capped log (M5b KTD4): a detached process has nowhere else to say why it started, refused or
/// stopped. Every server of the user appends to one file, a line at a time; when the file passes
/// <see cref="MaxBytes"/> it becomes <c>server.log.1</c>, replacing the previous one.
/// </summary>
internal sealed class ServerLog
{
    /// <summary>The size at which the log is rotated.</summary>
    public const long DefaultMaxBytes = 4 * 1024 * 1024;

    private readonly Lock _lock = new();

    /// <summary>A log at <paramref name="path"/>, rotated at <paramref name="maxBytes"/>.</summary>
    /// <param name="path">The log file.</param>
    /// <param name="maxBytes">The size at which it is rotated.</param>
    public ServerLog(string path, long maxBytes = DefaultMaxBytes)
    {
        ArgumentNullException.ThrowIfNull(path);
        ArgumentOutOfRangeException.ThrowIfLessThan(maxBytes, 1);
        Path = path;
        MaxBytes = maxBytes;
    }

    /// <summary>The log file.</summary>
    public string Path { get; }

    /// <summary>The size at which the log is rotated.</summary>
    public long MaxBytes { get; }

    /// <summary>
    /// The user's log: <c>%LOCALAPPDATA%\warrant\server.log</c> on Windows, <c>$XDG_STATE_HOME/warrant/server.log</c>
    /// (by default <c>~/.local/state/warrant/server.log</c>) elsewhere.
    /// </summary>
    /// <returns>The path.</returns>
    public static string DefaultPath()
    {
        string directory;
        if (OperatingSystem.IsWindows())
        {
            directory = Environment.GetFolderPath(Environment.SpecialFolder.LocalApplicationData);
        }
        else
        {
            directory = Environment.GetEnvironmentVariable("XDG_STATE_HOME") is { Length: > 0 } state
                ? state
                : System.IO.Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.UserProfile), ".local", "state");
        }
        return System.IO.Path.Combine(directory, "warrant", "server.log");
    }

    /// <summary>Appends a line with the time and the process id; a log that cannot be written is ignored.</summary>
    /// <param name="message">The line.</param>
    public void Write(string message)
    {
        ArgumentNullException.ThrowIfNull(message);
        var line = string.Create(CultureInfo.InvariantCulture, $"{DateTimeOffset.UtcNow:yyyy-MM-ddTHH:mm:ss.fffZ} [{Environment.ProcessId}] {message}{Environment.NewLine}");
        lock (_lock)
        {
            try
            {
                Directory.CreateDirectory(System.IO.Path.GetDirectoryName(Path)!);
                var file = new FileInfo(Path);
                if (file.Exists && file.Length >= MaxBytes)
                {
                    File.Move(Path, Path + ".1", overwrite: true);
                }
                using var stream = new FileStream(Path, FileMode.Append, FileAccess.Write, FileShare.ReadWrite | FileShare.Delete);
                var bytes = Encoding.UTF8.GetBytes(line);
                stream.Write(bytes);
            }
            catch (Exception ex) when (ex is IOException or UnauthorizedAccessException)
            {
                // The log is a diagnostic aid: a server that cannot write it still serves.
            }
        }
    }
}
