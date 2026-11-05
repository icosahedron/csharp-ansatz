namespace Warrant.Build.Tests;

using System.Runtime.InteropServices;
using System.Text;

/// <summary>
/// A project directory with a scripted run of <c>fake-warrant.dll</c> (tests/Warrant.Build.FakeCli), which replays
/// <c>fake-cli/stdout.txt</c>, <c>stderr.txt</c> and <c>exitcode.txt</c> and records its arguments.
/// </summary>
internal sealed class FakeCli : IDisposable
{
    private static readonly Encoding Utf8 = new UTF8Encoding(encoderShouldEmitUTF8Identifier: false);

    public FakeCli(string? projectDirectory = null)
    {
        ProjectDirectory = projectDirectory ?? Path.Combine(Path.GetTempPath(), "wrt-build-" + Guid.NewGuid().ToString("N")[..8]);
        Directory.CreateDirectory(ScriptDirectory);
    }

    /// <summary>The fake CLI, built beside the tests.</summary>
    public static string CliPath { get; } = Path.Combine(AppContext.BaseDirectory, "fake-warrant.dll");

    /// <summary>The <c>dotnet</c> host the tests launch the fake with.</summary>
    public static string DotnetHost { get; } = FindDotnet();

    public string ProjectDirectory { get; }

    private string ScriptDirectory => Path.Combine(ProjectDirectory, "fake-cli");

    /// <summary>Scripts the next run: its output lines (LF-terminated, UTF-8), error lines and exit code.</summary>
    public void Script(IEnumerable<string> stdout, int exitCode, IEnumerable<string>? stderr = null)
    {
        File.WriteAllText(Path.Combine(ScriptDirectory, "stdout.txt"), Lines(stdout), Utf8);
        File.WriteAllText(Path.Combine(ScriptDirectory, "stderr.txt"), Lines(stderr ?? []), Utf8);
        File.WriteAllText(Path.Combine(ScriptDirectory, "exitcode.txt"), exitCode.ToString(System.Globalization.CultureInfo.InvariantCulture));
    }

    /// <summary>The arguments of each run so far, in order.</summary>
    public IReadOnlyList<string[]> Invocations()
    {
        var runs = new List<string[]>();
        for (var n = 1; File.Exists(Path.Combine(ScriptDirectory, $"invocation-{n}.txt")); n++)
        {
            runs.Add(File.ReadAllLines(Path.Combine(ScriptDirectory, $"invocation-{n}.txt")));
        }

        return runs;
    }

    public void Dispose()
    {
        try
        {
            Directory.Delete(ProjectDirectory, recursive: true);
        }
        catch (IOException)
        {
            // A temp directory left behind is harmless.
        }
    }

    private static string Lines(IEnumerable<string> lines) => string.Concat(lines.Select(l => l + "\n"));

    private static string FindDotnet()
    {
        var host = Environment.GetEnvironmentVariable("DOTNET_HOST_PATH");
        if (!string.IsNullOrEmpty(host) && File.Exists(host))
        {
            return host;
        }

        var name = RuntimeInformation.IsOSPlatform(OSPlatform.Windows) ? "dotnet.exe" : "dotnet";
        return (Environment.GetEnvironmentVariable("PATH") ?? "")
            .Split(Path.PathSeparator, StringSplitOptions.RemoveEmptyEntries)
            .Select(d => Path.Combine(d, name))
            .FirstOrDefault(File.Exists)
            ?? throw new InvalidOperationException("dotnet is neither in DOTNET_HOST_PATH nor on the path");
    }
}
