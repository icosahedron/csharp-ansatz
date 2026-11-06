namespace Warrant.Build.Tests;

using System.Collections.Concurrent;
using System.Diagnostics;
using System.Runtime.InteropServices;
using System.Text;

/// <summary>
/// The three build hosts of the integration matrix (U13): <c>dotnet build</c>, and Visual Studio 2026's and 2022's
/// <c>MSBuild.exe</c>, found with <c>vswhere</c>. A host that cannot be found has a reason instead, which the test
/// reports as its skip reason, so a missing Visual Studio is never counted as a pass.
/// </summary>
internal sealed class BuildHost
{
    public const string Dotnet = "dotnet build";
    public const string VisualStudio2026 = "Visual Studio 2026 MSBuild";
    public const string VisualStudio2022 = "Visual Studio 2022 MSBuild";

    private static readonly ConcurrentDictionary<string, Lazy<(BuildHost? Host, string? Reason)>> Found = new(StringComparer.Ordinal);

    private BuildHost(string name, string? msbuild, string version)
    {
        Name = name;
        MSBuildExe = msbuild;
        Version = version;
    }

    public string Name { get; }

    /// <summary>Visual Studio's <c>MSBuild.exe</c>, or null for <c>dotnet build</c>.</summary>
    public string? MSBuildExe { get; }

    /// <summary>The host's own version: the SDK's MSBuild for <c>dotnet build</c>, <c>MSBuild.exe -version</c> otherwise.</summary>
    public string Version { get; }

    public override string ToString() => $"{Name} {Version}" + (MSBuildExe is null ? "" : $" ({MSBuildExe})");

    /// <summary>The host, or null and why it is not available.</summary>
    public static (BuildHost? Host, string? Reason) Find(string name) =>
        Found.GetOrAdd(name, n => new Lazy<(BuildHost?, string?)>(() => Locate(n))).Value;

    /// <summary>
    /// Runs a build of the project in <paramref name="directory"/> and returns its exit code and its UTF-8 file log at
    /// normal verbosity. Every host restores, and none keeps nodes or the compiler server alive afterwards.
    /// </summary>
    public (int ExitCode, string Log) Build(string directory, params string[] extra) => Build(directory, null, extra);

    /// <summary>
    /// <see cref="Build(string, string[])"/> with <paramref name="environment"/> added to the build's environment, which
    /// the task passes on to the CLI and the CLI to a server it starts.
    /// </summary>
    public (int ExitCode, string Log) Build(string directory, IReadOnlyDictionary<string, string>? environment, params string[] extra)
    {
        var log = Path.Combine(directory, $"build-{Guid.NewGuid():N}.log");
        var start = new ProcessStartInfo(MSBuildExe ?? FakeCli.DotnetHost)
        {
            WorkingDirectory = directory,
            RedirectStandardOutput = true,
            RedirectStandardError = true,
            UseShellExecute = false,
        };
        var args = MSBuildExe is null ? new List<string> { "build" } : ["-restore"];
        args.AddRange(["-nologo", "-nodeReuse:false", "-p:UseSharedCompilation=false", $"-flp:logfile={log};encoding=utf-8;verbosity=normal"]);
        args.AddRange(extra);
        foreach (var arg in args)
        {
            start.ArgumentList.Add(arg);
        }

        Isolate(start, visualStudio: MSBuildExe is not null);
        foreach (var (key, value) in environment ?? new Dictionary<string, string>())
        {
            start.Environment[key] = value;
        }

        var (exitCode, output) = Run(start, TimeSpan.FromMinutes(5));
        return (exitCode, File.Exists(log) ? File.ReadAllText(log, Encoding.UTF8) : output);
    }

    /// <summary>Evaluates one property of the project in <paramref name="directory"/>, as this host resolves it.</summary>
    public string Property(string directory, string property)
    {
        var start = new ProcessStartInfo(MSBuildExe ?? FakeCli.DotnetHost)
        {
            WorkingDirectory = directory,
            RedirectStandardOutput = true,
            RedirectStandardError = true,
            UseShellExecute = false,
        };
        if (MSBuildExe is null)
        {
            start.ArgumentList.Add("msbuild");
        }

        start.ArgumentList.Add("-nologo");
        start.ArgumentList.Add($"-getProperty:{property}");
        Isolate(start, visualStudio: MSBuildExe is not null);
        var (exitCode, output) = Run(start, TimeSpan.FromMinutes(2));
        Assert.True(exitCode == 0, $"evaluating {property} with {Name} failed:\n{output}");
        return output.Trim();
    }

    /// <summary>
    /// Keeps the test host's environment out of the build: <c>dotnet test</c> sets MSBuild variables that point at the
    /// SDK running the tests, and Visual Studio's MSBuild must resolve its own SDK from the sample's global.json.
    /// </summary>
    internal static void Isolate(ProcessStartInfo start, bool visualStudio)
    {
        foreach (var key in start.Environment.Keys.Where(k => k.StartsWith("MSBuild", StringComparison.OrdinalIgnoreCase)).ToList())
        {
            start.Environment.Remove(key);
        }

        if (visualStudio)
        {
            // A developer's prompt has no DOTNET_HOST_PATH unless the host sets it; the task then finds dotnet on the path.
            start.Environment.Remove("DOTNET_HOST_PATH");
        }

        start.Environment["MSBUILDDISABLENODEREUSE"] = "1";
        start.Environment["DOTNET_CLI_USE_MSBUILD_SERVER"] = "0";
        start.Environment["DOTNET_CLI_TELEMETRY_OPTOUT"] = "1";
        start.Environment["DOTNET_NOLOGO"] = "1";
        start.Environment["DOTNET_SKIP_FIRST_TIME_EXPERIENCE"] = "1";
    }

    internal static (int ExitCode, string Output) Run(ProcessStartInfo start, TimeSpan timeout)
    {
        start.StandardOutputEncoding = Encoding.UTF8;
        start.StandardErrorEncoding = Encoding.UTF8;
        using var process = Process.Start(start)!;
        var stdout = process.StandardOutput.ReadToEndAsync();
        var stderr = process.StandardError.ReadToEndAsync();
        if (!process.WaitForExit(timeout))
        {
            process.Kill(entireProcessTree: true);
            Assert.Fail($"{start.FileName} {string.Join(' ', start.ArgumentList)} timed out after {timeout}");
        }

        return (process.ExitCode, stdout.Result + stderr.Result);
    }

    private static (BuildHost?, string?) Locate(string name)
    {
        if (name == Dotnet)
        {
            return (new BuildHost(name, null, "(the SDK the sample's global.json selects)"), null);
        }

        var range = name switch
        {
            VisualStudio2026 => "[18.0,19.0)",
            VisualStudio2022 => "[17.0,18.0)",
            _ => throw new ArgumentException($"unknown host '{name}'", nameof(name)),
        };
        if (!RuntimeInformation.IsOSPlatform(OSPlatform.Windows))
        {
            return (null, $"{name} not run: Visual Studio runs only on Windows");
        }

        var vswhere = Path.Combine(
            Environment.GetFolderPath(Environment.SpecialFolder.ProgramFilesX86), "Microsoft Visual Studio", "Installer", "vswhere.exe");
        if (!File.Exists(vswhere))
        {
            return (null, $"{name} not run: vswhere is not installed at {vswhere}");
        }

        var find = new ProcessStartInfo(vswhere)
        {
            RedirectStandardOutput = true,
            RedirectStandardError = true,
            UseShellExecute = false,
        };
        foreach (var arg in new[]
                 {
                     "-latest", "-prerelease", "-products", "*", "-version", range,
                     "-requires", "Microsoft.Component.MSBuild", "-find", @"MSBuild\**\Bin\MSBuild.exe",
                 })
        {
            find.ArgumentList.Add(arg);
        }

        var (_, output) = Run(find, TimeSpan.FromMinutes(1));
        var msbuild = output.Split('\n', StringSplitOptions.RemoveEmptyEntries | StringSplitOptions.TrimEntries).FirstOrDefault(File.Exists);
        if (msbuild is null)
        {
            return (null, $"{name} not run: vswhere found no Visual Studio {range} with MSBuild");
        }

        var version = new ProcessStartInfo(msbuild)
        {
            RedirectStandardOutput = true,
            RedirectStandardError = true,
            UseShellExecute = false,
        };
        version.ArgumentList.Add("-version");
        version.ArgumentList.Add("-nologo");
        var (_, text) = Run(version, TimeSpan.FromMinutes(1));
        return (new BuildHost(name, msbuild, text.Trim()), null);
    }
}

/// <summary>
/// A build-integration fact (WARRANT_BUILD_INTEGRATION=1) that needs one build host; when the host cannot be found, the
/// fact is skipped and its skip reason says why.
/// </summary>
[AttributeUsage(AttributeTargets.Method)]
internal sealed class HostFactAttribute : FactAttribute
{
    public const string Gate = "WARRANT_BUILD_INTEGRATION";

    public HostFactAttribute(string host)
    {
        if (string.IsNullOrEmpty(Environment.GetEnvironmentVariable(Gate)))
        {
            Skip = $"set {Gate} to run";
            return;
        }

        var (_, reason) = BuildHost.Find(host);
        if (reason is not null)
        {
            Skip = reason;
        }
    }
}
