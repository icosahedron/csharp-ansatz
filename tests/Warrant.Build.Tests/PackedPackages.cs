namespace Warrant.Build.Tests;

using System.Diagnostics;
using System.Globalization;
using System.Text;
using System.Text.RegularExpressions;

/// <summary>The build-integration tests share one packed feed and run one at a time.</summary>
[CollectionDefinition(Name)]
public sealed class BuildIntegrationGroup : ICollectionFixture<PackedPackages>
{
    public const string Name = "build integration";
}

/// <summary>
/// <c>Warrant</c> and <c>Warrant.Build</c> packed into a temporary feed with a version no earlier run used, under a short
/// root (<c>%TEMP%\wrt-it\&lt;guid8&gt;</c>) that isolates every sample from the repository and the machine: empty
/// Directory.Build files, a global.json, and a NuGet.config with only the feed and nuget.org and its own packages folder.
/// Samples reference the packages with <c>PackageReference</c>, so NuGet imports their <c>build/</c> files as it would
/// for any consumer.
/// </summary>
public sealed class PackedPackages : IDisposable
{
    private readonly Lazy<(int ExitCode, string Log, IReadOnlyList<string> Diagnostics)> dotnetIncrement;

    public PackedPackages()
    {
        Root = Path.Combine(Path.GetTempPath(), "wrt-it", Guid.NewGuid().ToString("N")[..8]);
        Feed = Path.Combine(Root, "feed");
        Version = $"0.0.0-it.{DateTime.UtcNow.Ticks}";
        dotnetIncrement = new(() => BuildIncrement(BuildHost.Find(BuildHost.Dotnet).Host!, "IncrementDotnet", Samples.Net10));
        if (string.IsNullOrEmpty(Environment.GetEnvironmentVariable(HostFactAttribute.Gate)))
        {
            return;
        }

        Directory.CreateDirectory(Feed);
        // Stop MSBuild's upward search so the repository's and the machine's Directory.Build files never apply.
        // M5b KTD29: samples verify in-process unless they test the server, which they then shut down.
        File.WriteAllText(Path.Combine(Root, "Directory.Build.props"), """
            <Project>
              <PropertyGroup>
                <WarrantUseServer>false</WarrantUseServer>
              </PropertyGroup>
            </Project>
            """);
        File.WriteAllText(Path.Combine(Root, "Directory.Build.targets"), "<Project />");
        File.WriteAllText(Path.Combine(Root, "global.json"), Samples.GlobalJson("10.0.100", "latestFeature"));
        File.WriteAllText(Path.Combine(Root, "NuGet.config"), $"""
            <?xml version="1.0" encoding="utf-8"?>
            <configuration>
              <config>
                <add key="globalPackagesFolder" value="{Path.Combine(Root, "packages")}" />
              </config>
              <packageSources>
                <clear />
                <add key="warrant-it" value="{Feed}" />
                <add key="nuget.org" value="https://api.nuget.org/v3/index.json" />
              </packageSources>
            </configuration>
            """);

        var repository = RepositoryRoot();
        Pack(repository, Path.Combine(repository, "src", "Warrant", "Warrant.csproj"));
        Pack(repository, Path.Combine(repository, "src", "Warrant.Build", "Warrant.Build.csproj"));
    }

    public string Root { get; }

    public string Feed { get; }

    /// <summary>The packages' version, <c>0.0.0-it.&lt;ticks&gt;</c>.</summary>
    public string Version { get; }

    /// <summary>The packed CLI, which a build of any sample runs.</summary>
    public string CliPath => Path.Combine(Root, "packages", "warrant.build", Version, "tools", "net10.0", "any", "warrant.dll");

    /// <summary>The Increment sample built once with <c>dotnet build</c>: the diagnostics every other host must match.</summary>
    internal (int ExitCode, string Log, IReadOnlyList<string> Diagnostics) DotnetIncrement => dotnetIncrement.Value;

    /// <summary>
    /// Writes a sample project <paramref name="name"/>.csproj with <paramref name="files"/> beside it. A sample pinned to
    /// another SDK gets its own global.json.
    /// </summary>
    internal string Sample(string name, string projectBody, IReadOnlyDictionary<string, string> files, string? sdk = null)
    {
        var dir = Path.Combine(Root, name);
        Directory.CreateDirectory(dir);
        if (sdk is not null)
        {
            File.WriteAllText(Path.Combine(dir, "global.json"), Samples.GlobalJson(sdk, "latestPatch"));
        }

        File.WriteAllText(Path.Combine(dir, name + ".csproj"), $"""
            <Project Sdk="Microsoft.NET.Sdk">
            {projectBody.Replace("$(WarrantVersion)", Version, StringComparison.Ordinal)}
            </Project>
            """);
        foreach (var (file, text) in files)
        {
            File.WriteAllText(Path.Combine(dir, file), text, new UTF8Encoding(encoderShouldEmitUTF8Identifier: true));
        }

        return dir;
    }

    /// <summary>
    /// Builds the Increment sample with <paramref name="host"/> in a directory of its own, through a verification server of
    /// its own, which is shut down before this returns (M5b KTD29).
    /// </summary>
    internal (int ExitCode, string Log, IReadOnlyList<string> Diagnostics) BuildIncrement(BuildHost host, string name, string targetFramework, string? sdk = null)
    {
        var dir = Sample(name, Samples.Project($"<TargetFramework>{targetFramework}</TargetFramework>", useServer: true), Samples.Increment, sdk);
        using var server = new SampleServer(CliPath);
        var (exitCode, log) = host.Build(dir, server.Environment);
        Assert.True(server.ShutDown() is not null, $"no verification server was running after the build:\n{log}");
        return (exitCode, log, Samples.Diagnostics(log, dir));
    }

    public void Dispose()
    {
        try
        {
            if (Directory.Exists(Root))
            {
                Directory.Delete(Root, recursive: true);
            }
        }
        catch (IOException)
        {
            // A temp directory left behind is harmless.
        }
        catch (UnauthorizedAccessException)
        {
            // Likewise.
        }
    }

    private void Pack(string repository, string project)
    {
        var start = new ProcessStartInfo(FakeCli.DotnetHost)
        {
            WorkingDirectory = repository,
            RedirectStandardOutput = true,
            RedirectStandardError = true,
            UseShellExecute = false,
        };
        // PackageVersion, not Version: the assemblies keep their versions, so packing does not rebuild them every run.
        foreach (var arg in new[]
                 {
                     "pack", project, "-c", "Release", "-o", Feed, $"-p:PackageVersion={Version}",
                     "-nologo", "-nodeReuse:false", "-p:UseSharedCompilation=false",
                 })
        {
            start.ArgumentList.Add(arg);
        }

        BuildHost.Isolate(start, visualStudio: false);
        var (exitCode, output) = BuildHost.Run(start, TimeSpan.FromMinutes(10));
        Assert.True(exitCode == 0, $"dotnet pack {Path.GetFileName(project)} failed:\n{output}");
    }

    private static string RepositoryRoot()
    {
        for (var dir = new DirectoryInfo(AppContext.BaseDirectory); dir is not null; dir = dir.Parent)
        {
            if (File.Exists(Path.Combine(dir.FullName, "Warrant.slnx")))
            {
                return dir.FullName;
            }
        }

        throw new InvalidOperationException("the repository root (Warrant.slnx) is not above " + AppContext.BaseDirectory);
    }
}

/// <summary>
/// A verification server of one sample's own (M5b KTD29): its builds name a unique endpoint, so no other test's or the
/// user's server answers them, and it is shut down at the end, so no server outlives the tests or holds their files. The
/// short idle timeout is a backstop for a test run that is killed before the shutdown.
/// </summary>
internal sealed class SampleServer(string cliPath) : IDisposable
{
    private bool shutDown;

    /// <summary>The endpoint's name.</summary>
    public string Endpoint { get; } = "wrt-it-" + Guid.NewGuid().ToString("N")[..16];

    /// <summary>The variables a build that uses this server runs with.</summary>
    public IReadOnlyDictionary<string, string> Environment => new Dictionary<string, string>
    {
        ["WARRANT_SERVER_ENDPOINT"] = Endpoint,
        ["WARRANT_SERVER_IDLE_SECONDS"] = "300",
    };

    /// <summary>
    /// Runs <c>warrant server shutdown</c> and waits for the server's process to exit; returns its process ID, or null
    /// when no server was running.
    /// </summary>
    public int? ShutDown()
    {
        var (exitCode, output, processId) = ShutDownAndWait();
        Assert.True(exitCode == 0, $"warrant server shutdown failed:\n{output}");
        return processId;
    }

    public void Dispose()
    {
        if (!shutDown)
        {
            ShutDownAndWait();
        }
    }

    private (int ExitCode, string Output, int? ProcessId) ShutDownAndWait()
    {
        shutDown = true;
        var start = new ProcessStartInfo(FakeCli.DotnetHost)
        {
            RedirectStandardOutput = true,
            RedirectStandardError = true,
            UseShellExecute = false,
        };
        foreach (var arg in new[] { cliPath, "server", "shutdown" })
        {
            start.ArgumentList.Add(arg);
        }

        foreach (var (key, value) in Environment)
        {
            start.Environment[key] = value;
        }

        var (exitCode, output) = BuildHost.Run(start, TimeSpan.FromMinutes(2));
        var match = Regex.Match(output, @"\(process (\d+)\)");
        if (!match.Success)
        {
            return (exitCode, output, null);
        }

        var processId = int.Parse(match.Groups[1].Value, CultureInfo.InvariantCulture);
        try
        {
            using var process = Process.GetProcessById(processId);
            if (!process.WaitForExit(TimeSpan.FromMinutes(1)))
            {
                process.Kill();
                Assert.Fail($"the verification server (process {processId}) did not exit after shutdown");
            }
        }
        catch (ArgumentException)
        {
            // It has already exited.
        }

        return (exitCode, output, processId);
    }
}
