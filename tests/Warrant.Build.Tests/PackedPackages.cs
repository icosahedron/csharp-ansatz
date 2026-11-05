namespace Warrant.Build.Tests;

using System.Diagnostics;
using System.Text;

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
        File.WriteAllText(Path.Combine(Root, "Directory.Build.props"), "<Project />");
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

    /// <summary>Builds the Increment sample with <paramref name="host"/> in a directory of its own.</summary>
    internal (int ExitCode, string Log, IReadOnlyList<string> Diagnostics) BuildIncrement(BuildHost host, string name, string targetFramework, string? sdk = null)
    {
        var dir = Sample(name, Samples.Project($"<TargetFramework>{targetFramework}</TargetFramework>"), Samples.Increment, sdk);
        var (exitCode, log) = host.Build(dir);
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
