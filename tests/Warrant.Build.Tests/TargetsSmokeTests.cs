namespace Warrant.Build.Tests;

using System.Diagnostics;
using System.Text;

/// <summary>
/// Builds tiny sample projects with <c>dotnet build</c>, importing the targets the way the packages do, with the
/// task built here and the fake CLI in place of <c>warrant.dll</c>. Opt-in: set WARRANT_BUILD_INTEGRATION=1.
/// </summary>
public sealed class TargetsSmokeTests : IDisposable
{
    private const string Gate = "WARRANT_BUILD_INTEGRATION";

    private static readonly string Targets = Path.Combine(AppContext.BaseDirectory, "targets");

    private readonly string root = Path.Combine(Path.GetTempPath(), "wrt-it", Guid.NewGuid().ToString("N")[..8]);

    public TargetsSmokeTests()
    {
        Directory.CreateDirectory(root);
        // Stop MSBuild's upward search so the repository's own Directory.Build files never apply.
        File.WriteAllText(Path.Combine(root, "Directory.Build.props"), "<Project />");
        File.WriteAllText(Path.Combine(root, "Directory.Build.targets"), "<Project />");
    }

    public void Dispose()
    {
        try
        {
            Directory.Delete(root, recursive: true);
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

    [FactRequiringEnv(Gate)]
    public void AFailedTheoremFailsTheBuildAndEveryBuildVerifiesAgain()
    {
        var project = Sample("Increment", "<TargetFramework>net10.0</TargetFramework>");
        using var fake = new FakeCli(project);
        fake.Script(
            [
                "WRT1\tdiag\terror\tWRT0001\tIncrements.cs\t7\t17\t7\t40\ttheorem 'Increment_Gt' could not be proved\\nx : Int32\\n⊢ x + 1 > x",
                "WRT1\tgoal\tinfo\t\t\t0\t0\t0\t0\tx : Int32\\n⊢ x + 1 ≤ x",
                "WRT1\tsummary\tinfo\t\t\t0\t0\t0\t0\tWarrant: 1 verified unit, 0 theorems proved, 1 not proved.",
            ],
            exitCode: 1);

        var (exitCode, log) = Build(project);

        Assert.NotEqual(0, exitCode);
        Assert.Contains("Increments.cs(7,17,7,40): error WRT0001: theorem 'Increment_Gt' could not be proved", log, StringComparison.Ordinal);
        Assert.Contains("x + 1 ≤ x", log, StringComparison.Ordinal);
        Assert.Contains("Warrant: 1 verified unit, 0 theorems proved, 1 not proved.", log, StringComparison.Ordinal);
        Assert.DoesNotContain("MSB6006", log, StringComparison.Ordinal);
        Assert.DoesNotContain("WRT0011", log, StringComparison.Ordinal);

        var argsFile = Path.Combine(project, "obj", "Debug", "net10.0", "warrant.csc.args");
        var cscArgs = File.ReadAllLines(argsFile);
        Assert.Contains(cscArgs, a => a.StartsWith("/define:", StringComparison.Ordinal) && a.Contains("NET10_0", StringComparison.Ordinal));
        Assert.Contains(cscArgs, a => a.EndsWith("Increments.cs", StringComparison.Ordinal));
        var args = Assert.Single(fake.Invocations());
        Assert.Equal(["verify", "--csc-args"], args.Take(2));
        Assert.Equal(argsFile, Path.GetFullPath(args[2], project));
        Assert.DoesNotContain("--keep-conditional-check", args);

        fake.Script(["WRT1\tsummary\tinfo\t\t\t0\t0\t0\t0\tWarrant: 1 verified unit, 1 theorem proved, 0 not proved."], exitCode: 0);
        var (secondExit, secondLog) = Build(project);

        Assert.Equal(0, secondExit);
        Assert.Contains("Warrant: 1 verified unit, 1 theorem proved, 0 not proved.", secondLog, StringComparison.Ordinal);
        Assert.Equal(2, fake.Invocations().Count);
        Assert.True(File.Exists(argsFile));
    }

    [FactRequiringEnv(Gate)]
    public void ReferencingWarrantWithoutVerificationWarnsWrt0011()
    {
        var withoutTask = Sample("NoTask", "<TargetFramework>net10.0</TargetFramework>", importWarrantBuild: false);
        var disabled = Sample("Disabled", "<TargetFramework>net10.0</TargetFramework><WarrantEnabled>false</WarrantEnabled>");
        using var fake = new FakeCli(disabled);

        var (noTaskExit, noTaskLog) = Build(withoutTask);
        var (disabledExit, disabledLog) = Build(disabled);

        Assert.Equal(0, noTaskExit);
        Assert.Contains("warning WRT0011: Warrant: this project references Warrant but not Warrant.Build", noTaskLog, StringComparison.Ordinal);
        Assert.Equal(0, disabledExit);
        Assert.Contains("warning WRT0011: Warrant: WarrantEnabled is 'false'", disabledLog, StringComparison.Ordinal);
        Assert.Empty(fake.Invocations());
    }

    [FactRequiringEnv(Gate)]
    public void TheServerIsOffInContinuousIntegrationUnlessSetAndTheCacheIsUnderObj()
    {
        // M5b KTD27: WarrantUseServer, WarrantRecheck and WarrantCacheDir become --server, --recheck and --cache-dir.
        var project = Sample("Knobs", "<TargetFramework>net10.0</TargetFramework>");
        using var fake = new FakeCli(project);
        fake.Script(["WRT1	summary	info			0	0	0	0	Warrant: 0 verified units, 0 theorems proved, 0 not proved."], exitCode: 0);
        var cache = Path.Combine(project, "obj", "warrant", "cache");

        var builds = new[]
        {
            Build(project),
            Build(project, "-p:ContinuousIntegrationBuild=true"),
            Build(project, "-p:ContinuousIntegrationBuild=true", "-p:WarrantUseServer=true", "-p:WarrantRecheck=true"),
            Build(project, "-p:WarrantUseServer=false"),
            Build(project, "-p:WarrantUseCache=false"),
        };

        Assert.All(builds, b => Assert.True(b.ExitCode == 0, b.Log));
        var runs = fake.Invocations().Select(a => a.SkipWhile(x => x != "--server").ToArray()).ToList();
        Assert.Equal(
            [
                ["--server", "auto", "--cache-dir", cache],
                ["--server", "off", "--cache-dir", cache],
                ["--server", "auto", "--cache-dir", cache, "--recheck"],
                ["--server", "off", "--cache-dir", cache],
                ["--server", "auto"],
            ],
            runs);
    }

    [FactRequiringEnv(Gate)]
    public void CleanAndRebuildDeleteTheCache()
    {
        // M5b R12.
        var project = Sample("Clean", "<TargetFramework>net10.0</TargetFramework>");
        using var fake = new FakeCli(project);
        fake.Script(["WRT1	summary	info			0	0	0	0	Warrant: 0 verified units, 0 theorems proved, 0 not proved."], exitCode: 0);
        var cache = Path.Combine(project, "obj", "warrant", "cache");

        WriteCache(cache);
        var (cleanExit, cleanLog) = Build(project, "-t:Clean");
        Assert.True(cleanExit == 0, cleanLog);
        Assert.False(Directory.Exists(cache), cleanLog);
        Assert.True(Directory.Exists(Path.Combine(project, "obj")));

        WriteCache(cache);
        var (rebuildExit, rebuildLog) = Build(project, "-t:Rebuild");
        Assert.True(rebuildExit == 0, rebuildLog);
        Assert.False(Directory.Exists(cache), rebuildLog);
        Assert.Single(fake.Invocations());
    }

    [FactRequiringEnv(Gate)]
    public void CleanDeletesOnlyWhatTheCacheWrote()
    {
        // A WarrantCacheDir that names the project directory by mistake: no marker, so clean deletes nothing there.
        var project = Sample("CleanSafe", "<TargetFramework>net10.0</TargetFramework>");
        using var fake = new FakeCli(project);
        var keyNamed = Path.Combine(project, new string('a', 64) + ".json");
        File.WriteAllText(keyNamed, "not a cache entry");
        var (exit, log) = Build(project, "-t:Clean", "-p:WarrantCacheDir=.");
        Assert.True(exit == 0, log);
        Assert.True(File.Exists(keyNamed), log);
        Assert.True(File.Exists(Path.Combine(project, "CleanSafe.csproj")), log);

        // A marked cache that also holds a file the cache did not write: the entries go, the file and the directory stay.
        var cache = Path.Combine(project, "obj", "warrant", "cache");
        WriteCache(cache);
        var other = Path.Combine(cache, "notes.json");
        File.WriteAllText(other, "mine");
        (exit, log) = Build(project, "-t:Clean");
        Assert.True(exit == 0, log);
        Assert.Equal([other], Directory.GetFiles(cache));
    }

    /// <summary>A result cache as the CLI leaves it: the marker, two entries and an unfinished write.</summary>
    private static void WriteCache(string cache)
    {
        Directory.CreateDirectory(cache);
        File.WriteAllText(Path.Combine(cache, "WARRANT-CACHE"), "marker");
        File.WriteAllText(Path.Combine(cache, new string('0', 64) + ".json"), "{}");
        File.WriteAllText(Path.Combine(cache, new string('f', 64) + ".json"), "{}");
        File.WriteAllText(Path.Combine(cache, new string('f', 64) + ".json." + new string('1', 32) + ".tmp"), "{");
    }

    private string Sample(string name, string properties, bool importWarrantBuild = true)
    {
        var dir = Path.Combine(root, name);
        Directory.CreateDirectory(dir);
        var warrantBuild = Path.Combine(Targets, "Warrant.Build");
        var buildImports = importWarrantBuild
            ? ($"  <Import Project=\"{warrantBuild}\\Warrant.Build.props\" />", $"  <Import Project=\"{warrantBuild}\\Warrant.Build.targets\" />")
            : ("", "");
        File.WriteAllText(Path.Combine(dir, name + ".csproj"), $"""
            <Project>
              <Import Project="Sdk.props" Sdk="Microsoft.NET.Sdk" />
            {buildImports.Item1}
              <PropertyGroup>
                {properties}
                <OutputType>Library</OutputType>
                <ImplicitUsings>disable</ImplicitUsings>
              </PropertyGroup>
              <Import Project="Sdk.targets" Sdk="Microsoft.NET.Sdk" />
            {buildImports.Item2}
              <Import Project="{Path.Combine(Targets, "Warrant", "Warrant.targets")}" />
            </Project>
            """);
        File.WriteAllText(Path.Combine(dir, "Increments.cs"), "public static class Increments { public static int Increment(int x) => x + 1; }\n");
        return dir;
    }

    private static (int ExitCode, string Log) Build(string project, params string[] extra)
    {
        var log = Path.Combine(project, $"build-{Guid.NewGuid():N}.log");
        var start = new ProcessStartInfo(FakeCli.DotnetHost)
        {
            WorkingDirectory = project,
            RedirectStandardOutput = true,
            RedirectStandardError = true,
            UseShellExecute = false,
        };
        foreach (var arg in new[]
                 {
                     "build", "-nologo", "-nodeReuse:false", "-p:UseSharedCompilation=false",
                     $"-p:WarrantTaskAssembly={Path.Combine(AppContext.BaseDirectory, "Warrant.Build.dll")}",
                     $"-p:WarrantCliPath={FakeCli.CliPath}",
                     $"-flp:logfile={log};encoding=utf-8;verbosity=normal",
                 }.Concat(extra))
        {
            start.ArgumentList.Add(arg);
        }

        // The test host's MSBuild variables point at the SDK that runs the tests; the sample resolves its own.
        foreach (var key in start.Environment.Keys.Where(k => k.StartsWith("MSBuild", StringComparison.OrdinalIgnoreCase)).ToList())
        {
            start.Environment.Remove(key);
        }

        start.Environment["MSBUILDDISABLENODEREUSE"] = "1";
        start.Environment["DOTNET_CLI_USE_MSBUILD_SERVER"] = "0";
        start.Environment["DOTNET_CLI_TELEMETRY_OPTOUT"] = "1";
        start.Environment["DOTNET_NOLOGO"] = "1";

        using var process = Process.Start(start)!;
        var stdout = process.StandardOutput.ReadToEndAsync();
        var stderr = process.StandardError.ReadToEndAsync();
        Assert.True(process.WaitForExit(TimeSpan.FromMinutes(3)), "dotnet build timed out");
        var text = File.Exists(log) ? File.ReadAllText(log, Encoding.UTF8) : stdout.Result + stderr.Result;
        return (process.ExitCode, text);
    }
}
