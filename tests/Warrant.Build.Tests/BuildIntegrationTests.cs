namespace Warrant.Build.Tests;

using System.Text.RegularExpressions;
using Xunit.Abstractions;

/// <summary>
/// The build matrix (U13, R11, R12): the real packages, consumed by isolated sample projects, under <c>dotnet build</c>
/// and Visual Studio 2026's and 2022's <c>MSBuild.exe</c>. Opt-in: set WARRANT_BUILD_INTEGRATION=1. A Visual Studio that
/// <c>vswhere</c> cannot find is skipped with the reason, never passed.
/// </summary>
[Collection(BuildIntegrationGroup.Name)]
public sealed class BuildIntegrationTests(PackedPackages packages, ITestOutputHelper output)
{
    [HostFact(BuildHost.Dotnet)]
    public void TheIncrementSampleFailsDotnetBuildAtEachTheoremWithItsGoalAndCounterexample()
    {
        var host = BuildHost.Find(BuildHost.Dotnet).Host!;
        var (exitCode, log, diagnostics) = packages.DotnetIncrement;
        var dir = Path.Combine(packages.Root, "IncrementDotnet");
        Report(host, dir, log);
        Versions(host, dir);

        Assert.Equal(1, exitCode);
        AssertIncrementDiagnostics(diagnostics, log);
    }

    [HostFact(BuildHost.VisualStudio2026)]
    public void TheIncrementSampleFailsVisualStudio2026MSBuildWithTheSameDiagnostics()
    {
        var host = BuildHost.Find(BuildHost.VisualStudio2026).Host!;
        var (exitCode, log, diagnostics) = packages.BuildIncrement(host, "IncrementVs2026", Samples.Net10);
        var dir = Path.Combine(packages.Root, "IncrementVs2026");
        Report(host, dir, log);
        Versions(host, dir);

        Assert.Equal(1, exitCode);
        AssertIncrementDiagnostics(diagnostics, log);
        Assert.Equal(packages.DotnetIncrement.Diagnostics, diagnostics);
    }

    [HostFact(BuildHost.VisualStudio2022)]
    public void TheIncrementSampleOnSdk9AndNet8FailsVisualStudio2022MSBuildWithTheSameDiagnostics()
    {
        var host = BuildHost.Find(BuildHost.VisualStudio2022).Host!;
        var (exitCode, log, diagnostics) = packages.BuildIncrement(host, "IncrementVs2022", "net8.0", sdk: "9.0.320");
        var dir = Path.Combine(packages.Root, "IncrementVs2022");
        Report(host, dir, log);

        // MSBuild 17.14 cannot load SDK 10 ("requires at least version 18.0.0 of MSBuild"), so this sample is pinned to 9.
        Assert.StartsWith("9.0.", Versions(host, dir).Sdk, StringComparison.Ordinal);
        Assert.Equal(1, exitCode);
        AssertIncrementDiagnostics(diagnostics, log);
        Assert.Equal(packages.DotnetIncrement.Diagnostics, diagnostics);
    }

    [HostFact(BuildHost.Dotnet)]
    public void TrueTheoremsBuildGreenWithTheSummaryAndASecondBuildVerifiesAgain()
    {
        var host = BuildHost.Find(BuildHost.Dotnet).Host!;
        var dir = packages.Sample("Proved", Samples.Project($"<TargetFramework>{Samples.Net10}</TargetFramework>"), Samples.Proved);

        var (firstExit, firstLog) = host.Build(dir);
        var (secondExit, secondLog) = host.Build(dir);
        Report(host, dir, secondLog);

        const string Summary = "Warrant: 4 verified units, 3 theorems proved, 0 not proved.";
        Assert.True(firstExit == 0, firstLog);
        Assert.Contains(Summary, firstLog, StringComparison.Ordinal);
        Assert.True(secondExit == 0, secondLog);
        // The compiler was up to date, so Csc gave no arguments; the last compile's file was verified again (KTD22).
        Assert.Contains("Skipping target \"CoreCompile\" because all output files are up-to-date", secondLog, StringComparison.Ordinal);
        Assert.Contains(Summary, secondLog, StringComparison.Ordinal);
        Assert.True(File.Exists(Path.Combine(dir, "obj", "Debug", Samples.Net10, "warrant.csc.args")));
        Assert.DoesNotContain("WRT0011", firstLog + secondLog, StringComparison.Ordinal);
    }

    [HostFact(BuildHost.Dotnet)]
    public void ADesignTimeBuildDoesNotVerify()
    {
        var host = BuildHost.Find(BuildHost.Dotnet).Host!;
        var dir = packages.Sample("DesignTime", Samples.Project($"<TargetFramework>{Samples.Net10}</TargetFramework>"), Samples.Increment);

        // What Visual Studio's project system runs in the background: CoreCompile, with Csc reporting its arguments but
        // not compiling. The sample's theorems are false, so a verification would fail the build.
        var (exitCode, log) = host.Build(
            dir, "-t:CoreCompile", "-p:DesignTimeBuild=true", "-p:SkipCompilerExecution=true", "-p:ProvideCommandLineArgs=true");
        Report(host, dir, log);

        Assert.True(exitCode == 0, log);
        Assert.DoesNotContain("Warrant:", log, StringComparison.Ordinal);
        Assert.False(File.Exists(Path.Combine(dir, "obj", "Debug", Samples.Net10, "warrant.csc.args")));
    }

    [HostFact(BuildHost.Dotnet)]
    public void AMultiTargetedSampleVerifiesOnceAndReportsEachDiagnosticOnce()
    {
        var host = BuildHost.Find(BuildHost.Dotnet).Host!;
        var dir = packages.Sample(
            "Multi",
            Samples.Project("<TargetFrameworks>net8.0;net10.0</TargetFrameworks>"),
            new Dictionary<string, string> { ["Increments.cs"] = Samples.NoScriptOnly });

        var (exitCode, log) = host.Build(dir);
        Report(host, dir, log);

        Assert.Equal(1, exitCode);
        Assert.Equal(
            [
                "Increments.cs(9,28,9,36): error WRT0001: Theorem 'Increments.NoScript(int)' could not be proved: unsolved goals. Counterexample: x = 2147483647.",
                "Increments.cs(9,28,9,36): error WRT0001: x : Int32",
                "Increments.cs(9,28,9,36): error WRT0001: ⊢ Increment x > x",
            ],
            Samples.Diagnostics(log, dir));
        Assert.Single(Regex.Matches(log, "Warrant: 2 verified units, 0 theorems proved, 1 not proved\\."));
        Assert.Contains("1 Error(s)", log, StringComparison.Ordinal);
        Assert.True(File.Exists(Path.Combine(dir, "obj", "Debug", "net8.0", "warrant.csc.args")));
        Assert.False(File.Exists(Path.Combine(dir, "obj", "Debug", "net10.0", "warrant.csc.args")));
    }

    [HostFact(BuildHost.Dotnet)]
    public void AMultiTargetedVerifiedMethodThatDiffersUnderIfNet8IsRejected()
    {
        var host = BuildHost.Find(BuildHost.Dotnet).Host!;
        var dir = packages.Sample(
            "MultiIf",
            Samples.Project("<TargetFrameworks>net8.0;net10.0</TargetFrameworks>"),
            new Dictionary<string, string> { ["Picks.cs"] = Samples.DiffersUnderNet8 });

        var (exitCode, log) = host.Build(dir);
        Report(host, dir, log);

        Assert.Equal(1, exitCode);
        Assert.Equal(
            ["Picks.cs(8,23,8,27): error WRT0002: Sample.Picks.Pick(int) translates differently depending on which of NET8_0 the build defines."],
            Samples.Diagnostics(log, dir));
    }

    [HostFact(BuildHost.Dotnet)]
    public void ReferencingWarrantWithoutWarrantBuildWarnsWrt0011()
    {
        var host = BuildHost.Find(BuildHost.Dotnet).Host!;
        var dir = packages.Sample("NoTask", Samples.Project($"<TargetFramework>{Samples.Net10}</TargetFramework>", warrantBuild: false), Samples.Increment);

        var (exitCode, log) = host.Build(dir);
        Report(host, dir, log);

        Assert.True(exitCode == 0, log);
        // MSBuild places a Warning task's diagnostic at the task, here in the package's build/Warrant.targets.
        var warning = Assert.Single(Samples.Diagnostics(log, dir));
        Assert.Matches(
            @"[\\/]packages[\\/]warrant[\\/]0\.0\.0-it\.\d+[\\/]build[\\/]Warrant\.targets\(\d+,\d+\): warning WRT0011: Warrant: this project references Warrant but not Warrant\.Build, so no theorem is verified\. Add a reference to Warrant\.Build, or add WRT0011 to NoWarn\.$",
            warning);
        Assert.DoesNotContain(" verified unit", log, StringComparison.Ordinal);
    }

    [HostFact(BuildHost.Dotnet)]
    public void AnAppThatReferencesAVerifiedLibraryNeitherWarnsNorVerifiesIt()
    {
        var host = BuildHost.Find(BuildHost.Dotnet).Host!;
        packages.Sample("Library", Samples.Project($"<TargetFramework>{Samples.Net10}</TargetFramework>"), Samples.Proved);
        var app = packages.Sample(
            "App",
            $"""
              <PropertyGroup>
                <TargetFramework>{Samples.Net10}</TargetFramework>
                <OutputType>Exe</OutputType>
              </PropertyGroup>
              <ItemGroup>
                <ProjectReference Include="..\Library\Library.csproj" />
              </ItemGroup>
            """,
            new Dictionary<string, string> { ["Program.cs"] = "System.Console.WriteLine(Sample.Increments.Same(1));\n" });

        var (exitCode, log) = host.Build(app);
        Report(host, app, log);

        Assert.True(exitCode == 0, log);
        Assert.DoesNotContain("WRT0011", log, StringComparison.Ordinal);
        // The library verifies itself once; the app, which gets Warrant only transitively, runs nothing.
        Assert.Single(Regex.Matches(log, "Warrant: 4 verified units, 3 theorems proved, 0 not proved\\."));
        Assert.False(File.Exists(Path.Combine(app, "obj", "Debug", Samples.Net10, "warrant.csc.args")));
        Assert.True(File.Exists(Path.Combine(packages.Root, "Library", "obj", "Debug", Samples.Net10, "warrant.csc.args")));
    }

    [HostFact(BuildHost.Dotnet)]
    public void ASourceThatNeedsASourceGeneratorFailsWithWrt0012AndNoMsb6006()
    {
        var host = BuildHost.Find(BuildHost.Dotnet).Host!;
        var dir = packages.Sample(
            "Generated",
            Samples.Project($"<TargetFramework>{Samples.Net10}</TargetFramework>"),
            new Dictionary<string, string> { ["Patterns.cs"] = Samples.NeedsGeneratedRegex });

        var (exitCode, log) = host.Build(dir);
        Report(host, dir, log);

        Assert.Equal(1, exitCode);
        Assert.Contains(
            "Patterns.cs(9,33,9,35): error WRT0012: The compilation does not compile without generated sources (source generators run only inside the compiler); missing: As.",
            Samples.Diagnostics(log, dir));
        Assert.DoesNotContain("MSB6006", log, StringComparison.Ordinal);
        Assert.DoesNotContain("WRT0010", log, StringComparison.Ordinal);
    }

    /// <summary>
    /// Both theorems fail at their own location with WRT0001, the goal and the counterexample; the third, with a <c>≤</c>,
    /// shows that the goal's Unicode reaches the log intact.
    /// </summary>
    private static void AssertIncrementDiagnostics(IReadOnlyList<string> diagnostics, string log)
    {
        Assert.Contains(diagnostics, d => Regex.IsMatch(
            d, @"^Increments\.cs\(13,52,13,66\): error WRT0001: Theorem 'Increments\.AlwaysLarger\(int\)' could not be proved: .*Counterexample: x = 2147483647\.$"));
        Assert.Contains(
            "Increments.cs(16,18,16,26): error WRT0001: Theorem 'Increments.NoScript(int)' could not be proved: unsolved goals. Counterexample: x = 2147483647.",
            diagnostics);
        Assert.Contains(diagnostics, d => d.StartsWith("Increments.cs(19,18,19,29): error WRT0001: Theorem 'Increments.NeverLarger(int)' could not be proved: unsolved goals.", StringComparison.Ordinal));

        // The goal block, also logged as a message of its own (KTD20).
        var lines = string.Join('\n', Samples.Lines(log));
        Assert.Contains("\nx : Int32\n⊢ x + 1 > x\n", lines, StringComparison.Ordinal);
        Assert.Contains("\nx : Int32\n⊢ Increment x > x\n", lines, StringComparison.Ordinal);
        Assert.Contains("\nx : Int32\n⊢ Increment x ≤ x\n", lines, StringComparison.Ordinal);
        Assert.Contains("Warrant: 4 verified units, 0 theorems proved, 3 not proved.", log, StringComparison.Ordinal);
        // One error event per theorem: the loggers print each line of a message with its location, but count it once.
        Assert.Contains("3 Error(s)", log, StringComparison.Ordinal);
        Assert.DoesNotContain("MSB6006", log, StringComparison.Ordinal);
        Assert.DoesNotContain("WRT0010", log, StringComparison.Ordinal);
        Assert.DoesNotContain("WRT0011", log, StringComparison.Ordinal);
    }

    /// <summary>The MSBuild and SDK versions the host used for the sample, also written to the test output.</summary>
    private (string MSBuild, string Sdk) Versions(BuildHost host, string dir)
    {
        var versions = (host.Property(dir, "MSBuildVersion"), host.Property(dir, "NETCoreSdkVersion"));
        output.WriteLine($"{host.Name}: MSBuild {versions.Item1}, SDK {versions.Item2}");
        return versions;
    }

    private void Report(BuildHost host, string dir, string log)
    {
        output.WriteLine($"host: {host}");
        output.WriteLine($"sample: {dir}");
        output.WriteLine(log);
    }
}

/// <summary>The sample projects' files.</summary>
internal static class Samples
{
    public const string Net10 = "net10.0";

    /// <summary>The exit criterion's false claim, with and without a script, and a goal with <c>≤</c>.</summary>
    public static readonly IReadOnlyDictionary<string, string> Increment = new Dictionary<string, string>
    {
        ["Increments.cs"] = """
            using Warrant;

            namespace Sample;

            public static class Increments
            {
                [Verified]
                public static int Increment(int x) => x + 1;

                [Theorem]
                static Proof AlwaysLarger(int x) =>
                    Prove.That(Increment(x) > x)
                         .By(Tactic.Unfold(nameof(Increment)), Tactic.Omega());

                [Theorem]
                static Proof NoScript(int x) => Prove.That(Increment(x) > x);

                [Theorem]
                static Proof NeverLarger(int x) => Prove.That(Increment(x) <= x);
            }

            """,
    };

    /// <summary>True theorems that intro, exact, apply and unfold prove.</summary>
    public static readonly IReadOnlyDictionary<string, string> Proved = new Dictionary<string, string>
    {
        ["Increments.cs"] = """
            using Warrant;

            namespace Sample;

            public static class Increments
            {
                [Verified]
                public static int Same(int x) => x;

                [Theorem]
                static Proof Reflexive() =>
                    Prove.That(Spec.ForAll<int>(x => x == x)).By(Tactic.Intro("x"), Tactic.Exact(Lean.Const("rfl")));

                [Theorem]
                static Proof Symmetric(int a, int b) =>
                    Prove.That(Spec.Implies(a == b, b == a))
                         .By(Tactic.Intro("h"), Tactic.Apply(Lean.Const("Eq.symm")), Tactic.Exact("h"));

                [Theorem]
                static Proof SameIsIdentity(int x) =>
                    Prove.That(Same(x) == x).By(Tactic.Unfold(nameof(Same)), Tactic.Exact(Lean.Const("rfl")));
            }

            """,
    };

    public const string NoScriptOnly = """
        using Warrant;

        namespace Sample;

        public static class Increments
        {
            [Verified] public static int Increment(int x) => x + 1;

            [Theorem] static Proof NoScript(int x) => Prove.That(Increment(x) > x);
        }

        """;

    public const string DiffersUnderNet8 = """
        using Warrant;

        namespace Sample;

        public static class Picks
        {
            [Verified]
            public static int Pick(int x)
            {
        #if NET8_0
                return x;
        #else
                return x + 1;
        #endif
            }
        }

        """;

    public const string NeedsGeneratedRegex = """
        using System.Text.RegularExpressions;
        using Warrant;

        namespace Sample;

        public static partial class Patterns
        {
            [GeneratedRegex("a+")]
            public static partial Regex As();

            [Verified]
            public static int Same(int x) => x;
        }

        """;

    /// <summary>A project body referencing the packages as a consumer would; <c>$(WarrantVersion)</c> is filled in.</summary>
    public static string Project(string targetFrameworks, bool warrantBuild = true) => $"""
          <PropertyGroup>
            {targetFrameworks}
          </PropertyGroup>
          <ItemGroup>
            <PackageReference Include="Warrant" Version="$(WarrantVersion)" />
            {(warrantBuild ? "<PackageReference Include=\"Warrant.Build\" Version=\"$(WarrantVersion)\" />" : "")}
          </ItemGroup>
        """;

    public static string GlobalJson(string version, string rollForward) =>
        $$"""{ "sdk": { "version": "{{version}}", "rollForward": "{{rollForward}}" } }""";

    /// <summary>
    /// Each distinct error and warning line of a build log, in order, relative to the sample directory and without
    /// MSBuild's trailing <c>[project]</c>, so logs from different hosts and directories compare equal.
    /// </summary>
    public static IReadOnlyList<string> Diagnostics(string log, string sampleDir)
    {
        var prefix = sampleDir.TrimEnd(Path.DirectorySeparatorChar) + Path.DirectorySeparatorChar;
        return Lines(log)
            .Where(l => Regex.IsMatch(l, @": (error|warning) [A-Z]+\d+: "))
            .Select(l => l.StartsWith(prefix, StringComparison.OrdinalIgnoreCase) ? l[prefix.Length..] : l)
            .Select(l => Regex.Replace(l, @" \[[^\[\]]+\]$", ""))
            .Distinct(StringComparer.Ordinal)
            .ToList();
    }

    /// <summary>
    /// The log's lines, trimmed and without the <c>1&gt;</c> node prefix that <c>dotnet build</c>'s file logger adds and
    /// Visual Studio's MSBuild does not.
    /// </summary>
    public static IEnumerable<string> Lines(string log) =>
        log.Split('\n').Select(l => Regex.Replace(l.Trim(), @"^\d+>", ""));
}
