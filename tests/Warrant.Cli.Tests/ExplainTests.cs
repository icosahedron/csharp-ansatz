using Microsoft.CodeAnalysis;
using Warrant.Engine;
using Warrant.Frontend;

namespace Warrant.Cli.Tests;

/// <summary>
/// <c>warrant explain</c>, <c>export</c> and <c>report</c> (M5b U16, KTD24, KTD25): every step of a failing proof, from the
/// build's arguments or a directory, in-process or through the server; <c>verify --out</c> and <c>--report</c> through the
/// server give the files an in-process run gives, and the server keeps the report.
/// </summary>
[Collection(ServerProcesses.Name)]
public sealed class ExplainTests : IDisposable
{
    private const string Failing = """
        public static class Increments
        {
            [Verified]
            public static int Increment(int x) => unchecked(x + 1);

            [Theorem]
            static Proof AlwaysLarger(int x) =>
                Prove.That(Increment(x) > x)
                     .By(Tactic.Unfold(nameof(Increment)), Tactic.Omega());

            [Theorem]
            static Proof LargerBelowMax(int x) =>
                Prove.That(Spec.Implies(x < int.MaxValue, Increment(x) > x))
                     .By(Tactic.Unfold(nameof(Increment)), Tactic.Simp(), Tactic.Omega());

            [Verified]
            public static int Unrelated(int x) => unchecked(x * 2);
        }
        """;

    private readonly string _root = Path.Combine(Path.GetTempPath(), "warrant-explain-" + Guid.NewGuid().ToString("N")[..12]);

    public void Dispose()
    {
        if (Directory.Exists(_root))
        {
            Directory.Delete(_root, recursive: true);
        }
    }

    private static (int Code, string Output) Explain(string[] args, ServerSettings? settings = null)
    {
        using var output = new StringWriter { NewLine = "\n" };
        var code = ExplainCommand.Run(args, output, output, settings);
        return (code, output.ToString());
    }

    /// <summary>The lines after the first, which names the directory and so differs between runs.</summary>
    private static string Body(string output) => output[(output.IndexOf('\n', StringComparison.Ordinal) + 1)..];

    [Fact]
    public void ExplainPrintsTheGoalBeforeUnfoldTheGoalAfterItAndOmegasFailureWithTheCounterexample()
    {
        using var source = new SourceDirectory(Failing);

        var (code, output) = Explain(["Increments.AlwaysLarger(int)", "--sources", source.Path]);

        Assert.Equal(1, code);
        var expectedOrder = new[]
        {
            "explaining Increments.AlwaysLarger(int)  ",
            "[1] Tactic.Unfold(nameof(Increment))   ",
            "  before:\n    x : Int32\n    ⊢ Increment x > x\n",
            "  after:\n    x : Int32\n    ⊢ x + 1 > x\n",
            "[2] Tactic.Omega()   ",
            "  failed:\n    omega could not prove the goal",
            "error WRT0001: Theorem 'Increments.AlwaysLarger(int)' could not be proved: omega could not prove the goal. Counterexample: x = 2147483647.",
            "Warrant: 2 verified units, 0 theorems proved, 1 not proved.\n",
        };
        int at = 0;
        foreach (var part in expectedOrder)
        {
            int next = output.IndexOf(part, at, StringComparison.Ordinal);
            Assert.True(next >= 0, $"missing, or out of order: {part}\n---\n{output}");
            at = next + part.Length;
        }
        // Only the unit and what it needs were verified.
        Assert.DoesNotContain("LargerBelowMax", output, StringComparison.Ordinal);
        Assert.DoesNotContain("Unrelated", output, StringComparison.Ordinal);
    }

    [Fact]
    public void ADocCommentIdFindsTheSameUnitAndAnUnknownOrAmbiguousNameListsTheUnits()
    {
        using var source = new SourceDirectory(Failing);

        var (byName, nameOutput) = Explain(["AlwaysLarger", "--sources", source.Path]);
        var (byId, idOutput) = Explain(["M:Increments.AlwaysLarger(System.Int32)", "--sources", source.Path]);
        var (unknown, unknownOutput) = Explain(["NoSuchTheorem", "--sources", source.Path]);

        Assert.Equal(1, byName);
        Assert.Equal(1, byId);
        Assert.Equal(Body(nameOutput), Body(idOutput));
        Assert.Equal(2, unknown);
        Assert.Contains(
            "no unit is named 'NoSuchTheorem'; the units are:\n  Increments.AlwaysLarger(int)\n  Increments.Increment(int)\n  Increments.LargerBelowMax(int)\n  Increments.Unrelated(int)\n",
            unknownOutput, StringComparison.Ordinal);
    }

    [Fact]
    public void AProvedTheoremIsExplainedStepByStepAndExitsZero()
    {
        using var source = new SourceDirectory(Failing);

        var (code, output) = Explain(["LargerBelowMax", "--sources", source.Path]);

        Assert.Equal(0, code);
        Assert.Contains("[1] Tactic.Unfold(nameof(Increment))", output, StringComparison.Ordinal);
        Assert.Contains("[2] Tactic.Simp()", output, StringComparison.Ordinal);
        Assert.Contains("[3] Tactic.Omega()", output, StringComparison.Ordinal);
        Assert.Contains("  after:\n    no goals\n", output, StringComparison.Ordinal);
        Assert.EndsWith("Warrant: 2 verified units, 1 theorems proved, 0 not proved.\n", output, StringComparison.Ordinal);
    }

    [Fact]
    public async Task ExplainThroughTheServerPrintsWhatItPrintsInProcess()
    {
        await using var server = new TestServer();
        using var source = new SourceDirectory(Failing);

        var (offCode, off) = Explain(["Increments.AlwaysLarger(int)", "--sources", source.Path, "--server", "off"], server.Settings);
        var (autoCode, auto) = Explain(["Increments.AlwaysLarger(int)", "--sources", source.Path, "--server", "auto"], server.Settings);

        Assert.Equal(offCode, autoCode);
        Assert.DoesNotContain("verification server unavailable", auto, StringComparison.Ordinal);
        // --server off names no path; the server's run is tagged. Everything else, trace included, is the same.
        Assert.EndsWith(" not proved. [server]\n", auto, StringComparison.Ordinal);
        Assert.Equal(off, auto.Replace(" [server]\n", "\n", StringComparison.Ordinal));
        Assert.NotNull(await server.ConnectAsync());
    }

    /// <summary>
    /// A project as a build leaves it: the sample's arguments (plus <paramref name="extraArgs"/>) in <c>sample.csc.args</c>,
    /// <c>src/C.cs</c> holding <paramref name="source"/>, and the reference pack and Warrant under <c>refs/</c>.
    /// </summary>
    private string Project(string source, params string[] extraArgs)
    {
        var project = Path.Combine(_root, "project");
        var fixture = Path.Combine(AppContext.BaseDirectory, "cscargs");
        foreach (var file in Directory.EnumerateFiles(fixture, "*", SearchOption.AllDirectories))
        {
            var target = Path.Combine(project, Path.GetRelativePath(fixture, file));
            Directory.CreateDirectory(Path.GetDirectoryName(target)!);
            File.Copy(file, target);
        }
        var refs = Directory.CreateDirectory(Path.Combine(project, "refs")).FullName;
        foreach (var info in Basic.Reference.Assemblies.Net100.ReferenceInfos.All)
        {
            File.WriteAllBytes(Path.Combine(refs, info.FileName), info.ImageBytes);
        }
        using (var image = typeof(CompilationFactory).Assembly.GetManifestResourceStream("Warrant.dll")!)
        using (var dll = File.Create(Path.Combine(refs, "Warrant.dll")))
        {
            image.CopyTo(dll);
        }
        Directory.CreateDirectory(Path.Combine(project, "src"));
        File.WriteAllText(Path.Combine(project, "src", "C.cs"), "using Warrant;\n" + source);
        var args = Path.Combine(project, "sample.csc.args");
        File.AppendAllLines(args, extraArgs);
        return project;
    }

    [Fact]
    public void WithoutArgumentsExplainUsesTheLatestBuildsArgumentFileUnderObj()
    {
        var project = Project(Failing);
        var obj = Directory.CreateDirectory(Path.Combine(project, "obj", "Debug", "net10.0")).FullName;
        File.Move(Path.Combine(project, "sample.csc.args"), Path.Combine(obj, ExplainCommand.CscArgsFileName));

        var (code, output) = Explain(["AlwaysLarger", "--project-dir", project]);
        var (none, noneOutput) = Explain(["AlwaysLarger", "--project-dir", _root]);

        Assert.Equal(1, code);
        Assert.Contains($"from {Path.Combine(obj, ExplainCommand.CscArgsFileName)}", output, StringComparison.Ordinal);
        Assert.Contains("[2] Tactic.Omega()", output, StringComparison.Ordinal);
        Assert.Equal(2, none);
        Assert.Contains("no warrant.csc.args under", noneOutput, StringComparison.Ordinal);
    }

    [Fact]
    public void ExplainUsesTheArgumentsOfTheFrameworkTheBuildVerifiedNotTheNewest()
    {
        // #124: every target framework writes its argument file; only the one that verifies writes warrant.explain.
        var project = Project(Failing);
        var verified = Directory.CreateDirectory(Path.Combine(project, "obj", "Debug", "net10.0")).FullName;
        var other = Directory.CreateDirectory(Path.Combine(project, "obj", "Debug", "net8.0")).FullName;
        var verifiedArgs = Path.Combine(verified, ExplainCommand.CscArgsFileName);
        File.Move(Path.Combine(project, "sample.csc.args"), verifiedArgs);
        var otherArgs = Path.Combine(other, ExplainCommand.CscArgsFileName);
        File.WriteAllLines(otherArgs, ["/langversion:not-a-version", "src/C.cs"]);
        File.SetLastWriteTimeUtc(otherArgs, File.GetLastWriteTimeUtc(verifiedArgs).AddMinutes(1));

        var (ambiguous, ambiguousOutput) = Explain(["AlwaysLarger", "--project-dir", project]);
        File.WriteAllLines(Path.Combine(verified, ExplainCommand.BuildFileName),
            ["warrant-explain 1", $"args={verifiedArgs}", $"project={project}", "keep-conditional-check=true"]);
        var (code, output) = Explain(["AlwaysLarger", "--project-dir", project]);

        Assert.Equal(2, ambiguous);
        Assert.Contains("2 warrant.csc.args files under", ambiguousOutput, StringComparison.Ordinal);
        Assert.Equal(1, code);
        Assert.Contains($"from {verifiedArgs}", output, StringComparison.Ordinal);
        Assert.Contains("[2] Tactic.Omega()", output, StringComparison.Ordinal);
    }

    [Fact]
    public void ExplainPassesTheReferencedProjectsSourceRecordsTheBuildVerifiedWith()
    {
        // #123: a closed class from a referenced project is checked from that project's record, which explain must pass as
        // the build does. An old-format record makes the difference visible: it is read only when it is passed.
        var refs = Path.Combine(_root, "project", "refs");
        Directory.CreateDirectory(refs);
        var shapes = Microsoft.CodeAnalysis.CSharp.CSharpCompilation.Create(
            "Shapes",
            [Microsoft.CodeAnalysis.CSharp.CSharpSyntaxTree.ParseText(
                "namespace Shapes; [Warrant.Closed] public sealed class Color { public static Color Red { get; } = new(); private Color() { } }")],
            [.. Basic.Reference.Assemblies.Net100.References.All, CompilationFactory.WarrantReference],
            new Microsoft.CodeAnalysis.CSharp.CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary));
        Assert.True(shapes.Emit(Path.Combine(refs, "Shapes.dll")).Success);
        var project = Project(
            "public static class Uses { [Verified] public static bool Same(Shapes.Color a, Shapes.Color b) => a == b; }",
            "/reference:refs/Shapes.dll");
        var obj = Directory.CreateDirectory(Path.Combine(project, "obj", "Debug", "net10.0")).FullName;
        var args = Path.Combine(obj, ExplainCommand.CscArgsFileName);
        File.Move(Path.Combine(project, "sample.csc.args"), args);
        var record = Path.Combine(_root, "warrant.source");
        File.WriteAllLines(record, ["warrant-source 1", "assembly=Shapes", $"args={args}", $"project={project}"]);

        var (_, without) = Explain(["Uses.Same", "--project-dir", project]);
        File.WriteAllLines(Path.Combine(obj, ExplainCommand.BuildFileName),
            ["warrant-explain 1", $"args={args}", $"project={project}", "keep-conditional-check=false", $"reference-source={record}"]);
        var (_, with) = Explain(["Uses.Same", "--project-dir", project]);

        // Without the record the unit is rejected (WRT0002, no recorded source), so explain has no such unit; with it, the
        // record is read and its problem is the run's.
        Assert.Contains("no unit is named 'Uses.Same'", without, StringComparison.Ordinal);
        Assert.DoesNotContain("older Warrant.Build", without, StringComparison.Ordinal);
        Assert.Contains("WRT0012", with, StringComparison.Ordinal);
        Assert.Contains("warrant.source was written by an older Warrant.Build", with, StringComparison.Ordinal);
    }

    [Fact]
    public void AnUnreadableBuildFileIsDeclined()
    {
        var project = Project(Failing);
        var obj = Directory.CreateDirectory(Path.Combine(project, "obj", "Debug", "net10.0")).FullName;
        File.WriteAllLines(Path.Combine(obj, ExplainCommand.BuildFileName), ["warrant-explain 2"]);

        var (code, output) = Explain(["AlwaysLarger", "--project-dir", project]);

        Assert.Equal(2, code);
        Assert.Contains("is not a warrant.explain this Warrant can read", output, StringComparison.Ordinal);
    }

    [Fact]
    public async Task OutAndReportThroughTheServerWriteTheFilesAnInProcessRunWritesAndTheServerKeepsTheReport()
    {
        await using var server = new TestServer();
        using var source = new SourceDirectory(Failing);
        string Out(string name) => Path.Combine(_root, name);
        Directory.CreateDirectory(_root);

        var (offCode, off) = server.Verify([source.Path, "--server", "off", "--out", Out("off.ndjson"), "--report", Out("off")]);
        var (autoCode, auto) = server.Verify([source.Path, "--server", "auto", "--out", Out("auto.ndjson"), "--report", Out("auto")]);

        Assert.Equal(1, offCode);
        Assert.Equal(offCode, autoCode);
        Assert.EndsWith("[server]\n", auto, StringComparison.Ordinal);
        Assert.Equal(File.ReadAllBytes(Out("off.ndjson")), File.ReadAllBytes(Out("auto.ndjson")));
        Assert.Equal(File.ReadAllText(Path.Combine(Out("off"), "report.json")), File.ReadAllText(Path.Combine(Out("auto"), "report.json")));
        Assert.Equal(File.ReadAllText(Path.Combine(Out("off"), "report.md")), File.ReadAllText(Path.Combine(Out("auto"), "report.md")));
        Assert.Contains("wrote the bundle and ", auto, StringComparison.Ordinal);
        Assert.Equal(0, global::Cli.Run(["check", Out("auto.ndjson"), "--quiet"]));

        // The server kept the run's JSON report for the project directory.
        using var output = new StringWriter { NewLine = "\n" };
        Assert.Equal(0, ServerCommand.Run(["report", source.Path], output, output, server.Settings));
        Assert.Equal(File.ReadAllText(Path.Combine(Out("auto"), "report.json")), output.ToString());
        using var none = new StringWriter { NewLine = "\n" };
        Assert.Equal(1, ServerCommand.Run(["report", _root], none, none, server.Settings));
        Assert.Contains("has no report for", none.ToString(), StringComparison.Ordinal);
    }
}
