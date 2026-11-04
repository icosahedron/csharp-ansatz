using System.Globalization;
using System.Text.RegularExpressions;
using Basic.Reference.Assemblies;
using Warrant.Engine;
using Warrant.Frontend;

namespace Warrant.Cli.Tests;

/// <summary>
/// <c>warrant verify</c> (plan M5a U12, KTD20, KTD21, KTD24; docs/m5a/07), run in-process. <c>cscargs/sample.csc.args</c>
/// is the Extraction tests' argument file (<c>@(CscCommandLineArgs)</c> of a net10.0 library with <c>/define:DEBUG</c> and
/// <c>/langversion:14</c>) with <c>/checked-</c>, the SDK's default, so arithmetic wraps as the M5a exit example needs;
/// its reference pack is written to <c>refs\</c> here.
/// </summary>
public sealed class VerifyTests : IDisposable
{
    private static readonly string Corpus = Path.Combine(AppContext.BaseDirectory, "corpus", "m4");

    private readonly string project = Path.Combine(Path.GetTempPath(), "warrant-verify-" + Guid.NewGuid().ToString("N"));

    public VerifyTests()
    {
        var fixture = Path.Combine(AppContext.BaseDirectory, "cscargs");
        foreach (var file in Directory.EnumerateFiles(fixture, "*", SearchOption.AllDirectories))
        {
            var target = Path.Combine(project, Path.GetRelativePath(fixture, file));
            Directory.CreateDirectory(Path.GetDirectoryName(target)!);
            File.Copy(file, target);
        }
        var refs = Directory.CreateDirectory(Path.Combine(project, "refs")).FullName;
        foreach (var info in Net100.ReferenceInfos.All)
        {
            File.WriteAllBytes(Path.Combine(refs, info.FileName), info.ImageBytes);
        }
        // The Warrant package from the image the front end embeds: a Warrant.dll file must not sit beside warrant.dll (KTD4).
        using var image = typeof(CompilationFactory).Assembly.GetManifestResourceStream("Warrant.dll")!;
        using var dll = File.Create(Path.Combine(refs, "Warrant.dll"));
        image.CopyTo(dll);
    }

    public void Dispose() => Directory.Delete(project, recursive: true);

    private string ArgsFile => Path.Combine(project, "sample.csc.args");

    private string SourcePath => Path.Combine(project, "src", "C.cs");

    private void Write(string source)
    {
        Directory.CreateDirectory(Path.GetDirectoryName(SourcePath)!);
        File.WriteAllText(SourcePath, "using Warrant;\n" + source);
    }

    private (int Code, string Output) VerifyArgs(params string[] options) =>
        Verify(["--csc-args", ArgsFile, "--project-dir", project, .. options]);

    [Fact]
    public void AnIfDebugMethodVerifiesUnderTheBuildsDefinesWithoutTheCombinationCheck()
    {
        Write("""
            public static class C
            {
                [Verified]
                public static int F() =>
            #if DEBUG
                    1;
            #else
                    2;
            #endif

                [Theorem] static Proof IsOne() => Prove.That(F() == 1);
            }
            """);
        var (code, output) = VerifyArgs();
        Assert.True(code == 0, output);
        Assert.Matches(@"(?m)^  C\.F\(\) +translated$", output);
        Assert.Matches(@"(?m)^  C\.IsOne\(\) +proved \(rfl\)$", output);
        Assert.DoesNotContain("WRT0002", output, StringComparison.Ordinal);
        Assert.EndsWith("Warrant: 2 verified units, 1 theorems proved, 0 not proved.\n", output, StringComparison.Ordinal);
    }

    [Fact]
    public void ACSharp14FeatureInUnverifiedCodeCompilesAndVerifies()
    {
        Write("""
            public static class Extensions
            {
                extension(int x)
                {
                    public int Doubled => x * 2;
                }
            }
            public static class C
            {
                [Verified] public static int Same(int x) => x;
                public static int G(int x) => x.Doubled;
                [Theorem] static Proof Two() => Prove.That(Same(2) == 2);
            }
            """);
        var (code, output) = VerifyArgs();
        Assert.True(code == 0, output);
        Assert.Matches(@"(?m)^  C\.Two\(\) +proved \(", output);
    }

    [Fact]
    public void TheTextFormatNamesTheTheoremWithItsParameterTypesAndShowsTheGoal()
    {
        Write("""
            public static class Increments
            {
                [Verified] public static int Increment(int x) => x + 1;
                [Theorem] static Proof AlwaysLarger(int x) => Prove.That(Increment(x) > x);
            }
            """);
        var (code, output) = VerifyArgs();
        Assert.Equal(1, code);
        var file = Regex.Escape(SourcePath);
        Assert.Matches(
            $@"(?m)^{file}\(5,\d+\): error WRT0001: Theorem 'Increments\.AlwaysLarger\(int\)' could not be proved: unsolved goals\. "
            + @"Counterexample: x = 2147483647\.\n  x : Int32\n  ⊢ Increment x > x\n",
            output);
        Assert.EndsWith("Warrant: 2 verified units, 0 theorems proved, 1 not proved.\n", output, StringComparison.Ordinal);
    }

    [Fact]
    public void TheMsbuildFormatWritesOneRecordPerDiagnosticWithTheGoalAndTheTheoremsLocation()
    {
        Write("""
            public static class Increments
            {
                [Verified] public static int Increment(int x) => x + 1;
                [Theorem] static Proof AlwaysLarger(int x) => Prove.That(Increment(x) > x);
                [Theorem] static Proof Mismatch(int a) => Prove.That(a == a).By(Tactic.Exact(Lean.Const("Nat.zero")));
            }
            """);
        var (code, output) = VerifyArgs("--format", "msbuild");
        Assert.Equal(1, code);
        var records = output.Split('\n').Where(l => l.StartsWith("WRT1\t", StringComparison.Ordinal)).Select(l => l.Split('\t')).ToList();
        Assert.All(records, r => Assert.Equal(10, r.Length));

        var diagnostics = records.Where(r => r[1] == "diag").ToList();
        Assert.Equal(2, diagnostics.Count);
        var larger = diagnostics.Single(r => r[9].Contains("AlwaysLarger", StringComparison.Ordinal));
        // The theorem's location: its name on line 5 (after the `using Warrant;` line Write adds).
        var name = (File.ReadAllLines(SourcePath)[4].IndexOf("AlwaysLarger", StringComparison.Ordinal) + 1).ToString(CultureInfo.InvariantCulture);
        Assert.Equal(["error", "WRT0001", SourcePath, "5", name, "5"], larger[2..8]);
        var message = Unescape(larger[9]);
        Assert.Equal(
            "Theorem 'Increments.AlwaysLarger(int)' could not be proved: unsolved goals. Counterexample: x = 2147483647.\n"
            + "x : Int32\n⊢ Increment x > x",
            message);

        // The goal block follows its diagnostic as one record, newlines escaped.
        var goal = records[records.IndexOf(larger) + 1];
        Assert.Equal(["goal", "info", "", "", "0", "0", "0", "0", @"x : Int32\n⊢ Increment x > x"], goal[1..]);

        // A failing tactic call is the location when the engine reports one: line 6, at `Tactic.Exact(...)`.
        var mismatch = diagnostics.Single(r => r[9].Contains("Mismatch", StringComparison.Ordinal));
        var line6 = File.ReadAllLines(SourcePath)[5];
        Assert.Equal(["6", (line6.IndexOf("Tactic.Exact", StringComparison.Ordinal) + 1).ToString(CultureInfo.InvariantCulture)], mismatch[5..7]);
        Assert.StartsWith(
            "Theorem 'Increments.Mismatch(int)' could not be proved: Tactic `exact` failed: type mismatch\n",
            Unescape(mismatch[9]),
            StringComparison.Ordinal);

        Assert.Equal(["summary", "info", "", "", "0", "0", "0", "0", "Warrant: 3 verified units, 0 theorems proved, 2 not proved."], records[^1][1..]);
        Assert.DoesNotContain("\nWarrant: ", output, StringComparison.Ordinal);
    }

    [Fact]
    public void AllProvedExitsZero()
    {
        Write("""
            public static class C
            {
                [Verified] public static int Same(int x) => x;
                [Theorem] static Proof Refl(int a) => Prove.That(a == a).By(Tactic.Exact(Lean.Const("rfl")));
            }
            """);
        var (code, output) = VerifyArgs();
        Assert.True(code == 0, output);
        Assert.DoesNotContain(": error ", output, StringComparison.Ordinal);
    }

    [Fact]
    public void OnlyWarningsExitsZero()
    {
        Write("""
            [Closed] public enum Phase { Draft, Open }
            public static class C
            {
                public static Phase Cast(int x) => (Phase)x;
                [Verified] public static int Same(int x) => x;
            }
            """);
        var (code, output) = VerifyArgs();
        Assert.True(code == 0, output);
        Assert.Matches(@"(?m)C\.cs\(5,\d+\): warning WRT0008: ", output);

        var (msbuildCode, records) = VerifyArgs("--format", "msbuild");
        Assert.Equal(0, msbuildCode);
        Assert.Contains("WRT1\tdiag\twarning\tWRT0008\t", records, StringComparison.Ordinal);
    }

    [Fact]
    public void AMissingArgsFileExitsTwo()
    {
        var (code, output) = Verify("--csc-args", Path.Combine(project, "no-such.args"));
        Assert.Equal(2, code);
        Assert.Contains("not found", output, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData]
    [InlineData("--format", "xml")]
    [InlineData("--kernel-fuel", "lots")]
    [InlineData("--timeout")]
    public void BadArgumentsExitTwo(params string[] args)
    {
        var (code, _) = Verify(args.Length == 0 ? [] : ["--csc-args", ArgsFile, .. args]);
        Assert.Equal(2, code);
    }

    [Fact]
    public void ACompilationThatNeedsASourceGeneratorReportsWrt0012NamingTheMissingSymbols()
    {
        Write("""
            public static class C
            {
                [Verified] public static int F(int x) => x;
                public static object Settings() => new GeneratedSettings();
            }
            """);
        var (code, output) = VerifyArgs();
        Assert.Equal(1, code);
        Assert.Matches(@"(?m)C\.cs\(5,\d+\): error WRT0012: .*missing: GeneratedSettings\.$", output);

        var (msbuildCode, records) = VerifyArgs("--format", "msbuild");
        Assert.Equal(1, msbuildCode);
        Assert.Contains($"WRT1\tdiag\terror\tWRT0012\t{SourcePath}\t5\t", records, StringComparison.Ordinal);
    }

    [Fact]
    public void KeepingTheConditionalCheckRejectsAMethodThatDiffersUnderNet8()
    {
        Write("""
            public static class C
            {
                [Verified]
                public static int F()
                {
            #if NET8_0
                    return 8;
            #else
                    return 10;
            #endif
                }
            }
            """);
        var (plain, plainOutput) = VerifyArgs();
        Assert.True(plain == 0, plainOutput);

        var (code, output) = VerifyArgs("--keep-conditional-check");
        Assert.Equal(1, code);
        Assert.Matches(@"(?m)C\.cs\(\d+,\d+\): error WRT0002: C\.F\(\) translates differently depending on which of .*NET8_0", output);
    }

    [Fact]
    public void BudgetOptionsReachTheEngine()
    {
        Write("""
            public static class C
            {
                [Theorem] static Proof Refl(int a) => Prove.That(a == a).By(Tactic.Exact(Lean.Const("rfl")));
            }
            """);
        var (code, output) = VerifyArgs("--tactic-fuel", "1");
        Assert.Equal(1, code);
        Assert.Matches(@"(?m)error WRT0006: Theorem 'C\.Refl\(int\)' was not decided: .*tactic fuel", output);

        (code, output) = VerifyArgs("--timeout", "0");
        Assert.Equal(1, code);
        Assert.Contains("error WRT0006: ", output, StringComparison.Ordinal);

        (code, output) = VerifyArgs("--kernel-fuel", "100000000", "--tactic-fuel", "910", "--timeout", "30");
        Assert.True(code == 0, output);
    }

    [Fact]
    public void OutWritesNdjsonThatCheckAcceptsAndReportWritesBothReports()
    {
        Write("""
            public static class C
            {
                [Verified] public static int Same(int x) => x;
                [Theorem] static Proof Refl(int a) => Prove.That(Same(a) == a).By(Tactic.Unfold(nameof(Same)), Tactic.Exact(Lean.Const("rfl")));
            }
            """);
        var ndjson = Path.Combine(project, "out.ndjson");
        var reports = Path.Combine(project, "reports");
        var (code, output) = VerifyArgs("--out", ndjson, "--report", reports);
        Assert.True(code == 0, output);
        Assert.Equal(0, global::Cli.Run(["check", ndjson, "--quiet"]));
        Assert.StartsWith("# Assumption report", File.ReadAllText(Path.Combine(reports, "report.md")), StringComparison.Ordinal);
        var json = Warrant.Engine.Reports.JsonReport.Read(File.ReadAllText(Path.Combine(reports, "report.json")));
        Assert.Contains(json.Units, u => u.Key == "M:C.Refl(System.Int32)");
    }

    [Theory]
    [InlineData("accepted")]
    [InlineData("refuted")]
    [InlineData("rejected")]
    public void TheDirectoryModeGivesTheSameResultsAsTranslate(string compilation)
    {
        var dir = Path.Combine(Corpus, compilation);
        var (verifyCode, verify) = Verify(dir);
        var (translateCode, translate) = Translate(dir);
        Assert.Equal(translateCode, verifyCode);
        // Everything between the first line (what is read) and the summary line: unit lines and diagnostics.
        static string[] Body(string text) => text.TrimEnd('\n').Split('\n')[1..^1];
        Assert.Equal(Body(translate), Body(verify));
    }

    [Fact]
    public void AMissingOrMismatchedSidecarIsDeclined()
    {
        var bundles = Directory.CreateDirectory(Path.Combine(project, "bundle")).FullName;
        var bundle = Path.Combine(bundles, SemanticsBundle.FileName);
        File.Copy(Path.Combine(AppContext.BaseDirectory, SemanticsBundle.FileName), bundle);
        Write("public static class C { }");

        var (code, output) = VerifyArgs("--bundle", bundle);
        Assert.Equal(2, code);
        Assert.Contains("attribute sidecar", output, StringComparison.Ordinal);

        // The real sidecar beside a different bundle file: its recorded SHA-256 does not match.
        File.Copy(Path.Combine(AppContext.BaseDirectory, VerifyCommand.SidecarFileName), Path.Combine(bundles, VerifyCommand.SidecarFileName));
        File.AppendAllText(bundle, "x");
        (code, output) = VerifyArgs("--bundle", bundle);
        Assert.Equal(2, code);
        Assert.Contains("SHA-256", output, StringComparison.Ordinal);
    }

    [Fact]
    public void TheSidecarIsCopiedBesideTheCli()
    {
        var cli = Path.GetDirectoryName(typeof(VerifyCommand).Assembly.Location)!;
        Assert.True(File.Exists(Path.Combine(cli, VerifyCommand.SidecarFileName)));
    }

    private static string Unescape(string field) =>
        field.Replace(@"\\", "\0", StringComparison.Ordinal).Replace(@"\n", "\n", StringComparison.Ordinal)
            .Replace(@"\r", "\r", StringComparison.Ordinal).Replace(@"\t", "\t", StringComparison.Ordinal).Replace("\0", @"\", StringComparison.Ordinal);

    private static (int Code, string Output) Verify(params string[] args)
    {
        using var output = new StringWriter { NewLine = "\n" };
        var code = VerifyCommand.Run(args, output, output);
        return (code, output.ToString());
    }

    private static (int Code, string Output) Translate(params string[] args)
    {
        using var output = new StringWriter { NewLine = "\n" };
        var code = TranslateCommand.Run(args, output, output);
        return (code, output.ToString());
    }
}
