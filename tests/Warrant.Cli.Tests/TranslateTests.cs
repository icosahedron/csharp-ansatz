using System.Text.RegularExpressions;
using Warrant.Engine;

namespace Warrant.Cli.Tests;

/// <summary><c>warrant translate</c> (docs/m4/07; plan U11, KTD16), run in-process.</summary>
public sealed partial class TranslateTests
{
    private static readonly string Corpus = Path.Combine(AppContext.BaseDirectory, "corpus", "m4");

    [Fact]
    public void AcceptedExitsZeroWithOneLinePerMember()
    {
        var (code, output) = Translate(Path.Combine(Corpus, "accepted"));
        Assert.True(code == 0, output);
        Assert.Matches(@"(?m)^  Claims\.Payments\.Validate\(Claims\.Payment\) +translated$", output);
        Assert.Matches(@"(?m)^  Claims\.Payments\.RejectsZero\(\) +proved \(rfl\)$", output);
        Assert.Matches(@"(?m)^  Claims\.Payments\.RejectsProcessed\(\) +proved \(decide\)$", output);
        Assert.DoesNotContain(": error ", output, StringComparison.Ordinal);
    }

    [Fact]
    public void RefutedExitsOneWithWrt0001QuotingTheClaimAndTheValues()
    {
        var dir = Path.Combine(Corpus, "refuted");
        var (code, output) = Translate(dir);
        Assert.Equal(1, code);
        var file = Regex.Escape(Path.Combine(dir, "Increment.cs"));
        Assert.Matches(
            $@"(?m)^{file}\(12,\d+\): error WRT0001: Theorem 'Increments\.NeverWraps\(\)' is false\.\n"
            + @"  Claim:  Increment\(int\.MaxValue\) > int\.MaxValue\n"
            + @"  Values: Increment\(int\.MaxValue\) = -2147483648, int\.MaxValue = 2147483647\n",
            output);
        Assert.Contains("  Values: Increment(2) = 3, 4 = 4\n", output, StringComparison.Ordinal);
        Assert.Matches(@"(?m)^  Corpus\.Refuted\.Increments\.NeverWraps\(\) +false$", output);
    }

    [Fact]
    public void RejectedExitsOneWithDiagnosticsInCompilerFormat()
    {
        var (code, output) = Translate(Path.Combine(Corpus, "rejected"));
        Assert.Equal(1, code);
        var diagnostics = CompilerFormat().Matches(output);
        Assert.NotEmpty(diagnostics);
        Assert.Contains(diagnostics, m => m.Groups["code"].Value == "WRT0002");
    }

    [Fact]
    public void OutWritesTheBundleThenTheAdmittedDeclarationsAndReportWritesMarkdown()
    {
        var work = Directory.CreateTempSubdirectory("warrant-cli-");
        try
        {
            var ndjson = Path.Combine(work.FullName, "m4.ndjson");
            var report = Path.Combine(work.FullName, "m4.md");
            var (code, output) = Translate(Path.Combine(Corpus, "accepted"), "--out", ndjson, "--report", report);
            Assert.True(code == 0, output);

            var bundle = Lean4Export.Lean4Export.ReadFile(Path.Combine(AppContext.BaseDirectory, SemanticsBundle.FileName));
            var written = Lean4Export.Lean4Export.ReadFile(ndjson);
            Assert.True(written.Declarations.Count > bundle.Declarations.Count);
            Assert.Contains(written.Declarations.SelectMany(d => d.Constants), c => c.Name.ToString() == "Cs.Claims.Payments.RejectsZero");

            var markdown = File.ReadAllText(report);
            Assert.StartsWith("# Assumption report", markdown, StringComparison.Ordinal);
            Assert.Contains("    - p is not null\n", markdown, StringComparison.Ordinal);
        }
        finally
        {
            work.Delete(recursive: true);
        }
    }

    /// <summary>
    /// The M6 corpus holds members translation cannot take until M6 U10, U19 and U21 (contracts, dependencies, decimal), so the CLI tests must not run it before U11 adds
    /// its proof outcomes (tests/corpus/m6/README.md); this pins that it is not copied here.
    /// </summary>
    [Fact]
    public void TheM6CorpusIsNotRunHereYet()
    {
        Assert.False(Directory.Exists(Path.Combine(AppContext.BaseDirectory, "corpus", "m6")));
    }

    [Fact]
    public void TheBundleIsCopiedBesideTheCli()
    {
        var cli = typeof(TranslateCommand).Assembly.Location;
        Assert.Equal("warrant.dll", Path.GetFileName(cli));
        Assert.True(File.Exists(Path.Combine(Path.GetDirectoryName(cli)!, SemanticsBundle.FileName)));
    }

    [Fact]
    public void CompileErrorsArePrintedAndExitOne()
    {
        var work = Directory.CreateTempSubdirectory("warrant-cli-");
        try
        {
            File.WriteAllText(Path.Combine(work.FullName, "Broken.cs"), "public static class C { public static int F() => missing; }\n");
            var (code, output) = Translate(work.FullName);
            Assert.Equal(1, code);
            Assert.Matches(@"(?m)Broken\.cs\(1,\d+\): error CS0103: ", output);
        }
        finally
        {
            work.Delete(recursive: true);
        }
    }

    [Fact]
    public void AMissingDirectoryIsDeclined()
    {
        var (code, _) = Translate(Path.Combine(Corpus, "no-such-directory"));
        Assert.Equal(2, code);
    }

    private static (int Code, string Output) Translate(params string[] args)
    {
        using var output = new StringWriter { NewLine = "\n" };
        var code = TranslateCommand.Run(args, output, output);
        return (code, output.ToString());
    }

    [GeneratedRegex(@"(?m)^\S.*\.cs\(\d+,\d+\): (error|warning) (?<code>[A-Z]+\d{4}): \S.*$")]
    private static partial Regex CompilerFormat();
}
