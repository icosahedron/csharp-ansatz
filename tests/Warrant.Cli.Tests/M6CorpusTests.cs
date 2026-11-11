using System.Text.RegularExpressions;

namespace Warrant.Cli.Tests;

/// <summary>
/// <c>warrant verify</c> on the M6 corpus (plan M6 U11, as amended by #167, and U20), in-process with no server:
/// contracts proved by the default procedure with no script, design §5.2's ProcessPayment among them with its store as a
/// hypothesis, and refuted members reported as WRT0001 at each failing VC's operation, starting with its kind (#90).
/// </summary>
public sealed class M6CorpusTests
{
    private static readonly string Corpus = Path.Combine(AppContext.BaseDirectory, "corpus", "m6");

    [Fact]
    public void TheAcceptedMembersAreProvedAndProcessPaymentsReportIsTheCheckedInOne()
    {
        var accepted = Path.Combine(Corpus, "accepted");
        var reportDir = Path.Combine(Path.GetTempPath(), "warrant-m6-report-" + Guid.NewGuid().ToString("N"));
        try
        {
            var (code, output) = Verify(accepted, "--server", "off", "--report", reportDir);
            Assert.True(code == 0, output);
            Assert.Matches(@"(?m)^  Corpus\.M6\.Contracts\.Capped\(int\) +translated$", output);
            Assert.Matches(@"(?m)^  Corpus\.M6\.Payments\.PaymentService\.ProcessPayment\(int\) +translated$", output);
            Assert.DoesNotContain(": error ", output, StringComparison.Ordinal);

            // M6 U20: the report the CLI writes, from the wire outcomes. Its kernel and bundle names are the run's, and its
            // paths are relative to the verified directory, where the checked-in block (the engine's, ReportTests) names
            // them relative to the corpus.
            var markdown = File.ReadAllText(Path.Combine(reportDir, "report.md")).ReplaceLineEndings("\n");
            var block = Block(markdown, "Corpus.M6.Payments.PaymentService.ProcessPayment(int) ");
            block = Regex.Replace(block, @"\(kernel: [^,]*, bundle: [^)]*\)", "(kernel: Warrant test, bundle: warrant-semantics test)");
            block = block.Replace("(the call at Payments.cs:", "(the call at accepted/Payments.cs:", StringComparison.Ordinal);
            var expected = File.ReadAllText(Path.Combine(Corpus, "ProcessPayment.report.txt")).ReplaceLineEndings("\n");
            Assert.Equal(expected, block);
        }
        finally
        {
            if (Directory.Exists(reportDir))
            {
                Directory.Delete(reportDir, recursive: true);
            }
        }
    }

    /// <summary>A unit's block of a Markdown report: its line and its indented lines.</summary>
    private static string Block(string markdown, string head)
    {
        var lines = markdown.Split('\n');
        int start = Array.FindIndex(lines, l => l.StartsWith(head, StringComparison.Ordinal));
        Assert.True(start >= 0, markdown);
        int end = start + 1;
        while (end < lines.Length && lines[end].StartsWith(' '))
        {
            end++;
        }
        return string.Join('\n', lines[start..end]) + "\n";
    }

    [Fact]
    public void TheRefutedMembersFailAtTheirOperationWithTheirKind()
    {
        var dir = Path.Combine(Corpus, "refuted");
        var (code, output) = Verify(dir, "--server", "off");
        Assert.Equal(1, code);
        // Ratio's division may divide by zero and may overflow: two diagnostics at its one line.
        var effects = Regex.Escape(Path.Combine(dir, "Effects.cs"));
        Assert.Matches($@"(?m)^{effects}\(10,\d+\): error WRT0001: The contract of '[^']*Ratio[^']*' could not be proved: division by zero: ", output);
        Assert.Matches($@"(?m)^{effects}\(10,\d+\): error WRT0001: The contract of '[^']*Ratio[^']*' could not be proved: overflow in a checked operation: ", output);
        var nullables = Regex.Escape(Path.Combine(dir, "Nullables.cs"));
        Assert.Matches($@"(?m)^{nullables}\(25,\d+\): error WRT0001: The contract of '[^']*Unchecked[^']*' could not be proved: null passed where a non-null value is required: ", output);
    }

    private static (int Code, string Output) Verify(params string[] args)
    {
        using var output = new StringWriter { NewLine = "\n" };
        var code = VerifyCommand.Run(args, output, output);
        return (code, output.ToString());
    }
}
