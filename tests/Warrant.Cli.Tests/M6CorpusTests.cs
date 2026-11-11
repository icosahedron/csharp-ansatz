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

            // M6 U14: a method that throws on every path, whose report lists the throw.
            block = Block(markdown, "Corpus.M6.Effects.Closed(int) ");
            block = Regex.Replace(block, @"\(kernel: [^,]*, bundle: [^)]*\)", "(kernel: Warrant test, bundle: warrant-semantics test)");
            block = block.Replace("(the throw at Effects.cs:", "(the throw at accepted/Effects.cs:", StringComparison.Ordinal);
            Assert.Equal(File.ReadAllText(Path.Combine(Corpus, "Closed.report.txt")).ReplaceLineEndings("\n"), block);
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

        // M6 U14: each refuted contract at its line, with its kind (tests/corpus/m6/expected.json).
        var contracts = Regex.Escape(Path.Combine(dir, "Contracts.cs"));
        Assert.Matches($@"(?m)^{contracts}\(15,\d+\): error WRT0001: The contract of 'Contracts\.Ratio\(int, int\)' could not be proved: overflow in a checked operation: ", output);
        Assert.Matches($@"(?m)^{contracts}\(20,\d+\): error WRT0001: The contract of 'Contracts\.Neg\(int\)' could not be proved: overflow in a checked operation: ", output);
        Assert.Matches($@"(?m)^{contracts}\(30,\d+\): error WRT0001: The contract of 'Contracts\.ShareOfNothing\(\)' could not be proved: precondition of a callee at this call: ", output);
        Assert.Matches($@"(?m)^{contracts}\(35,\d+\): error WRT0001: The contract of 'Contracts\.Twice\(int\)' could not be proved: postcondition of the method: ", output);
        Assert.Matches($@"(?m)^{contracts}\(52,\d+\): error WRT0001: The contract of 'Contracts\.Asserted\(int, int\)' could not be proved: Spec\.Assert: ", output);
        Assert.Matches($@"(?m)^{contracts}\(60,\d+\): error WRT0001: The contract of 'Contracts\.Impossible\(int\)' could not be proved: The contract is unsatisfiable: ", output);
        // #182: under Spec.NoThrow a reachable explicit throw fails the build at the throw.
        Assert.Matches($@"(?m)^{contracts}\(72,\d+\): error WRT0001: The contract of 'Contracts\.QuotientOfAny\(int, int\)' could not be proved: an explicit throw is reachable under the Requires \(Spec\.NoThrow\): ", output);
        // A [ProofFor] script that fails is reported at the step that failed, as a theorem's script is.
        Assert.Matches($@"(?m)^{contracts}\(47,\d+\): error WRT0001: The contract of 'Contracts\.Kept\(int\)' could not be proved: omega could not prove the goal:", output);
        var dependencies = Regex.Escape(Path.Combine(dir, "Dependencies.cs"));
        Assert.Matches($@"(?m)^{dependencies}\(35,\d+\): error WRT0001: The contract of 'Lookups\.Neighbour\(int\)' could not be proved: postcondition of the method: ", output);
        Assert.Matches($@"(?m)^{dependencies}\(43,\d+\): error WRT0001: The contract of 'Lookups\.Saved\(Payment\)' could not be proved: postcondition of the method: ", output);
        Assert.Matches($@"(?m)^{dependencies}\(52,\d+\): error WRT0001: The contract of 'Lookups\.Twice\(int\)' could not be proved: postcondition of the method: ", output);
        Assert.Matches($@"(?m)^{dependencies}\(59,\d+\): error WRT0001: The contract of 'Lookups\.TwiceScripted\(int\)' could not be proved: unsolved goals", output);
        Assert.Matches($@"(?m)^{dependencies}\(82,\d+\): error WRT0001: The contract of 'ICounter\.Count\(\)' could not be proved: The contract is unsatisfiable: ", output);
        // #228: an awaited call to a verified method is checked against its Spec.Requires like any other call.
        Assert.Matches($@"(?m)^{dependencies}\(107,\d+\): error WRT0001: The contract of 'Steps\.Run\(int\)' could not be proved: precondition of a callee at this call: ", output);
    }

    private static (int Code, string Output) Verify(params string[] args)
    {
        using var output = new StringWriter { NewLine = "\n" };
        var code = VerifyCommand.Run(args, output, output);
        return (code, output.ToString());
    }
}
