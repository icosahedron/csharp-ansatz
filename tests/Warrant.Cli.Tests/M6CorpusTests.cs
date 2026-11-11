using System.Text.RegularExpressions;

namespace Warrant.Cli.Tests;

/// <summary>
/// <c>warrant verify</c> on the M6 corpus's members without dependencies (plan M6 U11, as amended by #167), in-process
/// with no server: contracts proved by the default procedure with no script, and refuted members reported as WRT0001 at
/// each failing VC's operation, starting with its kind (#90). The files with dependencies come with U19 and U20.
/// </summary>
public sealed class M6CorpusTests
{
    private static readonly string Corpus = Path.Combine(AppContext.BaseDirectory, "corpus", "m6");

    [Fact]
    public void TheAcceptedMembersWithoutDependenciesAreProved()
    {
        var (code, output) = Verify(Path.Combine(Corpus, "accepted"), "--server", "off");
        Assert.True(code == 0, output);
        Assert.Matches(@"(?m)^  Corpus\.M6\.Contracts\.Capped\(int\) +translated$", output);
        Assert.DoesNotContain(": error ", output, StringComparison.Ordinal);
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
