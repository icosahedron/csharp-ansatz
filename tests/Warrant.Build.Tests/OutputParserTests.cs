namespace Warrant.Build.Tests;

using Warrant.Build;

public sealed class OutputParserTests
{
    [Fact]
    public void ADiagnosticRecordCarriesEveryField()
    {
        var record = OutputParser.Parse("WRT1\tdiag\terror\tWRT0001\tsrc/Increments.cs\t12\t5\t12\t30\tnot proved\\n⊢ x + 1 > x");

        Assert.Equal(
            new OutputRecord(RecordKind.Diagnostic, RecordSeverity.Error, "WRT0001", "src/Increments.cs", 12, 5, 12, 30, "not proved\n⊢ x + 1 > x"),
            record);
    }

    [Theory]
    [InlineData("goal", "info", "Goal", "Info")]
    [InlineData("summary", "info", "Summary", "Info")]
    [InlineData("diag", "warning", "Diagnostic", "Warning")]
    [InlineData("diag", "info", "Diagnostic", "Info")]
    public void EveryKindAndSeverityParses(string kind, string severity, string expectedKind, string expectedSeverity)
    {
        var record = OutputParser.Parse($"WRT1\t{kind}\t{severity}\t\t\t0\t0\t0\t0\tWarrant: 1 verified unit");

        Assert.NotNull(record);
        Assert.Equal(expectedKind, record.Kind.ToString());
        Assert.Equal(expectedSeverity, record.Severity.ToString());
        Assert.Equal("", record.Code);
        Assert.Equal("", record.File);
        Assert.Equal((0, 0, 0, 0), (record.Line, record.Column, record.EndLine, record.EndColumn));
        Assert.Equal("Warrant: 1 verified unit", record.Message);
    }

    [Theory]
    [InlineData(@"a\\b", @"a\b")]
    [InlineData(@"a\nb", "a\nb")]
    [InlineData(@"a\rb", "a\rb")]
    [InlineData(@"a\tb", "a\tb")]
    [InlineData(@"\\n", @"\n")]
    [InlineData(@"\\\n", "\\\n")]
    [InlineData(@"C:\x", @"C:\x")]
    [InlineData(@"end\", @"end\")]
    [InlineData("no escapes, ⊢ ≤", "no escapes, ⊢ ≤")]
    public void MessagesAreUnescaped(string escaped, string expected)
    {
        var record = OutputParser.Parse($"WRT1\tgoal\tinfo\t\t\t0\t0\t0\t0\t{escaped}");

        Assert.Equal(expected, record?.Message);
    }

    [Theory]
    [InlineData("Warrant: 3 verified units, 2 theorems proved, 0 not proved.")]
    [InlineData("")]
    [InlineData("WRT1")]
    [InlineData("WRT1 diag error WRT0001 a.cs 1 1 1 1 text")]
    [InlineData("WRT2\tdiag\terror\tWRT0001\ta.cs\t1\t1\t1\t1\ttext")]
    [InlineData(" WRT1\tdiag\terror\tWRT0001\ta.cs\t1\t1\t1\t1\ttext")]
    [InlineData("WRT1\tdiag\terror\tWRT0001\ta.cs\t1\t1\t1\ttext")]
    [InlineData("WRT1\tdiag\terror\tWRT0001\ta.cs\t1\t1\t1\t1\ttext\textra")]
    [InlineData("WRT1\tnote\terror\tWRT0001\ta.cs\t1\t1\t1\t1\ttext")]
    [InlineData("WRT1\tdiag\tfatal\tWRT0001\ta.cs\t1\t1\t1\t1\ttext")]
    [InlineData("WRT1\tdiag\terror\tWRT0001\ta.cs\tone\t1\t1\t1\ttext")]
    [InlineData("WRT1\tdiag\terror\tWRT0001\ta.cs\t-1\t1\t1\t1\ttext")]
    [InlineData("WRT1\tdiag\terror\tWRT0001\ta.cs\t\t1\t1\t1\ttext")]
    public void OtherLinesAreOrdinaryOutput(string line)
    {
        Assert.Null(OutputParser.Parse(line));
    }
}
