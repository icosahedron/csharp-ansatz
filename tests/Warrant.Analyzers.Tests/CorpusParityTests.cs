using Warrant.Extraction;
using Warrant.TestSupport;

namespace Warrant.Analyzers.Tests;

/// <summary>
/// The IDE says what the build says (M5b U15, R18): on every compilation of the M4, M5a and M6 corpora, the analyzer's
/// diagnostics are a full extraction's, with the same ID, span, severity and message. The extraction is the active
/// configuration's, which is what the analyzer sees; the <c>#if</c> combination check is the build's alone.
/// </summary>
public sealed class CorpusParityTests
{
    public static TheoryData<string, string> Compilations()
    {
        var data = new TheoryData<string, string>();
        foreach (var set in new[] { CorpusSet.M4, CorpusSet.M5a, CorpusSet.M6 })
        {
            foreach (var name in set.Names)
            {
                data.Add(set.Name, name);
            }
        }
        return data;
    }

    [Theory]
    [MemberData(nameof(Compilations))]
    public async Task TheAnalyzerReportsWhatExtractionReportsAtTheSamePlace(string set, string name)
    {
        var corpus = set switch { "m4" => CorpusSet.M4, "m5a" => CorpusSet.M5a, _ => CorpusSet.M6 };
        var compilation = corpus.Compile(name);
        var extraction = Extractor.Extract(compilation, new ExtractionOptions { BuildDefines = true });
        Assert.False(extraction.HasCompileErrors);
        var expected = extraction.Diagnostics
            .Select(d => AnalyzerHarness.Line(
                d.Location!.Path, d.Location.StartLine, d.Location.StartColumn, d.Location.EndLine, d.Location.EndColumn,
                d.Severity == ExtractionSeverity.Warning ? "warning" : "error", d.Id, d.Message))
            .Order(StringComparer.Ordinal)
            .ToList();

        var (lines, exceptions) = await AnalyzerHarness.Run(compilation);

        Assert.Empty(exceptions);
        Assert.Equal(expected, lines.Order(StringComparer.Ordinal).ToList());
        if (name == "rejected")
        {
            Assert.NotEmpty(lines);
        }
    }
}
