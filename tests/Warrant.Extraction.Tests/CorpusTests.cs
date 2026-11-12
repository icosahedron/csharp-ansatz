using System.Text.Json;
using Warrant.Extraction;
using Warrant.TestSupport;
using Warrant.Vir;

namespace Warrant.Extraction.Tests;

/// <summary>
/// Every member of every compilation of the M4, M5a and M6 corpora gets the outcome expected.json gives it, as far as
/// extraction decides it (docs/m4/02, docs/m5a/01, tests/corpus/m6/README.md).
/// </summary>
public class CorpusTests
{
    public static TheoryData<string, string> Compilations
    {
        get
        {
            var data = new TheoryData<string, string>();
            foreach (var set in Corpus.Sets)
            {
                foreach (var name in set.Names)
                {
                    data.Add(set.Name, name);
                }
            }
            return data;
        }
    }

    public static TheoryData<string, string, string> Members
    {
        get
        {
            var data = new TheoryData<string, string, string>();
            foreach (var set in Corpus.Sets)
            {
                foreach (var name in set.Names)
                {
                    foreach (var (key, _) in Corpus.Members(set, name))
                    {
                        data.Add(set.Name, name, key);
                    }
                }
            }
            return data;
        }
    }

    [Theory]
    [MemberData(nameof(Compilations))]
    public void CompilesWithoutErrors(string corpus, string compilation)
    {
        var result = Corpus.Extract(Corpus.Set(corpus), compilation);
        Assert.False(result.HasCompileErrors, string.Join("\n", result.Diagnostics.Select(d => d.Message)));
    }

    [Theory]
    [MemberData(nameof(Members))]
    public void MemberHasItsExpectedOutcome(string corpus, string compilation, string key)
    {
        var set = Corpus.Set(corpus);
        var result = Corpus.Extract(set, compilation);
        var expected = Corpus.Member(set, compilation, key);
        var outcome = expected.GetProperty("outcome").GetString();
        var unit = result.Find(key);
        var diagnostics = result.DiagnosticsFor(key);
        switch (outcome)
        {
            case "translated" or "proved" or "false" or "unproved" or "skipped":
                Assert.Empty(diagnostics);
                Assert.NotNull(unit);
                // A proof outcome is a theorem's, a recursive method's decrease obligation's, or in the M6 corpus a method's
                // contract obligation's (plan M6 U11).
                if (outcome != "translated" && !expected.TryGetProperty("recursive", out _) && corpus != "m6")
                {
                    Assert.Equal(VirUnitKind.Theorem, unit.Unit.Kind);
                }
                Assert.Equal(Strings(expected, "assumeNonNull"), Subjects(unit.Unit, VirAssumptionKind.NonNull));
                bool identity = expected.TryGetProperty("assumeIdentityEquality", out var ie) && ie.GetBoolean();
                Assert.Equal(identity, unit.Unit.Assumptions.Contains(new VirAssumption(VirAssumptionKind.ClosedEquality, key)));
                ExtractedAsExpected(set, key, expected, unit.Unit);
                break;
            case "rejected" or "warning":
                if (outcome == "rejected")
                {
                    Assert.Null(unit);
                }
                var wanted = expected.GetProperty("diagnostics").EnumerateArray()
                    .Select(d => d.GetProperty("id").GetString() + " | " + d.GetProperty("construct").GetString())
                    .OrderBy(s => s, StringComparer.Ordinal);
                var got = diagnostics.Select(d => d.Id + " | " + d.Construct).OrderBy(s => s, StringComparer.Ordinal);
                Assert.Equal(wanted, got);
                foreach (var d in diagnostics)
                {
                    var severity = d.Id == DiagnosticIds.UnnamedClosedValue ? ExtractionSeverity.Warning : ExtractionSeverity.Error;
                    Assert.Equal(severity, d.Severity);
                    Assert.NotNull(d.Location);
                }
                break;
            default:
                Assert.Fail($"Unknown outcome '{outcome}'.");
                break;
        }
    }

    /// <summary>
    /// What extraction reads for an accepted member: a theorem's parameters (one per parameter in its key) and its
    /// script (every M5a theorem has one, no M4 theorem does), and a recursive method's measure as the first statement of its body.
    /// </summary>
    private static void ExtractedAsExpected(CorpusSet set, string key, JsonElement expected, VirUnit unit)
    {
        if (unit.Kind == VirUnitKind.Theorem)
        {
            int open = key.IndexOf('(', StringComparison.Ordinal);
            int arity = open < 0 ? 0 : key.Substring(open).Split(',').Length;
            Assert.Equal(arity, unit.Params!.Count);
            bool scripted = set == CorpusSet.M5a;
            Assert.Equal(scripted, unit.Script is { Count: > 0 });
        }
        bool recursive = expected.TryGetProperty("recursive", out var r) && r.GetBoolean();
        Assert.Equal(recursive, unit.Body is BlockStmt { Stmts: [DecreasesStmt, ..] });
    }

    [Theory]
    [MemberData(nameof(Compilations))]
    public void NoDiagnosticIsUnexpected(string corpus, string compilation)
    {
        var set = Corpus.Set(corpus);
        var keys = Corpus.Members(set, compilation).Select(m => m.Key).ToHashSet(StringComparer.Ordinal);
        var unexpected = Corpus.Extract(set, compilation).Diagnostics.Where(d => d.MemberKey is null || !keys.Contains(d.MemberKey));
        Assert.Empty(unexpected);
    }

    [Theory]
    [MemberData(nameof(Compilations))]
    public void UnitsComeAfterTheirDependencies(string corpus, string compilation)
    {
        var seen = new HashSet<string>(StringComparer.Ordinal);
        foreach (var unit in Corpus.Extract(Corpus.Set(corpus), compilation).Units)
        {
            Assert.All(unit.Unit.Deps, d => Assert.Contains(d, seen));
            seen.Add(unit.Key);
        }
    }

    private const string M4VirAtVersion1 = "17845076f4fda166e0409d5d374dbfbd6a89580b26c3f8e501b8df6d6f033994";

    [Fact]
    public void EveryM4UnitsVirIsUnchangedApartFromTheVersion()
    {
        var text = new System.Text.StringBuilder();
        foreach (var name in Corpus.CompilationNames)
        {
            foreach (var unit in Corpus.Extract(name).Units)
            {
                // The VIR version and the Roslyn version that produced it are provenance; the translation is the rest.
                text.Append(VirWriter.WriteString(unit.Unit with { Vir = 1, Facts = unit.Unit.Facts with { Roslyn = "5.0.0" } })).Append('\n');
            }
        }
        var hash = Convert.ToHexStringLower(System.Security.Cryptography.SHA256.HashData(System.Text.Encoding.UTF8.GetBytes(text.ToString())));
        Assert.Equal(M4VirAtVersion1, hash);
    }

    // The M5a corpus's VIR at version 2 (M5a), pinned before VIR version 3 (M6 U6, KTD19) so a change shows here.
    private const string M5aVirAtVersion2 = "d20be30369777df2ca1c4f9e607bc2303a2e26c8714699e5433da4feba1d5525";

    [Fact]
    public void EveryM5aUnitsVirIsUnchangedApartFromTheVersion()
    {
        var text = new System.Text.StringBuilder();
        foreach (var name in CorpusSet.M5a.Names)
        {
            foreach (var unit in Corpus.Extract(CorpusSet.M5a, name).Units)
            {
                text.Append(VirWriter.WriteString(unit.Unit with { Vir = 2, Facts = unit.Unit.Facts with { Roslyn = "5.0.0" } })).Append('\n');
            }
        }
        var hash = Convert.ToHexStringLower(System.Security.Cryptography.SHA256.HashData(System.Text.Encoding.UTF8.GetBytes(text.ToString())));
        Assert.Equal(M5aVirAtVersion2, hash);
    }

    private static List<string> Strings(JsonElement member, string property) =>
        member.TryGetProperty(property, out var list) ? list.EnumerateArray().Select(e => e.GetString()!).ToList() : [];

    private static List<string> Subjects(VirUnit unit, VirAssumptionKind kind) =>
        unit.Assumptions.Where(a => a.Kind == kind).Select(a => a.Subject).ToList();
}
