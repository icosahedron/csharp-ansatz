using System.Text.Json;
using Warrant.Extraction;
using Warrant.TestSupport;
using Warrant.Vir;

namespace Warrant.Extraction.Tests;

/// <summary>
/// Every member of every compilation of the M4 and M5a corpora gets the outcome expected.json gives it, as far as
/// extraction decides it (docs/m4/02, docs/m5a/01).
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
            case "translated" or "proved" or "false" or "unproved":
                Assert.Empty(diagnostics);
                Assert.NotNull(unit);
                if (outcome != "translated" && !expected.TryGetProperty("recursive", out _))
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

    // SHA-256 of every M4 unit's VIR at schema version 1, one unit per line in compilation and unit order, captured
    // from the M4 extractor before M5a added to VIR (plan U9): M5a adds kinds and fields but changes no existing encoding.
    private const string M4VirAtVersion1 = "17845076f4fda166e0409d5d374dbfbd6a89580b26c3f8e501b8df6d6f033994";

    [Fact]
    public void EveryM4UnitsVirIsUnchangedApartFromTheVersion()
    {
        var text = new System.Text.StringBuilder();
        foreach (var name in Corpus.CompilationNames)
        {
            foreach (var unit in Corpus.Extract(name).Units)
            {
                text.Append(VirWriter.WriteString(unit.Unit with { Vir = 1 })).Append('\n');
            }
        }
        var hash = Convert.ToHexStringLower(System.Security.Cryptography.SHA256.HashData(System.Text.Encoding.UTF8.GetBytes(text.ToString())));
        Assert.Equal(M4VirAtVersion1, hash);
    }

    private static List<string> Strings(JsonElement member, string property) =>
        member.TryGetProperty(property, out var list) ? list.EnumerateArray().Select(e => e.GetString()!).ToList() : [];

    private static List<string> Subjects(VirUnit unit, VirAssumptionKind kind) =>
        unit.Assumptions.Where(a => a.Kind == kind).Select(a => a.Subject).ToList();
}
