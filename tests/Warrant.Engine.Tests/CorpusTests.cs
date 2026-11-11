using System.Text.Json;
using Warrant.Extraction;

namespace Warrant.Engine.Tests;

/// <summary>
/// The M5a exit criterion as one test (plan U19, docs/m5a/01): every member of the M5a corpus gets the outcome
/// <c>tests/corpus/m5a/expected.json</c> gives it, from extraction through the engine.
/// </summary>
public sealed class CorpusTests(EngineFixture engine) : IClassFixture<EngineFixture>
{
    /// <summary>
    /// Every M6 corpus member (plan M6 U11, as amended by #167, and U19) gets its expected.json outcome from extraction
    /// through the default procedure: <c>accepted/</c> proves (a proved contract is a translated unit with its
    /// <c>$contract</c>), and <c>refuted/</c> fails with WRT0001 with the expected VC kind at the expected line. A method
    /// with dependencies is proved with its members' contracts as hypotheses (U20).
    /// </summary>
    [Fact]
    public void EveryM6MemberGetsItsExpectedOutcome()
    {
        var set = CorpusSet.M6;
        var mismatches = new List<string>();
        int members = 0;
        foreach (var compilation in set.Names)
        {
            var extraction = Extractor.Extract(set.Compile(compilation));
            var result = engine.Run($"m6/{compilation}");
            var expected = set.Expected.GetProperty("members").GetProperty(compilation);
            foreach (var member in expected.EnumerateObject())
            {
                members++;
                var actual = result.Find(member.Name);
                mismatches.AddRange(Compare(member.Name, member.Value, actual, extraction.DiagnosticsFor(member.Name)));
                if (actual is NotProvedOutcome notProved && member.Value.TryGetProperty("vc", out var vc))
                {
                    var line = Reports.OutcomeText.SpanOf(engine.Spans($"m6/{compilation}", member.Name), notProved.TacticNode) is { } span
                        ? $"{Path.GetFileName(span.Path)}:{span.StartLine}"
                        : "no line";
                    var kind = notProved.Vcs.IsDefaultOrEmpty ? "none" : notProved.Vcs[0].Kind.ToString();
                    var wanted = $"{vc.GetProperty("kind").GetString()} at {vc.GetProperty("at").GetString()} of {vc.GetProperty("count").GetInt32()}";
                    if (wanted != $"{kind} at {line} of {notProved.Vcs.Length}")
                    {
                        mismatches.Add($"{member.Name}: expected the VC {wanted}, got {kind} at {line} of {notProved.Vcs.Length}");
                    }
                }
            }
        }
        Assert.True(mismatches.Count == 0, string.Join("\n", mismatches));
        Assert.Equal(151, members);
    }

    [Fact]
    public void EveryM5aMemberGetsItsExpectedOutcome()
    {
        var set = CorpusSet.M5a;
        var mismatches = new List<string>();
        int members = 0;
        foreach (var compilation in set.Names)
        {
            var extraction = Extractor.Extract(set.Compile(compilation));
            var result = engine.Run($"m5a/{compilation}");
            var expected = set.Expected.GetProperty("members").GetProperty(compilation);
            foreach (var member in expected.EnumerateObject())
            {
                members++;
                mismatches.AddRange(Compare(member.Name, member.Value, result.Find(member.Name), extraction.DiagnosticsFor(member.Name)));
            }
            // Every unit the engine ran has an entry, so a member the corpus gains cannot go unchecked.
            mismatches.AddRange(result.Units.Where(u => !expected.TryGetProperty(u.Key, out _)).Select(u => $"{u.Key}: not in expected.json"));
        }
        Assert.True(mismatches.Count == 0, string.Join("\n", mismatches));
        Assert.Equal(33, members);
    }

    /// <summary>The ways one member's outcome differs from its expected.json entry; empty when it matches.</summary>
    private static IEnumerable<string> Compare(string key, JsonElement expected, UnitOutcome? actual, IReadOnlyList<ExtractionDiagnostic> diagnostics)
    {
        var outcome = expected.GetProperty("outcome").GetString()!;
        if (outcome == "rejected")
        {
            if (actual is not null)
            {
                yield return $"{key}: expected rejected, the engine ran it ({Reports.AssumptionReports.OutcomeName(actual)})";
            }
            var wanted = expected.GetProperty("diagnostics").EnumerateArray()
                .Select(d => d.GetProperty("id").GetString() + " | " + d.GetProperty("construct").GetString())
                .Order(StringComparer.Ordinal);
            var got = diagnostics.Select(d => d.Id + " | " + d.Construct).Order(StringComparer.Ordinal);
            if (!wanted.SequenceEqual(got))
            {
                yield return $"{key}: expected diagnostics [{string.Join(", ", wanted)}], got [{string.Join(", ", got)}]";
            }
            yield break;
        }
        if (actual is null)
        {
            yield return $"{key}: expected {outcome}, but the engine did not run it ({string.Join(", ", diagnostics.Select(d => d.Id + " " + d.Construct))})";
            yield break;
        }
        // The outcome under the name the reports and the CLI use.
        var name = Reports.AssumptionReports.OutcomeName(actual);
        if (name != outcome)
        {
            yield return $"{key}: expected {outcome}, got {name}: {actual}";
            yield break;
        }
        switch (actual)
        {
            case ProvedOutcome proved:
                var by = Reports.AssumptionReports.ProofName(proved.By);
                if (expected.GetProperty("by").GetString() != by)
                {
                    yield return $"{key}: expected proved by {expected.GetProperty("by").GetString()}, got {by}";
                }
                break;
            case NotProvedOutcome notProved:
                if (expected.GetProperty("code").GetString() != NotProvedOutcome.Code)
                {
                    yield return $"{key}: expected {expected.GetProperty("code").GetString()}, got {NotProvedOutcome.Code}";
                }
                var goal = expected.GetProperty("goal").GetString();
                if (goal != notProved.Goals)
                {
                    yield return $"{key}: expected the goal\n{goal}\ngot\n{notProved.Goals}";
                }
                var counterexample = expected.TryGetProperty("counterexample", out var ce)
                    ? ce.EnumerateObject().Select(p => $"{p.Name} = {p.Value.GetString()}").ToList()
                    : [];
                var found = notProved.Counterexample.Select(v => $"{v.Parameter} = {v.Value}").ToList();
                if (!counterexample.SequenceEqual(found))
                {
                    yield return $"{key}: expected the counterexample [{string.Join(", ", counterexample)}], got [{string.Join(", ", found)}]";
                }
                bool decreases = expected.TryGetProperty("obligation", out var o) && o.GetString() == "decreases";
                if (decreases != notProved.Decrease is not null)
                {
                    yield return $"{key}: expected the {(decreases ? "decrease obligation" : "claim")} to fail, got {notProved.Decrease}";
                }
                break;
        }
    }
}
