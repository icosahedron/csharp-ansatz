using System.Collections.Immutable;
using System.Security.Cryptography;
using Warrant.Vir;

namespace Warrant.Engine.Reports;

/// <summary>
/// The wording of a theorem's outcomes and of the bundle's identity, which every caller of the engine prints the same
/// way (docs/m4/06, docs/m4/07): <c>warrant translate</c>, <c>warrant verify</c> and the build task.
/// </summary>
public static class OutcomeText
{
    /// <summary>The assumption report's detail for a false theorem.</summary>
    public const string FalseDetail = $"the claim is false ({FalseOutcome.Code})";

    /// <summary>The diagnostic message for a false theorem (WRT0001).</summary>
    /// <param name="theorem">The theorem's short name, from <see cref="ShortName"/>.</param>
    /// <returns>The message.</returns>
    public static string FalseMessage(string theorem) => $"Theorem '{theorem}' is false.";

    /// <summary>
    /// The diagnostic message for a unit that ran out of a budget (WRT0006, R5): a theorem was not decided; a definition,
    /// with its decrease proofs and equation lemma, was not verified.
    /// </summary>
    /// <param name="kind">What the unit is.</param>
    /// <param name="name">The unit's short name, from <see cref="ShortName"/>.</param>
    /// <param name="reason">Why it is undecided.</param>
    /// <returns>The message.</returns>
    public static string UndecidedMessage(VirUnitKind kind, string name, string reason) =>
        kind == VirUnitKind.Theorem ? $"Theorem '{name}' was not decided: {reason}" : $"Member '{name}' was not verified: {reason}";

    /// <summary>The assumption report's detail for an undecided theorem.</summary>
    /// <param name="reason">Why it is undecided.</param>
    /// <returns>The detail.</returns>
    public static string UndecidedDetail(string reason) => $"the claim was not decided ({UndecidedOutcome.Code}): {reason}";

    /// <summary>
    /// The diagnostic message for a theorem that was not proved (WRT0001, docs/m5a/04, "What a failure reports"): one
    /// line, complete on its own, e.g. <c>Theorem 'AlwaysLarger' could not be proved: unsolved goals. Counterexample: x =
    /// 2147483647.</c>; the message's later lines and the goals follow in <see cref="NotProvedDetails"/>. For a recursive
    /// method's decrease failure, the overload that takes the source text names the call and the measure.
    /// </summary>
    /// <param name="theorem">The theorem's short name, from <see cref="ShortName"/>.</param>
    /// <param name="outcome">The outcome.</param>
    /// <returns>The message.</returns>
    public static string NotProvedMessage(string theorem, NotProvedOutcome outcome)
    {
        ArgumentNullException.ThrowIfNull(outcome);
        var line = $"Theorem '{theorem}' could not be proved: {FirstLine(outcome.Message)}";
        // A first line that introduces the next, such as omega's "could not prove the goal:", ends the sentence instead.
        return outcome.Counterexample.IsEmpty ? line : $"{line.TrimEnd('.', ':')}. Counterexample: {Counterexample(outcome.Counterexample)}.";
    }

    /// <summary>
    /// <see cref="NotProvedMessage(string, NotProvedOutcome)"/>, except that for a recursive method whose decrease
    /// obligation was not proved it names the call and the measure (docs/m5a/03, "Decrease theorems"), e.g. <c>The
    /// recursive call 'Bad(n - 1)' could not be shown to decrease 'n': omega could not prove the goal.</c>
    /// </summary>
    /// <param name="unit">The unit's short name, from <see cref="ShortName"/>.</param>
    /// <param name="outcome">The outcome.</param>
    /// <param name="spans">The unit's span table from the current extraction (KTD7); null when spans are not available.</param>
    /// <param name="sourceText">The source text of a span; null when it cannot be read.</param>
    /// <returns>The message.</returns>
    public static string NotProvedMessage(string unit, NotProvedOutcome outcome, SpanTable? spans, Func<VirSpan, string?> sourceText)
    {
        ArgumentNullException.ThrowIfNull(outcome);
        ArgumentNullException.ThrowIfNull(sourceText);
        if (outcome.Decrease is not { } decrease)
        {
            return NotProvedMessage(unit, outcome);
        }
        var call = SpanOf(spans, decrease.CallNode) is { } c && sourceText(c) is { } callText ? $"The recursive call '{callText}'" : $"Recursive call {decrease.Index} of '{unit}'";
        var measure = SpanOf(spans, decrease.MeasureNode) is { } m && sourceText(m) is { } measureText ? $"'{measureText}'" : "its measure";
        return $"{call} could not be shown to decrease {measure}: {FirstLine(outcome.Message).TrimEnd('.', ':')}.";
    }

    /// <summary>
    /// The lines that follow <see cref="NotProvedMessage(string, NotProvedOutcome)"/>: the message's later lines, then the goals, as Lean's
    /// "unsolved goals" message shows them.
    /// </summary>
    /// <param name="outcome">The outcome.</param>
    /// <returns>The lines, unindented; empty lines separate goals.</returns>
    public static IReadOnlyList<string> NotProvedDetails(NotProvedOutcome outcome)
    {
        ArgumentNullException.ThrowIfNull(outcome);
        var lines = outcome.Message.Split('\n').Skip(1).ToList();
        if (outcome.Goals.Length > 0)
        {
            if (lines.Count > 0)
            {
                lines.Add("");
            }
            lines.AddRange(outcome.Goals.Split('\n'));
        }
        return lines;
    }

    /// <summary>The assumption report's detail for a theorem that was not proved.</summary>
    /// <param name="outcome">The outcome.</param>
    /// <returns>The detail.</returns>
    public static string NotProvedDetail(NotProvedOutcome outcome)
    {
        ArgumentNullException.ThrowIfNull(outcome);
        if (outcome.Decrease is { } decrease)
        {
            return $"recursive call {decrease.Index} was not shown to decrease ({NotProvedOutcome.Code}): {FirstLine(outcome.Message)}";
        }
        var detail = $"the claim was not proved ({NotProvedOutcome.Code}): {FirstLine(outcome.Message)}";
        return outcome.Counterexample.IsEmpty ? detail : $"{detail}; counterexample {Counterexample(outcome.Counterexample)}";
    }

    /// <summary>A counterexample's values, e.g. <c>x = 2147483647, b = true</c>.</summary>
    /// <param name="values">The values, in parameter order.</param>
    /// <returns>The text.</returns>
    public static string Counterexample(ImmutableArray<CounterexampleValue> values) =>
        string.Join(", ", values.Select(v => $"{v.Parameter} = {v.Value}"));

    /// <summary>The diagnostic message for an internal error (WRT0010), which says the fault is Warrant's, not the claim's.</summary>
    /// <param name="theorem">The theorem's short name, from <see cref="ShortName"/>.</param>
    /// <param name="reason">The kernel's or Meta's message.</param>
    /// <returns>The message.</returns>
    public static string InternalErrorMessage(string theorem, string reason) =>
        $"Theorem '{theorem}' was not checked because of an internal error in Warrant: {FirstLine(reason)}";

    /// <summary>
    /// The diagnostic message for a unit the engine could not translate or the kernel rejected (WRT0010): extraction
    /// accepted it, so the fault is Warrant's.
    /// </summary>
    /// <param name="unit">The unit's name.</param>
    /// <param name="reason">The translator's or the kernel's message.</param>
    /// <returns>The message.</returns>
    public static string FailedMessage(string unit, string reason) =>
        $"'{unit}' was not admitted because of an internal error in Warrant: {FirstLine(reason)}";

    /// <summary>The assumption report's detail for an internal error.</summary>
    /// <param name="reason">The kernel's or Meta's message.</param>
    /// <returns>The detail.</returns>
    public static string InternalErrorDetail(string reason) => $"an internal error in Warrant ({InternalErrorOutcome.Code}): {FirstLine(reason)}";

    private static string FirstLine(string text)
    {
        var newline = text.IndexOf('\n', StringComparison.Ordinal);
        return newline < 0 ? text : text[..newline];
    }

    /// <summary>
    /// The values of a false comparison's sides, e.g. <c>Increment(2) = 3, 4 = 4</c>: each side's source text, or
    /// <c>left</c> and <c>right</c> when it is not known.
    /// </summary>
    /// <param name="sides">The sides, from <see cref="FalseOutcome.Sides"/>.</param>
    /// <param name="spans">The unit's span table from the current extraction (KTD7); null when spans are not available.</param>
    /// <param name="sourceText">The source text of a span; null when it cannot be read.</param>
    /// <returns>The values, comma-separated.</returns>
    public static string Values(ImmutableArray<ReadBackSide> sides, SpanTable? spans, Func<VirSpan, string?> sourceText)
    {
        ArgumentNullException.ThrowIfNull(sourceText);
        var values = sides.Select((s, i) => $"{(SpanOf(spans, s.NodeId) is { } span ? sourceText(span) : null) ?? (i == 0 ? "left" : "right")} = {s.Value}");
        return string.Join(", ", values);
    }

    /// <summary>
    /// The span an outcome's node ID has in the current extraction (KTD7): outcomes name positions by VIR node ID, so a
    /// cached outcome renders at the lines the code has now.
    /// </summary>
    /// <param name="spans">The unit's span table; null when spans are not available.</param>
    /// <param name="nodeId">The node ID, e.g. <see cref="NotProvedOutcome.TacticNode"/>; null for none.</param>
    /// <returns>The span, or null when there is no node or it has no span.</returns>
    public static VirSpan? SpanOf(SpanTable? spans, int? nodeId) =>
        spans is not null && nodeId is { } id && spans.TryGetSpan(id, out var span) ? span : null;

    /// <summary>A theorem's name without its type or containing type, as messages print it (docs/m4/06).</summary>
    /// <param name="displayName">The theorem's C# display name.</param>
    /// <returns>The short name.</returns>
    public static string ShortName(string displayName)
    {
        ArgumentNullException.ThrowIfNull(displayName);
        var paren = displayName.IndexOf('(', StringComparison.Ordinal);
        var head = paren < 0 ? displayName : displayName[..paren];
        return head[(head.LastIndexOf('.') + 1)..];
    }

    /// <summary>The bundle's file name and the start of its SHA-256, which identify it in reports.</summary>
    /// <param name="path">The bundle file.</param>
    /// <returns>The name, e.g. <c>warrant-semantics sha256:0123456789ab</c>.</returns>
    public static string BundleName(string path)
    {
        var hash = FileSha256(path);
        var name = Path.GetFileName(path);
        name = name.EndsWith(".ndjson.gz", StringComparison.Ordinal) ? name[..^".ndjson.gz".Length] : name;
        return $"{name} sha256:{hash[..12]}";
    }

    /// <summary>The SHA-256 of a file's bytes as lower-case hex.</summary>
    /// <param name="path">The file.</param>
    /// <returns>The 64-character hex digest.</returns>
    public static string FileSha256(string path)
    {
        using var stream = File.OpenRead(path);
        return Convert.ToHexStringLower(SHA256.HashData(stream));
    }
}
