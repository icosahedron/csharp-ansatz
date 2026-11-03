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

    /// <summary>The diagnostic message for an undecided theorem (WRT0006).</summary>
    /// <param name="theorem">The theorem's short name, from <see cref="ShortName"/>.</param>
    /// <param name="reason">Why it is undecided.</param>
    /// <returns>The message.</returns>
    public static string UndecidedMessage(string theorem, string reason) => $"Theorem '{theorem}' was not decided: {reason}";

    /// <summary>The assumption report's detail for an undecided theorem.</summary>
    /// <param name="reason">Why it is undecided.</param>
    /// <returns>The detail.</returns>
    public static string UndecidedDetail(string reason) => $"the claim was not decided ({UndecidedOutcome.Code}): {reason}";

    /// <summary>
    /// The values of a false comparison's sides, e.g. <c>Increment(2) = 3, 4 = 4</c>: each side's source text, or
    /// <c>left</c> and <c>right</c> when it is not known.
    /// </summary>
    /// <param name="sides">The sides, from <see cref="FalseOutcome.Sides"/>.</param>
    /// <param name="sourceText">The source text of a span; null when it cannot be read.</param>
    /// <returns>The values, comma-separated.</returns>
    public static string Values(ImmutableArray<ReadBackSide> sides, Func<VirSpan, string?> sourceText)
    {
        ArgumentNullException.ThrowIfNull(sourceText);
        var values = sides.Select((s, i) => $"{(s.Span is { } span ? sourceText(span) : null) ?? (i == 0 ? "left" : "right")} = {s.Value}");
        return string.Join(", ", values);
    }

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
        using var stream = File.OpenRead(path);
        var hash = Convert.ToHexStringLower(SHA256.HashData(stream));
        var name = Path.GetFileName(path);
        name = name.EndsWith(".ndjson.gz", StringComparison.Ordinal) ? name[..^".ndjson.gz".Length] : name;
        return $"{name} sha256:{hash[..12]}";
    }
}
