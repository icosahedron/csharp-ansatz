using Warrant.Vir;

namespace Warrant.Extraction;

/// <summary>The severity of an extraction diagnostic.</summary>
public enum ExtractionSeverity
{
    /// <summary>The member or type still translates (WRT0008).</summary>
    Warning,

    /// <summary>The member or type is not translated, or the compilation has errors.</summary>
    Error,
}

/// <summary>
/// A diagnostic from extraction (docs/m4/03, "Diagnostics"), or a compiler error.
/// </summary>
/// <param name="Id">The code: <c>WRT0002</c> to <c>WRT0005</c>, <c>WRT0008</c>, <c>WRT0009</c>, or a compiler code such as <c>CS0103</c>.</param>
/// <param name="Severity">The severity.</param>
/// <param name="Construct">
/// The construct, exactly as <c>tests/corpus/m4/expected.json</c> spells it (e.g. <c>division</c>), or a documentation-comment ID for
/// WRT0003 and WRT0005 (the callee); null for a compiler error.
/// </param>
/// <param name="MemberKey">The documentation-comment ID of the member or type the diagnostic is about; null for a compiler error.</param>
/// <param name="Location">Where it was found, or null if the compiler gave no source location.</param>
/// <param name="Message">A message for people, with C# display names.</param>
public sealed record ExtractionDiagnostic(
    string Id,
    ExtractionSeverity Severity,
    string? Construct,
    string? MemberKey,
    VirSpan? Location,
    string Message);

/// <summary>A translated unit, with its side table of spans.</summary>
/// <param name="Unit">The VIR unit.</param>
/// <param name="Spans">The spans of its nodes, by pre-order node ID; outside both hashes.</param>
/// <param name="DisplayName">The C# display name, for messages and reports (KTD6).</param>
/// <param name="Location">The declaration's name, for messages and reports.</param>
public sealed record ExtractedUnit(VirUnit Unit, SpanTable Spans, string DisplayName, VirSpan? Location)
{
    /// <summary>The unit's key, its documentation-comment ID.</summary>
    public string Key => Unit.Key;
}

/// <summary>What extraction produced from one compilation.</summary>
public sealed class ExtractionResult
{
    internal ExtractionResult(IReadOnlyList<ExtractedUnit> units, IReadOnlyList<ExtractionDiagnostic> diagnostics, bool hasCompileErrors)
    {
        Units = units;
        Diagnostics = diagnostics;
        HasCompileErrors = hasCompileErrors;
    }

    /// <summary>
    /// The translated units, every dependency before its users, ties broken by key (ordinal).
    /// Rejected units are absent; empty when the compilation has errors.
    /// </summary>
    public IReadOnlyList<ExtractedUnit> Units { get; }

    /// <summary>All diagnostics, ordered by location, then code, member key and construct (ordinal).</summary>
    public IReadOnlyList<ExtractionDiagnostic> Diagnostics { get; }

    /// <summary>Whether the compilation had errors, in which case <see cref="Diagnostics"/> holds them and nothing was extracted.</summary>
    public bool HasCompileErrors { get; }

    /// <summary>Finds a translated unit by key.</summary>
    /// <param name="key">The documentation-comment ID.</param>
    /// <returns>The unit, or null if it was not translated.</returns>
    public ExtractedUnit? Find(string key) => Units.FirstOrDefault(u => string.Equals(u.Key, key, StringComparison.Ordinal));

    /// <summary>The diagnostics about one member or type.</summary>
    /// <param name="key">The documentation-comment ID.</param>
    /// <returns>The diagnostics whose <see cref="ExtractionDiagnostic.MemberKey"/> is <paramref name="key"/>, in order.</returns>
    public IReadOnlyList<ExtractionDiagnostic> DiagnosticsFor(string key) =>
        Diagnostics.Where(d => string.Equals(d.MemberKey, key, StringComparison.Ordinal)).ToList();
}

/// <summary>The diagnostic codes extraction raises (docs/m4/03, "Diagnostics").</summary>
public static class DiagnosticIds
{
    /// <summary>A construct outside the M4 subset.</summary>
    public const string Unsupported = "WRT0002";

    /// <summary>A call to a <c>[Theorem]</c> method.</summary>
    public const string CallsTheorem = "WRT0003";

    /// <summary>A spec call outside a theorem statement.</summary>
    public const string MalformedSpec = "WRT0004";

    /// <summary>A call from verified code to a member that is neither verified nor modelled.</summary>
    public const string NotVerified = "WRT0005";

    /// <summary>A way an unnamed value can reach a <c>[Closed]</c> enum (a warning).</summary>
    public const string UnnamedClosedValue = "WRT0008";

    /// <summary>A <c>[Closed]</c> class without the closed shape.</summary>
    public const string NotClosedShape = "WRT0009";

    /// <summary>
    /// A <c>Spec</c> statement that states nothing (a warning): <c>Spec.NoThrow</c> on a method that cannot raise (#239).
    /// </summary>
    public const string IneffectiveSpec = "WRT0013";
}
