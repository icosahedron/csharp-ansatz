using Warrant.Vir;

namespace Warrant.Extraction;

/// <summary>
/// The BCL members verified code may call although they are not <c>[Verified]</c> (plan M6 KTD23): each becomes a
/// <see cref="ModelledCallExpr"/> that Semantics maps to a Warrant library definition. Adding a member means a row here,
/// a library definition, a CLR-agreement row and a corpus entry. The ones that can throw are
/// <see cref="Effects.ThrowingModelledMembers"/>, which must be a subset of these.
/// </summary>
public static class ModelledMembers
{
    private static readonly HashSet<string> Members = new(StringComparer.Ordinal)
    {
        "M:System.Math.Min(System.Int32,System.Int32)",
        "M:System.Math.Min(System.Int64,System.Int64)",
        "M:System.Math.Max(System.Int32,System.Int32)",
        "M:System.Math.Max(System.Int64,System.Int64)",
        "M:System.Math.Abs(System.Int32)",
        "M:System.Math.Abs(System.Int64)",

        // decimal (M6 U17): none of these can throw, since a decimal's sign is a bit of its own.
        "M:System.Math.Min(System.Decimal,System.Decimal)",
        "M:System.Math.Max(System.Decimal,System.Decimal)",
        "M:System.Math.Abs(System.Decimal)",
    };

    /// <summary>The modelled members' documentation-comment IDs.</summary>
    public static IReadOnlyCollection<string> Keys => Members;

    /// <summary>Whether a member is modelled.</summary>
    /// <param name="key">The member's documentation-comment ID.</param>
    /// <returns>True when verified code may call it.</returns>
    public static bool Contains(string key) => Members.Contains(key);
}
