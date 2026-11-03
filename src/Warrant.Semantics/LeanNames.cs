using Warrant.Cic;

namespace Warrant.Semantics;

/// <summary>
/// Lean names of translated C# symbols (KTD6, docs/m4/05 "Names"). A name depends on the symbol's
/// documentation-comment ID alone: <c>Cs</c>, then one component per namespace and type-path segment, then the
/// member, which carries its parameter list exactly as the ID writes it.
/// </summary>
public static class LeanNames
{
    /// <summary>The first component of every translated name.</summary>
    public static Name Root { get; } = Name.From("Cs");

    /// <summary>The name of a unit, from its documentation-comment ID.</summary>
    /// <param name="key">The ID, e.g. <c>M:Payouts.PayoutRules.Payout(System.Int32,System.Int32,System.Int32)</c>.</param>
    /// <returns>E.g. <c>Cs.Payouts.PayoutRules.«Payout(System.Int32,System.Int32,System.Int32)»</c>.</returns>
    /// <exception cref="TranslationException">The key is not a documentation-comment ID.</exception>
    public static Name ForKey(string key)
    {
        ArgumentNullException.ThrowIfNull(key);
        if (key.Length < 3 || key[1] != ':')
        {
            throw new TranslationException(key, $"'{key}' is not a documentation-comment ID.");
        }
        string body = key[2..];
        int paren = body.IndexOf('(', StringComparison.Ordinal);
        string path = paren < 0 ? body : body[..paren];
        string parameters = paren < 0 ? "" : body[paren..];
        var parts = path.Split('.');
        if (parts.Any(p => p.Length == 0))
        {
            throw new TranslationException(key, $"'{key}' has an empty name component.");
        }
        var name = Root;
        for (int i = 0; i < parts.Length; i++)
        {
            name = name.Append(i == parts.Length - 1 ? parts[i] + parameters : parts[i]);
        }
        return name;
    }

    /// <summary>A member of an enum or closed type: <c>Cs.Claims.Outcome.Matched</c>.</summary>
    /// <param name="typeKey">The type unit's key.</param>
    /// <param name="member">The member's name.</param>
    /// <returns>The name.</returns>
    public static Name Member(string typeKey, string member) => ForKey(typeKey).Append(member);

    /// <summary>A record's constructor, <c>R.$mk</c>.</summary>
    /// <param name="typeKey">The record's key.</param>
    /// <returns>The name.</returns>
    public static Name Constructor(string typeKey) => ForKey(typeKey).Append("$mk");

    /// <summary>A record's generated equality, <c>R.$eq : R → R → Bool</c>.</summary>
    /// <param name="typeKey">The record's key.</param>
    /// <returns>The name.</returns>
    public static Name Equality(string typeKey) => ForKey(typeKey).Append("$eq");

    /// <summary>A closed type's generated index, <c>T.$index : T → Nat</c>.</summary>
    /// <param name="typeKey">The closed type's key.</param>
    /// <returns>The name.</returns>
    public static Name Index(string typeKey) => ForKey(typeKey).Append("$index");

    /// <summary>The recursor the kernel generates for a record or closed type, <c>T.rec</c>.</summary>
    /// <param name="typeKey">The type's key.</param>
    /// <returns>The name.</returns>
    public static Name Recursor(string typeKey) => ForKey(typeKey).Append("rec");

    /// <summary>The display name used when no display name is supplied: the key without its kind prefix.</summary>
    /// <param name="key">The documentation-comment ID.</param>
    /// <returns>The fallback display name.</returns>
    public static string FallbackDisplay(string key)
    {
        ArgumentNullException.ThrowIfNull(key);
        return key.Length > 2 && key[1] == ':' ? key[2..] : key;
    }
}
