namespace Warrant.Cic;

/// <summary>One entry of an expression's metadata map.</summary>
/// <param name="Key">The key, in Lean's dotted name notation.</param>
/// <param name="Value">
/// The value as rendered by Lean's <c>repr</c> (for example <c>true</c>, <c>"text"</c>,
/// <c>`name</c>, <c>42</c>). Values are kept opaque because the kernel ignores metadata.
/// </param>
public sealed record KVMapEntry(string Key, string Value);

/// <summary>
/// The metadata attached by <see cref="MDataExpr"/>, mirroring Lean's <c>KVMap</c>.
/// Entry order is preserved.
/// </summary>
/// <param name="Entries">The entries, in order.</param>
public sealed record KVMap(EquatableArray<KVMapEntry> Entries)
{
    /// <summary>The empty map.</summary>
    public static readonly KVMap Empty = new(EquatableArray<KVMapEntry>.Empty);
}
