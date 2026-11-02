using System.Globalization;
using System.Text;

namespace Warrant.Cic;

/// <summary>The three shapes of a hierarchical <see cref="Name"/>.</summary>
public enum NameKind : byte
{
    /// <summary>The empty name, the root of every hierarchical name.</summary>
    Anonymous,

    /// <summary>A prefix extended with a string component.</summary>
    Str,

    /// <summary>A prefix extended with a numeric component.</summary>
    Num,
}

/// <summary>
/// A hierarchical name such as <c>Nat.add_comm</c>, mirroring Lean 4's <c>Lean.Name</c>.
/// </summary>
/// <remarks>
/// Names are immutable and compared structurally. Each name caches its hash and depth, so
/// equality is O(1) when names differ and O(depth) only when they are equal but not shared.
/// </remarks>
public sealed class Name : IEquatable<Name>, IComparable<Name>
{
    /// <summary>The anonymous (empty) name.</summary>
    public static readonly Name Anonymous = new();

    private readonly ulong _hash;
    private readonly string? _string;
    private readonly ulong _number;

    private Name()
    {
        Kind = NameKind.Anonymous;
        Prefix = null;
        Depth = 0;
        _hash = 0x1F2E3D4C5B6A7988UL;
    }

    private Name(Name prefix, string component)
    {
        Kind = NameKind.Str;
        Prefix = prefix;
        Depth = prefix.Depth + 1;
        _string = component;
        _hash = Hashing.Mix(prefix._hash, 1, Hashing.String(component));
    }

    private Name(Name prefix, ulong component)
    {
        Kind = NameKind.Num;
        Prefix = prefix;
        Depth = prefix.Depth + 1;
        _number = component;
        _hash = Hashing.Mix(prefix._hash, 2, component);
    }

    /// <summary>Which shape this name has.</summary>
    public NameKind Kind { get; }

    /// <summary>The prefix, or <see langword="null"/> for <see cref="Anonymous"/>.</summary>
    public Name? Prefix { get; }

    /// <summary>The number of components (0 for <see cref="Anonymous"/>).</summary>
    public int Depth { get; }

    /// <summary>Whether this is the anonymous name.</summary>
    public bool IsAnonymous => Kind == NameKind.Anonymous;

    /// <summary>The string component of a <see cref="NameKind.Str"/> name.</summary>
    /// <exception cref="InvalidOperationException">The name is not a string name.</exception>
    public string StringComponent =>
        Kind == NameKind.Str ? _string! : throw new InvalidOperationException($"Name '{this}' is not a string name.");

    /// <summary>The numeric component of a <see cref="NameKind.Num"/> name.</summary>
    /// <exception cref="InvalidOperationException">The name is not a numeric name.</exception>
    public ulong NumericComponent =>
        Kind == NameKind.Num ? _number : throw new InvalidOperationException($"Name '{this}' is not a numeric name.");

    internal ulong Hash64 => _hash;

    /// <summary>Extends <paramref name="prefix"/> with a string component.</summary>
    public static Name Str(Name prefix, string component)
    {
        ArgumentNullException.ThrowIfNull(prefix);
        ArgumentNullException.ThrowIfNull(component);
        return new Name(prefix, component);
    }

    /// <summary>Extends <paramref name="prefix"/> with a numeric component.</summary>
    public static Name Num(Name prefix, ulong component)
    {
        ArgumentNullException.ThrowIfNull(prefix);
        return new Name(prefix, component);
    }

    /// <summary>Extends this name with a string component.</summary>
    public Name Append(string component) => Str(this, component);

    /// <summary>Extends this name with a numeric component.</summary>
    public Name Append(ulong component) => Num(this, component);

    /// <summary>Builds a name from string components, e.g. <c>Name.From("Nat", "add")</c>.</summary>
    public static Name From(params ReadOnlySpan<string> components)
    {
        var name = Anonymous;
        foreach (var c in components)
        {
            name = Str(name, c);
        }
        return name;
    }

    /// <summary>
    /// Parses Lean's dotted notation: <c>Nat.add_comm</c>, <c>_private.0.foo</c>, <c>«a.b».c</c>.
    /// </summary>
    /// <remarks>
    /// Components consisting only of decimal digits become numeric components. Guillemets
    /// (<c>«…»</c>) quote a string component that contains dots or would otherwise read as a number.
    /// The empty string parses to <see cref="Anonymous"/>.
    /// </remarks>
    /// <exception cref="FormatException">The text is not a well-formed name.</exception>
    public static Name Parse(string text)
    {
        ArgumentNullException.ThrowIfNull(text);
        var name = Anonymous;
        int i = 0;
        while (i < text.Length)
        {
            if (text[i] == '«')
            {
                int close = text.IndexOf('»', i + 1);
                if (close < 0)
                {
                    throw new FormatException($"Unterminated '«' in name '{text}'.");
                }
                name = Str(name, text[(i + 1)..close]);
                i = close + 1;
            }
            else
            {
                int dot = text.IndexOf('.', i);
                int end = dot < 0 ? text.Length : dot;
                string part = text[i..end];
                if (part.Length == 0)
                {
                    throw new FormatException($"Empty component in name '{text}'.");
                }
                name = IsAllDigits(part)
                    ? Num(name, ulong.Parse(part, NumberStyles.None, CultureInfo.InvariantCulture))
                    : Str(name, part);
                i = end;
            }

            if (i < text.Length)
            {
                if (text[i] != '.' || i == text.Length - 1)
                {
                    throw new FormatException($"Malformed name '{text}' at position {i}.");
                }
                i++;
            }
        }
        return name;
    }

    /// <summary>The components from outermost to innermost.</summary>
    public IReadOnlyList<Name> Components()
    {
        var result = new Name[Depth];
        var n = this;
        for (int i = Depth - 1; i >= 0; i--)
        {
            result[i] = n;
            n = n.Prefix!;
        }
        return result;
    }

    /// <summary>
    /// Lean's <c>Name.appendAfter</c>: appends <paramref name="suffix"/> to the last string component
    /// (<c>n</c> → <c>n_ih</c>), or adds a string component if the last component is numeric.
    /// </summary>
    /// <remarks>Lean first strips macro scopes (hygiene suffixes); those are not modelled yet.</remarks>
    public Name AppendAfter(string suffix) =>
        Kind == NameKind.Str ? Str(Prefix!, _string + suffix) : Str(this, suffix);

    /// <summary>Lean's <c>Name.appendIndexAfter</c>: <c>motive</c> → <c>motive_1</c>.</summary>
    public Name AppendIndexAfter(int index) =>
        AppendAfter("_" + index.ToString(CultureInfo.InvariantCulture));

    /// <summary>
    /// Lean's <c>Name.replacePrefix</c>: replaces the prefix <paramref name="prefix"/> by
    /// <paramref name="newPrefix"/> (<c>Nat.zero</c> with <c>Nat</c> → anonymous gives <c>zero</c>).
    /// Returns this name unchanged if <paramref name="prefix"/> is not a prefix.
    /// </summary>
    public Name ReplacePrefix(Name prefix, Name newPrefix)
    {
        ArgumentNullException.ThrowIfNull(prefix);
        ArgumentNullException.ThrowIfNull(newPrefix);
        if (Equals(prefix))
        {
            return newPrefix;
        }
        if (IsAnonymous)
        {
            return this;
        }
        var p = Prefix!.ReplacePrefix(prefix, newPrefix);
        if (ReferenceEquals(p, Prefix))
        {
            return this;
        }
        return Kind == NameKind.Str ? Str(p, _string!) : Num(p, _number);
    }

    /// <summary>Concatenation: <c>Nat ++ add.comm = Nat.add.comm</c> (Lean's <c>name + name</c>).</summary>
    public static Name operator +(Name left, Name right)
    {
        ArgumentNullException.ThrowIfNull(left);
        ArgumentNullException.ThrowIfNull(right);
        if (right.IsAnonymous)
        {
            return left;
        }
        if (left.IsAnonymous)
        {
            return right;
        }
        var prefix = left + right.Prefix!;
        return right.Kind == NameKind.Str ? Str(prefix, right._string!) : Num(prefix, right._number);
    }

    /// <summary>Concatenation (see <see cref="op_Addition"/>).</summary>
    public static Name Add(Name left, Name right) => left + right;

    /// <summary>Whether <paramref name="prefix"/> is a (non-strict) prefix of this name.</summary>
    public bool StartsWith(Name prefix)
    {
        ArgumentNullException.ThrowIfNull(prefix);
        if (prefix.Depth > Depth)
        {
            return false;
        }
        var n = this;
        while (n.Depth > prefix.Depth)
        {
            n = n.Prefix!;
        }
        return n.Equals(prefix);
    }

    /// <inheritdoc/>
    public bool Equals(Name? other)
    {
        Name? a = this, b = other;
        while (true)
        {
            if (ReferenceEquals(a, b))
            {
                return true;
            }
            if (b is null || a!._hash != b._hash || a.Depth != b.Depth || a.Kind != b.Kind)
            {
                return false;
            }
            switch (a.Kind)
            {
                case NameKind.Str when !string.Equals(a._string, b._string, StringComparison.Ordinal):
                case NameKind.Num when a._number != b._number:
                    return false;
            }
            a = a.Prefix;
            b = b.Prefix;
        }
    }

    /// <inheritdoc/>
    public override bool Equals(object? obj) => obj is Name n && Equals(n);

    /// <inheritdoc/>
    public override int GetHashCode() => Hashing.Fold(_hash);

    /// <summary>
    /// Total order: component-wise from the root; numeric components sort before string components,
    /// numbers numerically, strings ordinally.
    /// </summary>
    public int CompareTo(Name? other)
    {
        if (other is null)
        {
            return 1;
        }
        if (ReferenceEquals(this, other))
        {
            return 0;
        }
        var xs = Components();
        var ys = other.Components();
        int n = Math.Min(xs.Count, ys.Count);
        for (int i = 0; i < n; i++)
        {
            var x = xs[i];
            var y = ys[i];
            int c = (x.Kind, y.Kind) switch
            {
                (NameKind.Num, NameKind.Num) => x._number.CompareTo(y._number),
                (NameKind.Str, NameKind.Str) => string.CompareOrdinal(x._string, y._string),
                (NameKind.Num, _) => -1,
                _ => 1,
            };
            if (c != 0)
            {
                return c;
            }
        }
        return xs.Count.CompareTo(ys.Count);
    }

    /// <summary>Equality operator (structural).</summary>
    public static bool operator ==(Name? left, Name? right) =>
        left is null ? right is null : left.Equals(right);

    /// <summary>Inequality operator (structural).</summary>
    public static bool operator !=(Name? left, Name? right) => !(left == right);

    /// <summary>Less-than under <see cref="CompareTo"/>.</summary>
    public static bool operator <(Name? left, Name? right) => Compare(left, right) < 0;

    /// <summary>Less-than-or-equal under <see cref="CompareTo"/>.</summary>
    public static bool operator <=(Name? left, Name? right) => Compare(left, right) <= 0;

    /// <summary>Greater-than under <see cref="CompareTo"/>.</summary>
    public static bool operator >(Name? left, Name? right) => Compare(left, right) > 0;

    /// <summary>Greater-than-or-equal under <see cref="CompareTo"/>.</summary>
    public static bool operator >=(Name? left, Name? right) => Compare(left, right) >= 0;

    private static int Compare(Name? left, Name? right) =>
        left is null ? (right is null ? 0 : -1) : left.CompareTo(right);

    /// <summary>Lean's dotted notation; round-trips through <see cref="Parse"/>.</summary>
    public override string ToString()
    {
        if (IsAnonymous)
        {
            return "[anonymous]";
        }
        var sb = new StringBuilder();
        var parts = Components();
        for (int i = 0; i < parts.Count; i++)
        {
            if (i > 0)
            {
                sb.Append('.');
            }
            var p = parts[i];
            if (p.Kind == NameKind.Num)
            {
                sb.Append(p._number.ToString(CultureInfo.InvariantCulture));
            }
            else if (NeedsQuoting(p._string!))
            {
                sb.Append('«').Append(p._string).Append('»');
            }
            else
            {
                sb.Append(p._string);
            }
        }
        return sb.ToString();
    }

    private static bool NeedsQuoting(string s) =>
        s.Length == 0 || s.Contains('.', StringComparison.Ordinal) || IsAllDigits(s) || s.Contains('«', StringComparison.Ordinal);

    private static bool IsAllDigits(string s)
    {
        foreach (char c in s)
        {
            if (c is < '0' or > '9')
            {
                return false;
            }
        }
        return s.Length > 0;
    }
}
