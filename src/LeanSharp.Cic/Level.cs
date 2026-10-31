using System.Text;

namespace LeanSharp.Cic;

/// <summary>The shapes of a universe <see cref="Level"/>.</summary>
public enum LevelKind : byte
{
    /// <summary>Level 0, the universe of <c>Prop</c>.</summary>
    Zero,

    /// <summary>The successor of a level.</summary>
    Succ,

    /// <summary>The maximum of two levels.</summary>
    Max,

    /// <summary><c>imax u v</c>: 0 if <c>v</c> is 0, otherwise <c>max u v</c>.</summary>
    IMax,

    /// <summary>A universe parameter of the enclosing declaration.</summary>
    Param,
}

/// <summary>
/// A universe level, mirroring the kernel fragment of Lean 4's <c>Lean.Level</c>
/// (universe metavariables are an elaborator concept and are not represented here).
/// </summary>
/// <remarks>
/// Levels are immutable and compared structurally (not up to the level algebra; normalization and
/// <c>≤</c> live in the kernel).
/// </remarks>
public sealed class Level : IEquatable<Level>
{
    /// <summary>Level 0.</summary>
    public static readonly Level Zero = new(LevelKind.Zero, null, null, null);

    /// <summary>Level 1.</summary>
    public static readonly Level One = Succ(Zero);

    private readonly ulong _hash;

    private Level(LevelKind kind, Level? lhs, Level? rhs, Name? param)
    {
        Kind = kind;
        Lhs = lhs;
        Rhs = rhs;
        ParamName = param;
        (_hash, HasParam, Depth) = kind switch
        {
            LevelKind.Zero => (0x5A5A5A5A12345678UL, false, 0),
            LevelKind.Succ => (Hashing.Mix(11, lhs!._hash), lhs.HasParam, lhs.Depth + 1),
            LevelKind.Max => (Hashing.Mix(12, lhs!._hash, rhs!._hash), lhs.HasParam || rhs.HasParam, Math.Max(lhs.Depth, rhs.Depth) + 1),
            LevelKind.IMax => (Hashing.Mix(13, lhs!._hash, rhs!._hash), lhs.HasParam || rhs.HasParam, Math.Max(lhs.Depth, rhs.Depth) + 1),
            LevelKind.Param => (Hashing.Mix(14, param!.Hash64), true, 0),
            _ => throw new ArgumentOutOfRangeException(nameof(kind)),
        };
    }

    /// <summary>Which shape this level has.</summary>
    public LevelKind Kind { get; }

    /// <summary>The operand of <c>succ</c>, or the left operand of <c>max</c>/<c>imax</c>.</summary>
    public Level? Lhs { get; }

    /// <summary>The right operand of <c>max</c>/<c>imax</c>.</summary>
    public Level? Rhs { get; }

    /// <summary>The parameter name of a <see cref="LevelKind.Param"/> level.</summary>
    public Name? ParamName { get; }

    /// <summary>Whether a universe parameter occurs in this level.</summary>
    public bool HasParam { get; }

    /// <summary>
    /// Lean's level depth: 0 for zero and parameters, one more than the operand for <c>succ</c>, one
    /// more than the deeper operand for <c>max</c>/<c>imax</c>. For an explicit level <c>succⁿ 0</c>
    /// it is <c>n</c>.
    /// </summary>
    public int Depth { get; }

    internal ulong Hash64 => _hash;

    /// <summary><c>succ l</c>.</summary>
    public static Level Succ(Level l)
    {
        ArgumentNullException.ThrowIfNull(l);
        return new Level(LevelKind.Succ, l, null, null);
    }

    /// <summary><c>max l r</c>.</summary>
    public static Level Max(Level l, Level r)
    {
        ArgumentNullException.ThrowIfNull(l);
        ArgumentNullException.ThrowIfNull(r);
        return new Level(LevelKind.Max, l, r, null);
    }

    /// <summary><c>imax l r</c>.</summary>
    public static Level IMax(Level l, Level r)
    {
        ArgumentNullException.ThrowIfNull(l);
        ArgumentNullException.ThrowIfNull(r);
        return new Level(LevelKind.IMax, l, r, null);
    }

    /// <summary>The universe parameter <paramref name="name"/>.</summary>
    public static Level Param(Name name)
    {
        ArgumentNullException.ThrowIfNull(name);
        return new Level(LevelKind.Param, null, null, name);
    }

    /// <inheritdoc/>
    public bool Equals(Level? other)
    {
        if (ReferenceEquals(this, other))
        {
            return true;
        }
        if (other is null || _hash != other._hash || Kind != other.Kind || Depth != other.Depth)
        {
            return false;
        }
        return Kind switch
        {
            LevelKind.Zero => true,
            LevelKind.Succ => Lhs!.Equals(other.Lhs),
            LevelKind.Max or LevelKind.IMax => Lhs!.Equals(other.Lhs) && Rhs!.Equals(other.Rhs),
            LevelKind.Param => ParamName!.Equals(other.ParamName),
            _ => false,
        };
    }

    /// <inheritdoc/>
    public override bool Equals(object? obj) => obj is Level l && Equals(l);

    /// <inheritdoc/>
    public override int GetHashCode() => Hashing.Fold(_hash);

    /// <summary>Equality operator (structural).</summary>
    public static bool operator ==(Level? left, Level? right) =>
        left is null ? right is null : left.Equals(right);

    /// <summary>Inequality operator (structural).</summary>
    public static bool operator !=(Level? left, Level? right) => !(left == right);

    /// <summary>Lean-like notation, e.g. <c>max u (v+1)</c>.</summary>
    public override string ToString()
    {
        var sb = new StringBuilder();
        Write(sb, this, atomic: false);
        return sb.ToString();
    }

    private static void Write(StringBuilder sb, Level l, bool atomic)
    {
        // Peel successors: l = base + k.
        int k = 0;
        var b = l;
        while (b.Kind == LevelKind.Succ)
        {
            k++;
            b = b.Lhs!;
        }

        if (b.Kind == LevelKind.Zero)
        {
            sb.Append(k);
            return;
        }

        bool needParens = atomic && (k > 0 || b.Kind is LevelKind.Max or LevelKind.IMax);
        if (needParens)
        {
            sb.Append('(');
        }
        switch (b.Kind)
        {
            case LevelKind.Param:
                sb.Append(b.ParamName);
                break;
            case LevelKind.Max:
            case LevelKind.IMax:
                if (k > 0)
                {
                    sb.Append('(');
                }
                sb.Append(b.Kind == LevelKind.Max ? "max " : "imax ");
                Write(sb, b.Lhs!, atomic: true);
                sb.Append(' ');
                Write(sb, b.Rhs!, atomic: true);
                if (k > 0)
                {
                    sb.Append(')');
                }
                break;
        }
        if (k > 0)
        {
            sb.Append('+').Append(k);
        }
        if (needParens)
        {
            sb.Append(')');
        }
    }
}
