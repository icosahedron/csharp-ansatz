using System.Collections.Immutable;
using System.Globalization;
using System.Numerics;

namespace Warrant.Meta.Omega;

/// <summary>
/// Lean's <c>Int</c> and <c>Nat</c> operations as Init defines them: <c>/</c> and <c>%</c> on <c>Int</c> are
/// <c>Int.ediv</c> and <c>Int.emod</c> (Init/Data/Int/DivMod/Basic.lean 73-117), division by zero is zero, and
/// <c>Nat</c> subtraction truncates. The proofs <c>omega</c> builds make the kernel recompute these, so they must agree
/// exactly.
/// </summary>
internal static class LeanInt
{
    /// <summary><c>Int.ediv</c>: <c>sign y * ⌊x / |y|⌋</c>, and <c>x / 0 = 0</c>.</summary>
    public static BigInteger EDiv(BigInteger x, BigInteger y)
    {
        if (y.IsZero)
        {
            return BigInteger.Zero;
        }
        var q = BigInteger.DivRem(x, y, out var r);
        if (r.Sign < 0)
        {
            q = y.Sign > 0 ? q - 1 : q + 1;
        }
        return q;
    }

    /// <summary><c>Int.emod</c>: the remainder in <c>[0, |y|)</c>, and <c>x % 0 = x</c>.</summary>
    public static BigInteger EMod(BigInteger x, BigInteger y)
    {
        if (y.IsZero)
        {
            return x;
        }
        var r = BigInteger.Remainder(x, y);
        return r.Sign < 0 ? r + BigInteger.Abs(y) : r;
    }

    /// <summary>
    /// <c>Int.bmod x m</c> (DivMod/Basic.lean 318): <c>let r := x % m; if r &lt; (m + 1) / 2 then r else r - m</c>.
    /// </summary>
    public static BigInteger BMod(BigInteger x, BigInteger m)
    {
        var r = EMod(x, m);
        return r < EDiv(m + 1, 2) ? r : r - m;
    }

    /// <summary><c>Nat</c> subtraction, truncated at zero.</summary>
    public static BigInteger NatSub(BigInteger x, BigInteger y) => x >= y ? x - y : BigInteger.Zero;

    /// <summary><c>Nat</c> division, with <c>x / 0 = 0</c>.</summary>
    public static BigInteger NatDiv(BigInteger x, BigInteger y) => y.IsZero ? BigInteger.Zero : BigInteger.Divide(x, y);

    /// <summary><c>x ^ n</c> for a natural exponent; null when the exponent is too large to compute.</summary>
    public static BigInteger? Pow(BigInteger x, BigInteger n) =>
        n.Sign < 0 || n > int.MaxValue ? null : BigInteger.Pow(x, (int)n);

    /// <summary>Lean's <c>Int.sign</c>.</summary>
    public static BigInteger Sign(BigInteger x) => x.Sign;
}

/// <summary>
/// <c>Lean.Omega.Coeffs</c>, which is <c>List Int</c> (Init/Omega/Coeffs.lean, IntList.lean). The length is part of the
/// value: <c>[1]</c> and <c>[1, 0]</c> are different keys and different literals, as in Lean, so every operation keeps
/// the length Init's definition gives.
/// </summary>
internal sealed class Coeffs : IEquatable<Coeffs>, IComparable<Coeffs>
{
    /// <summary>The empty list.</summary>
    public static readonly Coeffs Nil = new([]);

    public Coeffs(ImmutableArray<BigInteger> values)
    {
        Values = values.IsDefault ? [] : values;
    }

    /// <summary>The entries.</summary>
    public ImmutableArray<BigInteger> Values { get; }

    /// <summary><c>Coeffs.length</c>.</summary>
    public int Length => Values.Length;

    /// <summary>Builds a list from its entries.</summary>
    public static Coeffs Of(params IEnumerable<BigInteger> values) => new([.. values]);

    /// <summary><c>IntList.get</c>: the <paramref name="i"/>-th entry, or 0 past the end.</summary>
    public BigInteger Get(int i) => i < Values.Length ? Values[i] : BigInteger.Zero;

    /// <summary>
    /// <c>IntList.set xs i y</c>: replaces the <paramref name="i"/>-th entry, padding with zeros past the end.
    /// </summary>
    public Coeffs Set(int i, BigInteger y)
    {
        var b = ImmutableArray.CreateBuilder<BigInteger>(Math.Max(Values.Length, i + 1));
        b.AddRange(Values);
        while (b.Count <= i)
        {
            b.Add(BigInteger.Zero);
        }
        b[i] = y;
        return new(b.MoveToImmutable());
    }

    /// <summary><c>List.zipWithAll</c> with missing entries read as 0: the result is as long as the longer list.</summary>
    private static Coeffs ZipWithAll(Coeffs xs, Coeffs ys, Func<BigInteger, BigInteger, BigInteger> f)
    {
        int n = Math.Max(xs.Length, ys.Length);
        var b = ImmutableArray.CreateBuilder<BigInteger>(n);
        for (int i = 0; i < n; i++)
        {
            b.Add(f(xs.Get(i), ys.Get(i)));
        }
        return new(b.MoveToImmutable());
    }

    private Coeffs Map(Func<BigInteger, BigInteger> f) => new([.. Values.Select(f)]);

    /// <summary><c>IntList.add</c>.</summary>
    public static Coeffs Add(Coeffs xs, Coeffs ys) => ZipWithAll(xs, ys, (x, y) => x + y);

    /// <summary><c>IntList.sub</c>.</summary>
    public static Coeffs Sub(Coeffs xs, Coeffs ys) => ZipWithAll(xs, ys, (x, y) => x - y);

    /// <summary><c>IntList.neg</c>.</summary>
    public Coeffs Neg() => Map(x => -x);

    /// <summary><c>IntList.smul xs i</c>, printed <c>i * xs</c>.</summary>
    public Coeffs Smul(BigInteger i) => Map(x => i * x);

    /// <summary><c>IntList.sdiv xs g</c>: each entry divided by <paramref name="g"/> (<c>Int.ediv</c>).</summary>
    public Coeffs Sdiv(BigInteger g) => Map(x => LeanInt.EDiv(x, g));

    /// <summary><c>IntList.combo a xs b ys</c>: <c>a * x + b * y</c> entrywise, as long as the longer list.</summary>
    public static Coeffs Combo(BigInteger a, Coeffs xs, BigInteger b, Coeffs ys) => ZipWithAll(xs, ys, (x, y) => a * x + b * y);

    /// <summary><c>IntList.bmod x m</c>: <c>Int.bmod</c> of each entry.</summary>
    public Coeffs Bmod(BigInteger m) => Map(x => LeanInt.BMod(x, m));

    /// <summary><c>IntList.gcd</c>: <c>foldr (fun x g => Nat.gcd x.natAbs g) 0</c>.</summary>
    public BigInteger Gcd()
    {
        var g = BigInteger.Zero;
        for (int i = Values.Length - 1; i >= 0; i--)
        {
            g = BigInteger.GreatestCommonDivisor(BigInteger.Abs(Values[i]), g);
        }
        return g;
    }

    /// <summary><c>IntList.leading</c>: the first non-zero entry, or 0.</summary>
    public BigInteger Leading()
    {
        foreach (var x in Values)
        {
            if (!x.IsZero)
            {
                return x;
            }
        }
        return BigInteger.Zero;
    }

    /// <summary><c>Coeffs.isZero</c>: every entry is 0.</summary>
    public bool IsZero => Values.All(x => x.IsZero);

    /// <summary><c>Coeffs.findIdx? (·.natAbs = 1)</c>.</summary>
    public int? FindUnit()
    {
        for (int i = 0; i < Values.Length; i++)
        {
            if (BigInteger.Abs(Values[i]).IsOne)
            {
                return i;
            }
        }
        return null;
    }

    public bool Equals(Coeffs? other) => other is not null && Values.AsSpan().SequenceEqual(other.Values.AsSpan());

    public override bool Equals(object? obj) => obj is Coeffs c && Equals(c);

    public override int GetHashCode()
    {
        var h = new HashCode();
        foreach (var x in Values)
        {
            h.Add(x);
        }
        return h.ToHashCode();
    }

    /// <summary>Lean's <c>List.lt</c>: lexicographic, a proper prefix first.</summary>
    public int CompareTo(Coeffs? other)
    {
        if (other is null)
        {
            return 1;
        }
        for (int i = 0; ; i++)
        {
            if (i == Length)
            {
                return i == other.Length ? 0 : -1;
            }
            if (i == other.Length)
            {
                return 1;
            }
            int c = Values[i].CompareTo(other.Values[i]);
            if (c != 0)
            {
                return c;
            }
        }
    }

    /// <summary>Lean's <c>toString</c> of a list: <c>[1, -2, 0]</c>.</summary>
    public override string ToString() => "[" + string.Join(", ", Values.Select(v => v.ToString(CultureInfo.InvariantCulture))) + "]";
}

/// <summary>
/// <c>Lean.Omega.Constraint</c> (Init/Omega/Constraint.lean): an interval with optional ends, which a linear combination
/// of the atoms must lie in.
/// </summary>
/// <param name="Lower">The lower bound, or none.</param>
/// <param name="Upper">The upper bound, or none.</param>
internal readonly record struct Constraint(BigInteger? Lower, BigInteger? Upper)
{
    /// <summary><c>Constraint.trivial</c>: <c>⟨none, none⟩</c>.</summary>
    public static Constraint Trivial => new(null, null);

    /// <summary><c>Constraint.impossible</c>: <c>⟨some 1, some 0⟩</c>.</summary>
    public static Constraint Impossible => new(BigInteger.One, BigInteger.Zero);

    /// <summary><c>Constraint.exact r</c>.</summary>
    public static Constraint Exact(BigInteger r) => new(r, r);

    /// <summary><c>Constraint.sat c t</c>.</summary>
    public bool Sat(BigInteger t) => (Lower is not { } l || l <= t) && (Upper is not { } u || t <= u);

    /// <summary><c>Constraint.isImpossible</c>: both ends, the upper below the lower.</summary>
    public bool IsImpossible => Lower is { } x && Upper is { } y && y < x;

    /// <summary><c>Constraint.isExact</c>: both ends, equal.</summary>
    public bool IsExact => Lower is { } x && Upper is { } y && x == y;

    private Constraint Map(Func<BigInteger, BigInteger> f) => new(Lower is { } l ? f(l) : null, Upper is { } u ? f(u) : null);

    /// <summary><c>Constraint.flip</c>: swaps the ends.</summary>
    public Constraint Flip() => new(Upper, Lower);

    /// <summary><c>Constraint.neg</c>: <c>c.flip.map (- ·)</c>.</summary>
    public Constraint Neg() => Flip().Map(x => -x);

    /// <summary><c>Constraint.scale k c</c> (Constraint.lean 136).</summary>
    public Constraint Scale(BigInteger k)
    {
        if (k.IsZero)
        {
            return IsImpossible ? this : new(BigInteger.Zero, BigInteger.Zero);
        }
        return k.Sign > 0 ? Map(x => k * x) : Flip().Map(x => k * x);
    }

    /// <summary><c>Constraint.add</c>: an end is present when both are.</summary>
    public static Constraint Add(Constraint x, Constraint y) => new(
        x.Lower is { } a && y.Lower is { } b ? a + b : null,
        x.Upper is { } c && y.Upper is { } d ? c + d : null);

    /// <summary><c>Constraint.combo a x b y</c>: <c>add (scale a x) (scale b y)</c>.</summary>
    public static Constraint Combo(BigInteger a, Constraint x, BigInteger b, Constraint y) => Add(x.Scale(a), y.Scale(b));

    /// <summary><c>Constraint.combine</c>: the intersection, by <c>Option.merge max</c> and <c>Option.merge min</c>.</summary>
    public Constraint Combine(Constraint y) => new(
        Lower is { } a ? (y.Lower is { } b ? BigInteger.Max(a, b) : a) : y.Lower,
        Upper is { } c ? (y.Upper is { } d ? BigInteger.Min(c, d) : c) : y.Upper);

    /// <summary><c>Constraint.div c k</c>: <c>lowerBound.map (- ((- x) / k))</c>, <c>upperBound.map (· / k)</c>.</summary>
    public Constraint Div(BigInteger k) => new(
        Lower is { } x ? -LeanInt.EDiv(-x, k) : null,
        Upper is { } y ? LeanInt.EDiv(y, k) : null);

    /// <summary>Lean's <c>toString</c> of a constraint (Constraint.lean 50).</summary>
    public override string ToString() => (Lower, Upper) switch
    {
        (null, null) => "(-∞, ∞)",
        (null, { } y) => $"(-∞, {y}]",
        ({ } x, null) => $"[{x}, ∞)",
        ({ } x, { } y) => x == y ? $"{{{x}}}" : $"[{x}, {y}]",
    };
}

/// <summary>
/// The normalisation steps of Init/Omega/Constraint.lean 228-336 on a constraint and its coefficients. The proofs cite
/// <c>tidy_sat</c> and <c>bmod_sat</c>, whose statements the kernel evaluates, so each function here is Init's.
/// </summary>
internal static class Tidy
{
    /// <summary><c>normalize?</c>: divides through by the gcd; none when the gcd is 1.</summary>
    public static (Constraint, Coeffs)? NormalizeQ(Constraint s, Coeffs x)
    {
        var gcd = x.Gcd();
        if (gcd.IsZero)
        {
            return (s.Sat(BigInteger.Zero) ? Constraint.Trivial : Constraint.Impossible, x);
        }
        if (gcd.IsOne)
        {
            return null;
        }
        return (s.Div(gcd), x.Sdiv(gcd));
    }

    /// <summary><c>normalize</c>: <c>normalize? p |>.getD p</c>.</summary>
    public static (Constraint, Coeffs) Normalize(Constraint s, Coeffs x) => NormalizeQ(s, x) ?? (s, x);

    /// <summary><c>positivize?</c>: negates when the leading coefficient is negative; none otherwise.</summary>
    public static (Constraint, Coeffs)? PositivizeQ(Constraint s, Coeffs x) =>
        x.Leading().Sign >= 0 ? null : (s.Neg(), x.Smul(BigInteger.MinusOne));

    /// <summary><c>positivize</c>: <c>positivize? p |>.getD p</c>.</summary>
    public static (Constraint, Coeffs) Positivize(Constraint s, Coeffs x) => PositivizeQ(s, x) ?? (s, x);

    /// <summary><c>tidy?</c>: <c>positivize?</c> then <c>normalize</c>, or <c>normalize?</c> alone; none if neither acts.</summary>
    public static (Constraint, Coeffs)? TidyQ(Constraint s, Coeffs x) =>
        PositivizeQ(s, x) is var (s1, x1) ? Normalize(s1, x1) : NormalizeQ(s, x);

    /// <summary><c>tidy</c>: <c>tidy? p |>.getD p</c>.</summary>
    public static (Constraint, Coeffs) TidyPair(Constraint s, Coeffs x) => TidyQ(s, x) ?? (s, x);

    /// <summary><c>bmod_coeffs m i x</c>: <c>Coeffs.set (Coeffs.bmod x m) i m</c>.</summary>
    public static Coeffs BmodCoeffs(BigInteger m, int i, Coeffs x) => x.Bmod(m).Set(i, m);
}

/// <summary><c>Lean.Omega.LinearCombo</c> (Init/Omega/LinearCombo.lean): a constant plus coefficients of the atoms.</summary>
/// <param name="Const">The constant term.</param>
/// <param name="Coeffs">The coefficients of the atoms.</param>
internal sealed record LinearCombo(BigInteger Const, Coeffs Coeffs)
{
    /// <summary>The constant <paramref name="c"/>, with no coefficients.</summary>
    public static LinearCombo Constant(BigInteger c) => new(c, Coeffs.Nil);

    /// <summary><c>LinearCombo.coordinate i</c>: <c>⟨0, Coeffs.set [] i 1⟩</c>.</summary>
    public static LinearCombo Coordinate(int i) => new(BigInteger.Zero, Coeffs.Nil.Set(i, BigInteger.One));

    /// <summary><c>LinearCombo.add</c>.</summary>
    public static LinearCombo operator +(LinearCombo l1, LinearCombo l2) => new(l1.Const + l2.Const, Coeffs.Add(l1.Coeffs, l2.Coeffs));

    /// <summary><c>LinearCombo.sub</c>.</summary>
    public static LinearCombo operator -(LinearCombo l1, LinearCombo l2) => new(l1.Const - l2.Const, Coeffs.Sub(l1.Coeffs, l2.Coeffs));

    /// <summary><c>LinearCombo.neg</c>.</summary>
    public static LinearCombo operator -(LinearCombo l) => new(-l.Const, l.Coeffs.Neg());

    /// <summary><c>LinearCombo.smul lc i</c>, printed <c>i * lc</c>.</summary>
    public LinearCombo Smul(BigInteger i) => new(i * Const, Coeffs.Smul(i));

    /// <summary>
    /// <c>LinearCombo.mul</c>: <c>l₂.const * l₁ + l₁.const * l₂ - {const := l₁.const * l₂.const}</c>, meaningful when one
    /// side is constant.
    /// </summary>
    public static LinearCombo Mul(LinearCombo l1, LinearCombo l2) =>
        l1.Smul(l2.Const) + l2.Smul(l1.Const) - Constant(l1.Const * l2.Const);
}
