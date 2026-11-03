using FsCheck;
using FsCheck.Fluent;

namespace Warrant.TestSupport;

/// <summary>
/// Boundary-biased FsCheck generators for <c>int</c> and <c>long</c> (plan U9, KTD19). FsCheck's default integer
/// generators stay near zero, so they never reach the overflow boundaries where a wrong operator row shows. These
/// generators yield the boundary values first (one per size, while FsCheck's size is small) and then uniform values
/// over the whole range, with boundaries still mixed in. Their shrinkers move toward 0 and the boundary values
/// (M5a KTD26), and <see cref="ShrinkFields"/> and <see cref="ShrinkTowardFirst"/> shrink records and enums.
/// </summary>
public static class Generators
{
    /// <summary>The <c>int</c> boundaries: <c>MinValue</c>, <c>MinValue+1</c>, -1, 0, 1, <c>MaxValue-1</c>, <c>MaxValue</c>.</summary>
    public static IReadOnlyList<int> Int32Boundaries { get; } =
        [int.MinValue, int.MinValue + 1, -1, 0, 1, int.MaxValue - 1, int.MaxValue];

    /// <summary>The <c>long</c> boundaries, as <see cref="Int32Boundaries"/>.</summary>
    public static IReadOnlyList<long> Int64Boundaries { get; } =
        [long.MinValue, long.MinValue + 1, -1, 0, 1, long.MaxValue - 1, long.MaxValue];

    /// <summary>A uniform <c>int</c> over the whole range.</summary>
    public static Gen<int> UniformInt32 { get; } =
        Gen.Choose(0, 0xFFFF).SelectMany(hi => Gen.Choose(0, 0xFFFF).Select(lo => unchecked((int)(((uint)hi << 16) | (uint)lo))));

    /// <summary>A uniform <c>long</c> over the whole range.</summary>
    public static Gen<long> UniformInt64 { get; } =
        UniformInt32.SelectMany(hi => UniformInt32.Select(lo => unchecked((long)(((ulong)(uint)hi << 32) | (uint)lo))));

    /// <summary>Boundaries first (by size), then a mix of one part boundary to three parts uniform.</summary>
    public static Gen<int> Int32Values { get; } = Biased(Int32Boundaries, UniformInt32);

    /// <summary>Boundaries first (by size), then a mix of one part boundary to three parts uniform.</summary>
    public static Gen<long> Int64Values { get; } = Biased(Int64Boundaries, UniformInt64);

    /// <summary><see cref="Int32Values"/> as an arbitrary, shrinking by <see cref="ShrinkInt32"/>.</summary>
    public static Arbitrary<int> Int32s { get; } = Arb.From(Int32Values, ShrinkInt32);

    /// <summary><see cref="Int64Values"/> as an arbitrary, shrinking by <see cref="ShrinkInt64"/>.</summary>
    public static Arbitrary<long> Int64s { get; } = Arb.From(Int64Values, ShrinkInt64);

    /// <summary>Independent pairs of <see cref="Int32Values"/>, shrinking one component at a time.</summary>
    public static Arbitrary<(int, int)> Int32Pairs { get; } = Arb.From(Pair(Int32Values), p => ShrinkPair(p, ShrinkInt32));

    /// <summary>Independent pairs of <see cref="Int64Values"/>, shrinking one component at a time.</summary>
    public static Arbitrary<(long, long)> Int64Pairs { get; } = Arb.From(Pair(Int64Values), p => ShrinkPair(p, ShrinkInt64));

    /// <summary>Every ordered pair of boundary values (49 pairs).</summary>
    public static IEnumerable<(int, int)> Int32BoundaryPairs() =>
        from a in Int32Boundaries from b in Int32Boundaries select (a, b);

    /// <summary>Every ordered pair of boundary values (49 pairs).</summary>
    public static IEnumerable<(long, long)> Int64BoundaryPairs() =>
        from a in Int64Boundaries from b in Int64Boundaries select (a, b);

    /// <summary>Independent pairs drawn from <paramref name="gen"/>.</summary>
    public static Gen<(T, T)> Pair<T>(Gen<T> gen) => gen.SelectMany(a => gen.Select(b => (a, b)));

    /// <summary>
    /// Smaller candidates for a failing <c>int</c>: the boundary values first, in the order 0, 1, -1, <c>MinValue</c>,
    /// <c>MaxValue</c>, <c>MinValue+1</c>, <c>MaxValue-1</c> (a boundary value shrinks only to those before it); then,
    /// for any other value, the point halfway to its nearest boundary value and the next value toward it. A failure is
    /// therefore reported at a boundary value, or at the end of the failing range nearest one, not at a random value
    /// such as -1216.
    /// </summary>
    public static IEnumerable<int> ShrinkInt32(int value) => ShrinkToward(value, Int32ShrinkOrder).Select(v => (int)v);

    /// <summary>Smaller candidates for a failing <c>long</c>, as <see cref="ShrinkInt32"/>.</summary>
    public static IEnumerable<long> ShrinkInt64(long value) => ShrinkToward(value, Int64ShrinkOrder).Select(v => (long)v);

    /// <summary>A record's fields shrunk one at a time, in field order, each by its own shrinker, the others unchanged.</summary>
    public static IEnumerable<object?[]> ShrinkFields(IReadOnlyList<object?> fields, IReadOnlyList<Func<object?, IEnumerable<object?>>> shrinkers)
    {
        ArgumentNullException.ThrowIfNull(fields);
        ArgumentNullException.ThrowIfNull(shrinkers);
        for (int i = 0; i < fields.Count; i++)
        {
            foreach (var smaller in shrinkers[i](fields[i]))
            {
                var candidate = fields.ToArray();
                candidate[i] = smaller;
                yield return candidate;
            }
        }
    }

    /// <summary>
    /// The members listed before <paramref name="value"/>, first member first: an enum or closed value shrinks toward
    /// its first member. A value not in the list (an unnamed enum value) shrinks to any member.
    /// </summary>
    public static IEnumerable<T> ShrinkTowardFirst<T>(IReadOnlyList<T> members, T value)
    {
        ArgumentNullException.ThrowIfNull(members);
        for (int i = 0; i < members.Count; i++)
        {
            if (EqualityComparer<T>.Default.Equals(members[i], value))
            {
                return members.Take(i);
            }
        }
        return members;
    }

    private static IEnumerable<(T, T)> ShrinkPair<T>((T A, T B) pair, Func<T, IEnumerable<T>> shrink) =>
        shrink(pair.A).Select(a => (a, pair.B)).Concat(shrink(pair.B).Select(b => (pair.A, b)));

    private static readonly Int128[] Int32ShrinkOrder = [0, 1, -1, int.MinValue, int.MaxValue, int.MinValue + 1, int.MaxValue - 1];

    private static readonly Int128[] Int64ShrinkOrder = [0, 1, -1, long.MinValue, long.MaxValue, long.MinValue + 1, long.MaxValue - 1];

    /// <summary>
    /// Shrinking terminates: a boundary value's candidates come earlier in <paramref name="order"/>, and any other
    /// value's candidates are boundary values or strictly closer to its nearest boundary value.
    /// </summary>
    private static IEnumerable<Int128> ShrinkToward(Int128 value, Int128[] order)
    {
        var rank = Array.IndexOf(order, value);
        if (rank >= 0)
        {
            return order.Take(rank);
        }
        var nearest = order.MinBy(b => Int128.Abs(value - b));
        var step = nearest > value ? 1 : -1;
        var half = value + (nearest - value) / 2;
        Int128[] closer = half == value ? [value + step] : [half, value + step];
        return order.Concat(closer.Distinct().Where(c => Array.IndexOf(order, c) < 0));
    }

    private static Gen<T> Biased<T>(IReadOnlyList<T> boundaries, Gen<T> uniform)
    {
        var mixed = Gen.Frequency<T>((1, Gen.Elements<T>(boundaries)), (3, uniform));
        return Gen.Sized<T>(size => size < boundaries.Count ? Gen.Constant(boundaries[size]) : mixed);
    }
}
