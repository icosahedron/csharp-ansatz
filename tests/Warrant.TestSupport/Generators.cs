using FsCheck;
using FsCheck.Fluent;

namespace Warrant.TestSupport;

/// <summary>
/// Boundary-biased FsCheck generators for <c>int</c> and <c>long</c> (plan U9, KTD19). FsCheck's default integer
/// generators stay near zero, so they never reach the overflow boundaries where a wrong operator row shows. These
/// generators yield the boundary values first (one per size, while FsCheck's size is small) and then uniform values
/// over the whole range, with boundaries still mixed in.
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

    /// <summary><see cref="Int32Values"/> as an arbitrary (no shrinking).</summary>
    public static Arbitrary<int> Int32s { get; } = Int32Values.ToArbitrary();

    /// <summary><see cref="Int64Values"/> as an arbitrary (no shrinking).</summary>
    public static Arbitrary<long> Int64s { get; } = Int64Values.ToArbitrary();

    /// <summary>Independent pairs of <see cref="Int32Values"/>.</summary>
    public static Arbitrary<(int, int)> Int32Pairs { get; } = Pair(Int32Values).ToArbitrary();

    /// <summary>Independent pairs of <see cref="Int64Values"/>.</summary>
    public static Arbitrary<(long, long)> Int64Pairs { get; } = Pair(Int64Values).ToArbitrary();

    /// <summary>Every ordered pair of boundary values (49 pairs).</summary>
    public static IEnumerable<(int, int)> Int32BoundaryPairs() =>
        from a in Int32Boundaries from b in Int32Boundaries select (a, b);

    /// <summary>Every ordered pair of boundary values (49 pairs).</summary>
    public static IEnumerable<(long, long)> Int64BoundaryPairs() =>
        from a in Int64Boundaries from b in Int64Boundaries select (a, b);

    /// <summary>Independent pairs drawn from <paramref name="gen"/>.</summary>
    public static Gen<(T, T)> Pair<T>(Gen<T> gen) => gen.SelectMany(a => gen.Select(b => (a, b)));

    private static Gen<T> Biased<T>(IReadOnlyList<T> boundaries, Gen<T> uniform)
    {
        var mixed = Gen.Frequency<T>((1, Gen.Elements<T>(boundaries)), (3, uniform));
        return Gen.Sized<T>(size => size < boundaries.Count ? Gen.Constant(boundaries[size]) : mixed);
    }
}
