using LeanSharp.Cic;

namespace LeanSharp.Kernel.Tests;

public class LevelOpsTests
{
    private static readonly Level U = Level.Param(Name.Parse("u"));
    private static readonly Level V = Level.Param(Name.Parse("v"));
    private static readonly Level Zero = Level.Zero;
    private static readonly Level One = Level.One;

    private static Level S(Level l, int k = 1) => LevelOps.MkSucc(l, k);

    public static TheoryData<Level, Level> Equivalent => new()
    {
        { Level.Max(U, U), U },
        { Level.Max(S(U), U), S(U) },
        { Level.Max(U, V), Level.Max(V, U) },
        { Level.Max(U, Level.Max(V, U)), Level.Max(V, U) },
        { Level.IMax(U, Zero), Zero },
        { Level.IMax(Zero, U), U },
        { Level.IMax(One, U), U },
        { Level.IMax(U, S(V)), Level.Max(U, S(V)) },
        { Level.Max(One, S(U)), S(U) },
        { S(Level.Max(U, V)), Level.Max(S(U), S(V)) },
        { Level.Max(Zero, U), U },
        { Level.Max(S(Zero, 2), S(Zero, 3)), S(Zero, 3) },
    };

    [Theory]
    [MemberData(nameof(Equivalent))]
    public void EquivalentLevelsNormalizeAlike(Level a, Level b)
    {
        Assert.True(LevelOps.IsEquivalent(a, b), $"{a} ≡ {b}");
        Assert.True(LevelOps.IsGeq(a, b) && LevelOps.IsGeq(b, a));
    }

    public static TheoryData<Level, Level> NotEquivalent => new()
    {
        { U, V },
        { U, S(U) },
        { Level.Max(U, V), U },
        { Level.IMax(U, V), Level.Max(U, V) }, // differ when v = 0
        { One, Zero },
    };

    [Theory]
    [MemberData(nameof(NotEquivalent))]
    public void DistinctLevelsAreNotEquivalent(Level a, Level b) => Assert.False(LevelOps.IsEquivalent(a, b), $"{a} ≢ {b}");

    [Fact]
    public void GeqIsSoundForSimpleCases()
    {
        Assert.True(LevelOps.IsGeq(Level.Max(U, V), U));
        Assert.True(LevelOps.IsGeq(S(U), U));
        Assert.True(LevelOps.IsGeq(U, Zero));
        Assert.True(LevelOps.IsGeq(S(U, 2), One));
        Assert.False(LevelOps.IsGeq(U, S(U)));
        Assert.False(LevelOps.IsGeq(U, V));
        Assert.False(LevelOps.IsGeq(U, One)); // u may be 0
    }

    [Fact]
    public void ZeroTests()
    {
        Assert.True(LevelOps.IsNotZero(S(U)));
        Assert.True(LevelOps.IsNotZero(Level.Max(U, One)));
        Assert.False(LevelOps.IsNotZero(Level.IMax(One, U)));
        Assert.True(LevelOps.NormalizesToZero(Level.IMax(One, Zero)));
        Assert.True(LevelOps.NormalizesToZero(Level.Max(Zero, Zero)));
        Assert.False(LevelOps.NormalizesToZero(U));
    }

    [Fact]
    public void SmartConstructorsSimplify()
    {
        Assert.Same(U, LevelOps.MkMax(U, Zero));
        Assert.Equal(S(Zero, 3), LevelOps.MkMax(S(Zero, 2), S(Zero, 3)));
        Assert.Same(Zero, LevelOps.MkIMax(U, Zero));
        Assert.Equal(Level.Max(U, S(V)), LevelOps.MkIMax(U, S(V)));
    }

    [Fact]
    public void InstantiateSubstitutesAndSimplifies()
    {
        var names = EquatableArray.Create(Name.Parse("u"), Name.Parse("v"));
        var l = Level.IMax(S(U), V);
        Assert.Equal(Zero, LevelOps.Instantiate(l, names, EquatableArray.Create(One, Zero)));
        Assert.Equal(S(Zero, 2), LevelOps.Instantiate(l, names, EquatableArray.Create(One, One)));
        Assert.Equal(Name.Parse("w"), LevelOps.GetUndefinedParam(Level.Max(U, Level.Param(Name.Parse("w"))), names));
        Assert.Null(LevelOps.GetUndefinedParam(l, names));
    }
}
