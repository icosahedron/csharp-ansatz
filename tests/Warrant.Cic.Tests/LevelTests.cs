using Warrant.Cic;

namespace Warrant.Cic.Tests;

public class LevelTests
{
    private static readonly Level U = Level.Param(Name.Parse("u"));
    private static readonly Level V = Level.Param(Name.Parse("v"));

    [Fact]
    public void StructuralEquality()
    {
        Assert.Equal(Level.Max(U, Level.Succ(V)), Level.Max(Level.Param(Name.Parse("u")), Level.Succ(Level.Param(Name.Parse("v")))));
        Assert.NotEqual(Level.Max(U, V), Level.IMax(U, V));
        Assert.NotEqual(Level.Max(U, V), Level.Max(V, U)); // equal up to the algebra, but not structurally
    }

    [Fact]
    public void HasParamPropagates()
    {
        Assert.False(Level.Succ(Level.Zero).HasParam);
        Assert.True(Level.Succ(U).HasParam);
        Assert.True(Level.IMax(Level.Zero, U).HasParam);
    }

    [Fact]
    public void ToStringUsesLeanNotation()
    {
        Assert.Equal("0", Level.Zero.ToString());
        Assert.Equal("2", Level.Succ(Level.One).ToString());
        Assert.Equal("u+1", Level.Succ(U).ToString());
        Assert.Equal("max u (v+1)", Level.Max(U, Level.Succ(V)).ToString());
        Assert.Equal("(imax u v)+1", Level.Succ(Level.IMax(U, V)).ToString());
    }
}
