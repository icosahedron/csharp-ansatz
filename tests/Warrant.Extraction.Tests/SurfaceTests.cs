namespace Warrant.Extraction.Tests;

public class SurfaceTests
{
    [Fact]
    public void ProveThatThrows()
    {
        var ex = Assert.Throws<InvalidOperationException>(() => Prove.That(true));
        Assert.Equal("[Theorem] methods are never executed.", ex.Message);
    }

    [Theory]
    [InlineData(false, false, true)]
    [InlineData(false, true, true)]
    [InlineData(true, false, false)]
    [InlineData(true, true, true)]
    public void SpecImpliesIsImplication(bool premise, bool conclusion, bool expected) =>
        Assert.Equal(expected, Spec.Implies(premise, conclusion));
}
