using LeanSharp.Cic;

namespace LeanSharp.Cic.Tests;

public class NameTests
{
    [Theory]
    [InlineData("Nat")]
    [InlineData("Nat.add_comm")]
    [InlineData("_private.Init.Core.0.foo")]
    [InlineData("«a.b».c")]
    [InlineData("Foo.«42»")]
    [InlineData("α.β₁")]
    public void ParseAndToStringRoundTrip(string text)
    {
        var name = Name.Parse(text);
        Assert.Equal(text, name.ToString());
        Assert.Equal(name, Name.Parse(name.ToString()));
    }

    [Fact]
    public void ParseDistinguishesNumericComponents()
    {
        var name = Name.Parse("foo.0.bar");
        var parts = name.Components();
        Assert.Equal([NameKind.Str, NameKind.Num, NameKind.Str], parts.Select(p => p.Kind));
        Assert.Equal(0UL, parts[1].NumericComponent);
        Assert.Equal(NameKind.Str, Name.Parse("foo.«0»").Kind);
    }

    [Theory]
    [InlineData("a..b")]
    [InlineData(".a")]
    [InlineData("a.")]
    [InlineData("«unterminated")]
    public void ParseRejectsMalformedNames(string text) =>
        Assert.Throws<FormatException>(() => Name.Parse(text));

    [Fact]
    public void EmptyStringParsesToAnonymous()
    {
        Assert.Same(Name.Anonymous, Name.Parse(""));
        Assert.Equal("[anonymous]", Name.Anonymous.ToString());
    }

    [Fact]
    public void SeparatelyBuiltNamesAreEqualWithEqualHashes()
    {
        var a = Name.From("Nat", "add_comm");
        var b = Name.Anonymous.Append("Nat").Append("add_comm");
        Assert.NotSame(a, b);
        Assert.Equal(a, b);
        Assert.True(a == b);
        Assert.Equal(a.GetHashCode(), b.GetHashCode());
        Assert.NotEqual(a, Name.From("Nat", "add_assoc"));
        Assert.NotEqual(Name.From("x").Append(1), Name.From("x", "1"));
    }

    [Fact]
    public void HashIsDeterministicAcrossProcesses()
    {
        // Pinned so that an accidental switch to a per-process randomized hash is caught.
        Assert.Equal(0xA36FDD6F698D46CEUL, Name.Parse("Nat.add_comm").Hash64);
    }

    [Fact]
    public void StartsWithChecksComponentPrefixes()
    {
        var name = Name.Parse("Nat.add_comm");
        Assert.True(name.StartsWith(Name.Parse("Nat")));
        Assert.True(name.StartsWith(name));
        Assert.True(name.StartsWith(Name.Anonymous));
        Assert.False(name.StartsWith(Name.Parse("Na")));
        Assert.False(Name.Parse("Nat").StartsWith(name));
    }

    [Fact]
    public void OrderingIsComponentwiseWithNumbersFirst()
    {
        var sorted = new[] { "b", "a.b", "a", "a.2", "a.10", "a.x" }.Select(Name.Parse).Order().Select(n => n.ToString());
        Assert.Equal(["a", "a.2", "a.10", "a.b", "a.x", "b"], sorted);
    }
}
