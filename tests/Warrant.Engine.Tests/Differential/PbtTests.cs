using System.Text.RegularExpressions;
using FsCheck;
using FsCheck.Fluent;
using Xunit.Sdk;

namespace Warrant.Engine.Tests.Differential;

/// <summary>
/// The property-test helper (M5a KTD26): a pinned seed, replay from the seed a failure prints, and the counts the
/// environment selects. The environment is passed in, so these tests do not depend on the variables of the run.
/// </summary>
public sealed partial class PbtTests
{
    private static Func<string, string?> Env(params (string Name, string Value)[] variables) =>
        name => variables.FirstOrDefault(v => v.Name == name).Value;

    private static List<int> Drawn(Config config)
    {
        var drawn = new List<int>();
        Pbt.Check(Prop.ForAll(Generators.Int32s, x => drawn.Add(x)), config);
        return drawn;
    }

    [Fact]
    public void AnUnsetSeedGivesTheSameInputsOnEveryRun()
    {
        var first = Drawn(Pbt.Config(200, Env()));
        Assert.Equal(200, first.Count);
        Assert.Equal(first, Drawn(Pbt.Config(200, Env())));
        Assert.NotEqual(first, Drawn(Pbt.Config(200, Env((Pbt.SeedVariable, "7,3")))));
    }

    [Fact]
    public void AFailureIsShrunkToABoundaryAndReplaysFromThePrintedSeed()
    {
        var property = Prop.ForAll(Generators.Int32s, x => x < 1000);
        var failure = Assert.Throws<XunitException>(() => Pbt.Check(property, Pbt.Config(100, Env((Pbt.SeedVariable, "random")))));
        Assert.Contains("Shrunk:\n2147483647", failure.Message.ReplaceLineEndings("\n"), StringComparison.Ordinal);
        var seed = ReplayHint().Match(failure.Message);
        Assert.True(seed.Success, failure.Message);

        var replayed = Assert.Throws<XunitException>(() => Pbt.Check(property, Pbt.Config(100, Env((Pbt.SeedVariable, seed.Groups[1].Value)))));
        Assert.Equal(failure.Message, replayed.Message);
    }

    [Fact]
    public void TheEnvironmentSelectsTheCount()
    {
        Assert.Equal(150, Pbt.Count(150, Env()));
        Assert.Equal(Pbt.LongCount, Pbt.Count(150, Env((Pbt.LongVariable, "1"))));
        Assert.Equal(25, Pbt.Count(150, Env((Pbt.LongVariable, "1"), (Pbt.CountVariable, "25"))));
        Assert.Equal(Pbt.LongCount, Drawn(Pbt.Config(150, Env((Pbt.LongVariable, "1")))).Count);
    }

    [Fact]
    public void ASeedIsAnOddGammaPair()
    {
        Assert.Equal(Pbt.DefaultSeed, Pbt.Seed(null));
        Assert.Null(Pbt.Seed("random"));
        Assert.Equal((12UL, 7UL), Pbt.Seed("(12,7)"));
        Assert.Throws<ArgumentException>(() => Pbt.Seed("12,8"));
    }

    [GeneratedRegex($"Replay with {Pbt.SeedVariable}=(\\d+,\\d+)$")]
    private static partial Regex ReplayHint();
}
