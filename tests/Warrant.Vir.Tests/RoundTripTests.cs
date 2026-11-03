namespace Warrant.Vir.Tests;

public class RoundTripTests
{
    public static TheoryData<string> UnitKeys()
    {
        var data = new TheoryData<string>();
        foreach (var unit in Samples.All())
        {
            data.Add(unit.Key);
        }
        return data;
    }

    [Theory]
    [MemberData(nameof(UnitKeys))]
    public void WritingThenReadingGivesAnEqualUnit(string key)
    {
        var unit = Samples.All().Single(u => u.Key == key);
        var bytes = VirWriter.Write(unit);

        var read = VirReader.Read(bytes);

        Assert.Equal(unit, read);
        Assert.Equal(bytes, VirWriter.Write(read));
    }

    [Fact]
    public void TheSamplesUseEveryNodeKind()
    {
        var used = Samples.All().SelectMany(VirTree.PreOrder).Select(n => n.GetType()).ToHashSet();
        var all = typeof(VirNode).Assembly.GetTypes()
            .Where(t => !t.IsAbstract && typeof(VirNode).IsAssignableFrom(t))
            .ToList();

        Assert.Equal(30, all.Count); // 18 expression, 6 statement and 6 pattern kinds
        Assert.Empty(all.Where(t => !used.Contains(t)).Select(t => t.Name));
    }

    [Fact]
    public void SixtyFourBitExtremesSurviveTheRoundTrip()
    {
        var read = VirReader.Read(VirWriter.Write(Samples.Everything()));

        var lits = VirTree.PreOrder(read).OfType<LitExpr>().Where(l => l.Type == VirType.Int64).Select(l => l.Value).ToList();
        Assert.Contains(long.MinValue, lits);
        Assert.Contains(long.MaxValue, lits);
        var closed = (ClosedDefinition)VirReader.Read(VirWriter.Write(Samples.ClosedEnumType())).Definition!;
        Assert.Equal(long.MaxValue, closed.Members[1].Value);
    }
}
