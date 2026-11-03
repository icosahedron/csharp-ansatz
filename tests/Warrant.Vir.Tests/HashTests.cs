namespace Warrant.Vir.Tests;

public class HashTests
{
    // SHA-256 of golden/payout.json, computed independently with `sha256sum`.
    private const string GoldenPayoutHash = "51fabe50cdb12706c646ea7cb1a9e5e09ffc78fb9387f4cd12d362d6b2d76418";

    [Fact]
    public void TheGoldenUnitHashIsStable()
    {
        Assert.Equal(GoldenPayoutHash, VirHash.OfUnit(Samples.Payout()).ToString());
        Assert.Equal(GoldenPayoutHash, VirHash.OfUnit(VirReader.Read(VirWriter.Write(Samples.Payout()))).ToString());
    }

    [Fact]
    public void SpansAreNotInTheHash()
    {
        var unit = Samples.Payout();
        var near = SpanTable.Build(unit, _ => new VirSpan("PayoutRules.cs", 10, 5, 10, 20));
        var far = SpanTable.Build(unit, _ => new VirSpan("PayoutRules.cs", 99, 1, 99, 9));
        Assert.True(near.TryGetSpan(0, out var a));
        Assert.True(far.TryGetSpan(0, out var b));
        Assert.NotEqual(a, b);

        Assert.Equal(VirHash.OfUnit(unit), VirHash.OfUnit(Samples.Payout()));
    }

    [Fact]
    public void OneLiteralChangesTheUnitHash()
    {
        Assert.NotEqual(VirHash.OfUnit(Samples.Payout(zero: 0)), VirHash.OfUnit(Samples.Payout(zero: 1)));
    }

    [Fact]
    public void ACalleesBodyChangesTheCallersClosureHashButNotItsUnitHash()
    {
        var before = VirHash.Closures([Samples.Payout(zero: 0), Samples.Capped()]);
        var after = VirHash.Closures([Samples.Payout(zero: 1), Samples.Capped()]);

        Assert.NotEqual(before[Samples.CappedKey], after[Samples.CappedKey]);
        Assert.Equal(VirHash.OfUnit(Samples.Capped()), VirHash.OfUnit(Samples.Capped()));
    }

    [Fact]
    public void ClosureHashIsTheUnitHashFollowedByTheDepsClosureHashes()
    {
        var payout = Samples.Payout();
        var capped = Samples.Capped();
        var all = VirHash.Closures([capped, payout]);

        // A unit without deps: SHA-256 over its unit hash alone.
        Assert.Equal(VirHash.Sha256(VirHash.OfUnit(payout).ToByteArray()), all[Samples.PayoutKey]);
        Assert.Equal(
            VirHash.Sha256([.. VirHash.OfUnit(capped).ToByteArray(), .. all[Samples.PayoutKey].ToByteArray()]),
            all[Samples.CappedKey]);
        Assert.Equal(all[Samples.CappedKey], VirHash.Closure(capped, all));
    }

    [Fact]
    public void ClosureHashesNeedEveryDep()
    {
        Assert.Throws<KeyNotFoundException>(() => VirHash.Closures([Samples.Capped()]));
    }
}
