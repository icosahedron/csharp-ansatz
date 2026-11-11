using static Warrant.Extraction.Tests.Inline;

namespace Warrant.Extraction.Tests;

/// <summary>
/// The M6 contract surface (plan U5) at run time and where it is not a statement. What extraction reads from it (U8) is
/// in <see cref="ContractExtractionTests"/>.
/// </summary>
public class ContractSurfaceTests
{
    [Fact]
    public void ProveContractIsNotATheoremStatement()
    {
        var result = Extract("""
            public static class C
            {
                [Theorem] static Proof T() => Prove.Contract();
            }
            """);

        Assert.Equal("WRT0002 | theorem that is not Prove.That", Only(result, "M:C.T"));
    }

    [Fact]
    public void ProveContractThrowsAndTheContractMembersDoNothing()
    {
        var ex = Assert.Throws<InvalidOperationException>(() => Prove.Contract());
        Assert.Equal("[ProofFor] methods are never executed.", ex.Message);
        Spec.Requires(false);
        Spec.Ensures<int>(_ => false);
        Spec.Ensures(() => false);
        Spec.Assert(false, Tactic.VcGen());
        Assert.Equal(typeof(IComparable), new ContractForAttribute(typeof(IComparable)).Interface);
        Assert.Equal("M", new ProofForAttribute("M").Method);
    }
}
