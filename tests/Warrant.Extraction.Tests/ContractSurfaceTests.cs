using static Warrant.Extraction.Tests.Inline;

namespace Warrant.Extraction.Tests;

/// <summary>
/// The M6 contract surface (plan U5) before extraction reads it (U8): each new member is treated as any call to a member
/// that is neither verified nor modelled, so a contract in verified code is rejected, never silently dropped. U8 replaces
/// these expectations.
/// </summary>
public class ContractSurfaceTests
{
    [Theory]
    [InlineData("Spec.Requires(x >= 0);", "M:Warrant.Spec.Requires(System.Boolean)")]
    [InlineData("Spec.Ensures<int>(r => r >= x);", "M:Warrant.Spec.Ensures``1(System.Func{System.Int32,System.Boolean})")]
    [InlineData("Spec.Ensures(() => x >= 0);", "M:Warrant.Spec.Ensures(System.Func{System.Boolean})")]
    [InlineData("Spec.Assert(x >= 0);", "M:Warrant.Spec.Assert(System.Boolean,Warrant.Tactic[])")]
    [InlineData("Spec.Assert(x >= 0, Tactic.VcGen(), Tactic.Omega());", "M:Warrant.Spec.Assert(System.Boolean,Warrant.Tactic[])")]
    public void AContractCallInVerifiedCodeIsStillNotAVerifiedMember(string statement, string construct)
    {
        var result = Extract($$"""
            public static class C
            {
                [Verified]
                public static int Id(int x)
                {
                    {{statement}}
                    return x;
                }
            }
            """);

        Assert.Equal("WRT0005 | " + construct, Only(result, "M:C.Id(System.Int32)"));
    }

    [Fact]
    public void AProofForMethodAndAContractClassAreIgnored()
    {
        var result = Extract("""
            public interface IStore { int Get(int id); }

            [ContractFor(typeof(IStore))]
            internal abstract class StoreContract : IStore
            {
                public int Get(int id) { Spec.Requires(id > 0); Spec.Ensures<int>(r => r >= 0); return default!; }
            }

            public static class C
            {
                [Verified] public static int Id(int x) => x;

                [ProofFor(nameof(Id))]
                static Proof IdProof() => Prove.Contract().By(Tactic.VcGen(), Tactic.Omega());
            }
            """);

        Assert.Empty(result.Diagnostics);
        Assert.Equal(["M:C.Id(System.Int32)"], result.Units.Select(u => u.Key));
    }

    [Fact]
    public void VcGenIsNotYetATacticOfATheoremScript()
    {
        var result = Extract("""
            public static class C
            {
                [Verified] public static int Id(int x) => x;
                [Theorem] static Proof T(int x) => Prove.That(Id(x) == x).By(Tactic.VcGen());
            }
            """);

        Assert.Equal("WRT0004 | unsupported script argument", Only(result, "M:C.T(System.Int32)"));
    }

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
