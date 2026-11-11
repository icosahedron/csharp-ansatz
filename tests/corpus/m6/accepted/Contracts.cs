// Contracts without dependencies (plan M6 U8, KTD8, KTD16): the leading Spec.Requires and Spec.Ensures of a block body,
// Spec.Assert where a statement stands, and a [ProofFor] method's script for a method's contract obligation.
using Warrant;

namespace Corpus.M6;

public static class Contracts
{
    [Verified]
    public static int NonNegative(int x)
    {
        Spec.Ensures<int>(r => r >= 0);
        return x < 0 ? 0 : x;
    }

    [Verified]
    public static int AtMost(int x, int limit)
    {
        Spec.Requires(x >= 0);
        Spec.Requires(limit >= 0);
        Spec.Ensures<int>(r => r >= 0 && r <= limit);
        return x > limit ? limit : x;
    }

    // A call to a method with Spec.Requires makes the caller prove the precondition (KTD11), so it can raise.
    [Verified]
    public static int Capped(int x)
    {
        Spec.Requires(x >= 0);
        Spec.Ensures<int>(r => r <= 100);
        return AtMost(x, 100);
    }

    [Verified]
    public static int Average(int a, int b)
    {
        Spec.Requires(a >= 0 && a <= 1000 && b >= 0 && b <= 1000);
        Spec.Assert(a + b >= 0, Tactic.Omega());
        return (a + b) / 2;
    }

    [Verified]
    public static int Same(int x)
    {
        Spec.Ensures<int>(r => r == x);
        return x;
    }

    [ProofFor(nameof(Same))]
    static Proof SameProof() => Prove.Contract().By(Tactic.VcGen(), Tactic.Omega());
}
