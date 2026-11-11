// M6 U14's refuted contracts without dependencies (KTD12, KTD16, KTD25, #98): a precondition that leaves an exception
// possible, a division by -1, a caller that breaks its callee's precondition, a false Spec.Ensures with and without a
// [ProofFor] script, a failing Spec.Assert, a contradictory Spec.Requires, and an overflowing Spec.Ensures (#183).
using Warrant;

namespace Corpus.M6.Refuted;

public static class Contracts
{
    // b != 0 rules out a zero divisor but not int.MinValue / -1.
    [Verified]
    public static int Ratio(int a, int b)
    {
        Spec.Requires(b != 0);
        return a / b;
    }

    // x / -1 is x negated, which overflows for int.MinValue even in unchecked code.
    [Verified]
    public static int Neg(int x) { return x / -1; }

    [Verified]
    public static int Share(int x)
    {
        Spec.Requires(x != 0);
        return 100 / x;
    }

    [Verified]
    public static int ShareOfNothing() => Share(0);

    [Verified]
    public static int Twice(int x)
    {
        Spec.Requires(x > -1000 && x < 1000);
        Spec.Ensures<int>(r => r == x + x + 1);
        return x + x;
    }

    [Verified]
    public static int Kept(int x)
    {
        Spec.Requires(x < 1000);
        Spec.Ensures<int>(r => r == x + 1);
        return x;
    }

    [ProofFor(nameof(Kept))]
    static Proof KeptProof() => Prove.Contract().By(Tactic.VcGen(), Tactic.Omega());

    [Verified]
    public static int Asserted(int a, int b)
    {
        Spec.Assert(b != 0);
        return a / b;
    }

    [Verified]
    public static int Impossible(int x)
    {
        Spec.Requires(x > 0);
        Spec.Requires(x < 0);
        return x;
    }

    // Spec.NoThrow (#182) without b != 0 in the Requires: the throw is reachable, so the build fails at it.
    [Verified]
    public static int QuotientOfAny(int a, int b)
    {
        Spec.Requires(b != -1);
        Spec.NoThrow();
        if (b == 0)
        {
            throw new System.ArgumentException("b");
        }
        return a / b;
    }

    // Arithmetic in a Spec expression must not overflow (#183): nothing bounds a + b, though the code's own + wraps.
    [Verified]
    public static int SumUnbounded(int a, int b)
    {
        Spec.Ensures<int>(r => r == a + b);
        return a + b;
    }
}
