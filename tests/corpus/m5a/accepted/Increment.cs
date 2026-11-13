// The true variant of the exit criterion's false claim (../refuted/Increment.cs): below int.MaxValue, Increment(x) > x.
using Warrant;

namespace Corpus;

public static class Increments
{
    [Verified]
    public static int Increment(int x)
    {
        // x + 1 must not overflow (#244); the theorem's premise is this precondition.
        Spec.Requires(x < int.MaxValue);
        return x + 1;
    }

    [Theorem]
    static Proof LargerBelowMax(int x) =>
        Prove.That(Spec.Implies(x < int.MaxValue, Increment(x) > x))
             .By(Tactic.Unfold(nameof(Increment)), Tactic.Simp(), Tactic.Omega());
}
