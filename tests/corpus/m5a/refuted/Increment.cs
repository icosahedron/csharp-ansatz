// The M5a exit criterion's false claim (design §11): Increment wraps at int.MaxValue, so Increment(x) > x fails there; it wraps on purpose, unchecked (#244).
using Warrant;

namespace Corpus.Refuted;

public static class Increments
{
    [Verified]
    public static int Increment(int x) => unchecked(x + 1);

    [Theorem]
    static Proof AlwaysLarger(int x) =>
        Prove.That(Increment(x) > x)
             .By(Tactic.Unfold(nameof(Increment)), Tactic.Omega());
}
