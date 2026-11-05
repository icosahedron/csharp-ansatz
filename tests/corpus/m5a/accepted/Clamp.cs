// An upper bound through literals: the omega-prep set's literal lemmas turn 100 and -100 into integers for omega.
using Warrant;

namespace Corpus;

public static class Clamps
{
    [Verified]
    public static int Clamp(int x) => x > 100 ? 100 : x < -100 ? -100 : x;

    [Theorem]
    static Proof AtMostOneHundred(int x) =>
        Prove.That(Clamp(x) <= 100)
             .By(Tactic.Unfold(nameof(Clamp)), Tactic.Omega());
}
