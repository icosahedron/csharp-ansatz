// Spec.ForAll with Intro, Cases over bool and a [Closed] enum, and Induction (plan R1, R8).
using Warrant;

namespace Corpus;

[Closed]
public enum Light { Red, Amber, Green }

public static class Quantifiers
{
    [Theorem]
    static Proof ZeroIsNeutral() =>
        Prove.That(Spec.ForAll<int>(y => y + 0 == y))
             .By(Tactic.Intro("y"), Tactic.Omega());

    [Verified]
    public static bool Flip(bool b) => !b;

    [Theorem]
    static Proof FlipTwice(bool b) =>
        Prove.That(Flip(Flip(b)) == b)
             .By(Tactic.Unfold(nameof(Flip)), Tactic.Cases("b"), Tactic.AllGoals(Tactic.Simp()));

    [Verified]
    public static int Rank(Light l) => l switch
    {
        Light.Red => 0,
        Light.Amber => 1,
        _ => 2,
    };

    [Theorem]
    static Proof RankIsSmall(Light l) =>
        Prove.That(Rank(l) <= 2)
             .By(Tactic.Unfold(nameof(Rank)), Tactic.Cases("l"), Tactic.AllGoals(Tactic.Simp().With(decide: true)));

    [Verified]
    public static bool AndTrue(bool b) => b && true;

    [Theorem]
    static Proof AndTrueIsIdentity(bool b) =>
        Prove.That(AndTrue(b) == b)
             .By(Tactic.Unfold(nameof(AndTrue)), Tactic.Induction("b"), Tactic.AllGoals(Tactic.Try(Tactic.Simp())));
}
