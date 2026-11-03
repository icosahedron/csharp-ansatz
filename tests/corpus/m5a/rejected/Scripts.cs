// Malformed proof scripts and specs (WRT0004; plan KTD18).
using Warrant;

namespace Corpus.Rejected;

public static class Scripts
{
    [Verified]
    public static int Scale(int x) => x + x;

    [Verified]
    public static long Scale(long x) => x + x;

    // nameof of an overloaded method names no single member.
    [Theorem]
    static Proof UnfoldsAnOverload(int x) =>
        Prove.That(Scale(x) == x + x)
             .By(Tactic.Unfold(nameof(Scale)), Tactic.Omega());

    // A string literal names a hypothesis, not a lemma.
    [Theorem]
    static Proof SimpWithAString(int x) =>
        Prove.That(Scale(x) == x + x)
             .By(Tactic.Simp("Scale"));

    // Spec.ForAll is valid only in a theorem statement.
    [Verified]
    public static bool ForAllInCode() => Spec.ForAll<int>(y => y + 0 == y);
}
