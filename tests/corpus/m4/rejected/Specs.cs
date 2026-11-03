// Theorem and spec forms M4 rejects (plan KTD15, KTD18, KTD20).
using Warrant;

namespace Corpus.Rejected;

public static class Specs
{
    [Verified]
    public static int Id(int x) => x;

    // Quantified theorems need tactics (M5a).
    [Theorem]
    static Proof WithParameters(int x) => Prove.That(Id(x) == x);

    // Spec.Implies is valid only inside a theorem statement (WRT0004).
    [Verified]
    public static bool ImpliesInCode(bool a, bool b) => Spec.Implies(a, b);

    // A verified member may not call a [Theorem] (WRT0003).
    [Verified]
    public static int CallsATheorem()
    {
        Valid();
        return 0;
    }

    [Theorem]
    static Proof Valid() => Prove.That(Id(1) == 1);
}
