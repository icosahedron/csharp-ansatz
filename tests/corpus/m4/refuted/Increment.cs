// Theorems that translate but are false: `warrant translate` reports WRT0001 and exits 1.
using Warrant;

namespace Corpus.Refuted;

public static class Increments
{
    [Verified]
    public static int Increment(int x) => x + 1;

    [Theorem]
    static Proof NeverWraps() => Prove.That(Increment(int.MaxValue) > int.MaxValue);

    [Theorem]
    static Proof WrongSum() => Prove.That(Increment(2) == 4);
}
