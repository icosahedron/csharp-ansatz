// Wrap-around at the boundaries (design §2, D7). The false theorem about it is in ../refuted. The wrap is on purpose, so the arithmetic is unchecked (#244).
using Warrant;

namespace Corpus;

public static class Increments
{
    [Verified]
    public static int Increment(int x) => unchecked(x + 1);

    [Verified]
    public static long IncrementLong(long x) => unchecked(x + 1);

    [Theorem]
    static Proof WrapsAtMax() => Prove.That(Increment(int.MaxValue) == int.MinValue);

    [Theorem]
    static Proof LongWrapsAtMax() => Prove.That(IncrementLong(long.MaxValue) == long.MinValue);

    [Theorem]
    static Proof IncrementIsLarger() => Prove.That(Increment(41) > 41);
}
