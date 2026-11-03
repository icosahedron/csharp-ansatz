// A recursion without a guard: its decrease obligation fails at n <= 0 (plan KTD14, KTD15).
using Warrant;

namespace Corpus.Refuted;

public static class Recursion
{
    [Verified]
    public static int Bad(int n)
    {
        Spec.Decreases(n);
        return Bad(n - 1);
    }
}
