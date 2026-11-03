// Well-founded recursion with Spec.Decreases (plan KTD14, KTD15): each decrease obligation is proved by omega.
using Warrant;

namespace Corpus;

public static class Recursion
{
    [Verified]
    public static int Sum(int n)
    {
        Spec.Decreases(n);
        if (n <= 0) return 0;
        return n + Sum(n - 1);
    }

    // Two parameters; the measure is the second.
    [Verified]
    public static int Add(int a, int b)
    {
        Spec.Decreases(b);
        if (b <= 0) return a;
        return Add(a + 1, b - 1);
    }

    // A long measure.
    [Verified]
    public static long SumLong(long n)
    {
        Spec.Decreases(n);
        if (n <= 0) return 0;
        return n + SumLong(n - 1);
    }
}
