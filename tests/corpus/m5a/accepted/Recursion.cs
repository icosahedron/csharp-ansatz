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
        // Nothing is known of a recursive call's result where the sum's obligation is stated: a recursive method may
        // bound n with Spec.Requires (#256) but cannot yet state a Spec.Ensures bounding the sum, so it wraps (#244).
        return unchecked(n + Sum(n - 1));
    }

    // Two parameters; the measure is the second.
    [Verified]
    public static int Add(int a, int b)
    {
        Spec.Decreases(b);
        // a + 1 stays in range: the body assumes this, and the recursive call must satisfy it again (#256).
        Spec.Requires(b >= 0 && a <= int.MaxValue - b);
        if (b <= 0) return a;
        return Add(a + 1, b - 1);
    }

    // A long measure.
    [Verified]
    public static long SumLong(long n)
    {
        Spec.Decreases(n);
        if (n <= 0) return 0;
        // As Sum: no Spec.Ensures bounds the recursive result yet.
        return unchecked(n + SumLong(n - 1));
    }
}
