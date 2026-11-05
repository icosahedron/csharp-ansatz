// Recursion M5a rejects (plan R7, KTD14, KTD15).
using Warrant;

namespace Corpus.Rejected;

public static class Recursion
{
    // Mutual recursion, even with a measure on both.
    [Verified]
    public static bool IsEven(int n)
    {
        Spec.Decreases(n);
        if (n <= 0) return true;
        return IsOdd(n - 1);
    }

    [Verified]
    public static bool IsOdd(int n)
    {
        Spec.Decreases(n);
        if (n <= 0) return false;
        return IsEven(n - 1);
    }

    // No measure: an expression body has no statement to hold one.
    [Verified]
    public static int Factorial(int n) => n <= 1 ? 1 : n * Factorial(n - 1);

    // The measure is read at entry, so it must come first.
    [Verified]
    public static int Countdown(int n)
    {
        if (n <= 0) return 0;
        Spec.Decreases(n);
        return Countdown(n - 1);
    }

    // A decrease obligation cannot name the inner call's result.
    [Verified]
    public static int Nested(int n)
    {
        Spec.Decreases(n);
        if (n <= 0) return 0;
        return Nested(Nested(n - 1));
    }
}
