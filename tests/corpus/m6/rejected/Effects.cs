// What M6 U7 still rejects, one construct per member: an exception whose construction could throw something else,
// try, a BCL member that is not modelled, and a raising operation in a theorem statement (KTD11).
using System;
using Warrant;

namespace Corpus.M6.Rejected;

public sealed class Odd : Exception
{
    public Odd(int x) : base("odd") { Code = 100 / x; }

    public int Code { get; }
}

public static class Effects
{
    [Verified]
    public static int ThrowsOdd(int x) => x != 0 ? x : throw new Odd(x);

    [Verified]
    public static int TryFinally(int n)
    {
        try
        {
            return n;
        }
        finally
        {
        }
    }

    [Verified]
    public static int Sign(int n) => Math.Sign(n);

    [Theorem]
    static Proof RatioAtMost(int x, int y) => Prove.That(x / y <= x);

    [Theorem]
    static Proof AbsoluteIsNonNegative(int x) => Prove.That(Math.Abs(x) >= 0);

    [Verified]
    public static int TryCatch(int a, int b)
    {
        try
        {
            return a / b;
        }
        catch (DivideByZeroException)
        {
            return 0;
        }
    }

    // % by a variable can raise, so the recursion is recursion with effects (KTD11).
    [Verified]
    public static int Gcd(int a, int b)
    {
        Spec.Decreases(b);
        return b == 0 ? a : Gcd(b, a % b);
    }
}
