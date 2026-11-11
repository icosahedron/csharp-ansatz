// Control flow and types M4 rejects (plan KTD15).
using System;
using Warrant;

namespace Corpus.Rejected;

public static class Statements
{
    [Verified]
    public static int Factorial(int n) => n <= 1 ? 1 : n * Factorial(n - 1);

    [Verified]
    public static bool IsEven(int n) => n == 0 || IsOdd(n - 1);

    [Verified]
    public static bool IsOdd(int n) => n != 0 && IsEven(n - 1);

    [Verified]
    public static int ForLoop(int n)
    {
        var total = 0;
        for (var i = 0; i < n; i++) total += i;
        return total;
    }

    [Verified]
    public static int WhileLoop(int n)
    {
        while (n > 10) n -= 10;
        return n;
    }

    [Verified]
    public static int DoLoop(int n)
    {
        do n -= 1; while (n > 0);
        return n;
    }

    [Verified]
    public static int TryCatch(int n)
    {
        try
        {
            return n;
        }
        catch (InvalidOperationException)
        {
            return 0;
        }
    }

    [Verified]
    public static int LocalFunction(int n)
    {
        return Twice(n);

        static int Twice(int x) => x + x;
    }

    [Verified]
    public static int Unreachable(bool c)
    {
        if (c) return 1;
        else return 2;
#pragma warning disable CS0162
        return 3;
#pragma warning restore CS0162
    }

    // Translation places default last, which a section shared with case labels cannot express.
    [Verified]
    public static int MixedDefault(int n)
    {
        switch (n)
        {
            case 1:
            default:
                return 0;
            case 2:
                return 5;
        }
    }

    [Verified]
    public static int Strings(string s) => s.Length;

    // #133: a ref local is another name for p, so the write through it changes what p reads.
    [Verified]
    public static int RefLocal(int p)
    {
        ref int alias = ref p;
        alias = 5;
        return p;
    }

    [Verified]
    public static int RefReadonlyLocal(int p)
    {
        int a = p;
        ref readonly int alias = ref a;
        a = 9;
        return alias;
    }

    // Decimals, which M6 supports, moved to tests/corpus/m6 (README).
    [Verified]
    public static double Doubles(double d) => d;

    // Replaces CallsUnverified (Math.Abs), which M6 models and which moved to tests/corpus/m6 (README).
    [Verified]
    public static int CallsUnmodelled(int n) => Math.Sign(n);
}
