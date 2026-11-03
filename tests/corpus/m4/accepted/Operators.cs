// Operators and patterns no other corpus member uses, so the differential tests check their wiring against the CLR.
using Warrant;

namespace Corpus;

public enum Magnitude : long { Small = 1, Huge = 5000000000 }

public static class Operators
{
    [Verified]
    public static bool Or(bool a, bool b) => a || b;

    [Verified]
    public static bool EagerOr(bool a, bool b) => a | b;

    [Verified]
    public static bool EagerAnd(bool a, bool b) => a & b;

    [Verified]
    public static bool Xor(bool a, bool b) => a ^ b;

    [Verified]
    public static int UnaryPlus(int x) => +x;

    [Verified]
    public static long LongSubtract(long a, long b) => a - b;

    [Verified]
    public static long LongMultiply(long a, long b) => a * b;

    [Verified]
    public static bool LongLess(long a, long b) => a < b;

    [Verified]
    public static bool LongAtMost(long a, long b) => a <= b;

    [Verified]
    public static bool LongEqual(long a, long b) => a == b;

    [Verified]
    public static int Band(int n) => n switch
    {
        < 0 => -1,
        <= 3 => 0,
        4 or 5 => 1,
        >= 100 and not 200 => 4,
        not 10 => 2,
        _ => 3,
    };

    [Verified]
    public static int Size(Magnitude m) => m switch
    {
        Magnitude.Small => 0,
        Magnitude.Huge => 1,
        _ => 2,
    };

    [Verified]
    public static long Raw(Magnitude m) => (long)m;
}
