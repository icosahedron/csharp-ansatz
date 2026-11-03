// Arithmetic M4 rejects: division and remainder need exceptions (M6), checked arithmetic needs
// OverflowException (M6), and integer bitwise operators and shifts wait for a milestone that
// needs them (plan KTD15). Each member uses one rejected construct and nothing else unsupported.
using Warrant;

namespace Corpus.Rejected;

public static class Arithmetic
{
    [Verified]
    public static int Halve(int x) => x / 2;

    [Verified]
    public static int Remainder(int x) => x % 3;

    [Verified]
    public static int CheckedAdd(int a, int b) => checked(a + b);

    [Verified]
    public static int And(int a, int b) => a & b;

    [Verified]
    public static int Or(int a, int b) => a | b;

    [Verified]
    public static int Xor(int a, int b) => a ^ b;

    [Verified]
    public static int Complement(int a) => ~a;

    [Verified]
    public static int ShiftLeft(int a) => a << 1;

    [Verified]
    public static int ShiftRight(int a) => a >> 1;

    [Verified]
    public static int UnsignedShiftRight(int a) => a >>> 1;

    // A constant expression is folded by the compiler, so it is accepted (plan KTD13).
    [Verified]
    public static int FoldedDivision() => 10 / 2;
}
