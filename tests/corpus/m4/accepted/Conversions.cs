// int to long and back, and casts between open enums and integers.
using Warrant;

namespace Claims;

public static class Conversions
{
    [Verified]
    public static long Widen(int x) => x;

    [Verified]
    public static int Narrow(long x) => (int)x;

    [Verified]
    public static int StatusCode(PaymentStatus s) => (int)s;

    [Verified]
    public static PaymentStatus FromCode(int code) => (PaymentStatus)code;

    [Verified]
    public static bool IsUnnamed(PaymentStatus s) =>
        s != PaymentStatus.Pending && s != PaymentStatus.Processed && s != PaymentStatus.Failed;

    [Theorem]
    static Proof NarrowingKeepsLowBits() => Prove.That(Narrow(3000000000L) == -1294967296);

    [Theorem]
    static Proof SevenIsUnnamed() => Prove.That(IsUnnamed(FromCode(7)));

    [Theorem]
    static Proof WideningKeepsSign() => Prove.That(Widen(-5) == -5L);

    [Theorem]
    static Proof ProcessedIsOne() => Prove.That(StatusCode(PaymentStatus.Processed) == 1);
}
