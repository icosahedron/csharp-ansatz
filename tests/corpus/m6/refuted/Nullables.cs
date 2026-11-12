// M6 U17's nullable reads, unwraps and decimal arithmetic whose exceptions nothing rules out without a Spec.Requires
// (KTD5, KTD7, KTD12). Roslyn warns about the two dereferences; the model checks them whatever it says (#163).
using Warrant;

namespace Corpus.M6.Refuted;

public sealed record Payment(int Id);

public static class Nullables
{
    [Verified]
    public static int Read(int? x) => x.Value;

    [Verified]
    public static long Cast(long? x) => (long)x;

    [Verified]
    public static int Use(Payment payment) => payment.Id;

#pragma warning disable CS8602, CS8604
    [Verified]
    public static int IdOf(Payment? payment) => payment.Id;

    [Verified]
    public static int Unchecked(Payment? payment) => Use(payment);
#pragma warning restore CS8602, CS8604
}

public static class Decimals
{
    [Verified]
    public static decimal AddFee(decimal amount) => amount + 1.25m;

    [Verified]
    public static decimal Difference(decimal a, decimal b) => a - b;
}
