// M6 U17's nullable values and decimals that cannot raise, or whose raise the path rules out (KTD5, KTD7): null tests,
// ??, GetValueOrDefault, a nullable reference used only after it is tested, decimal comparisons, negation and Math.
using System;
using Warrant;

namespace Corpus.M6;

public sealed record Payment(int Id, decimal Amount);

public static class Nullables
{
    [Verified]
    public static bool IsMissing(Payment? payment) => payment is null;

    [Verified]
    public static int OrZero(int? x) => x ?? 0;

    [Verified]
    public static long OrDefault(long? x) => x.GetValueOrDefault();

    [Verified]
    public static int? Wrap(int a) => a;

    [Verified]
    public static int ValueWhenKnown(int? x) => x.HasValue ? x.Value : 0;

    [Verified]
    public static int Use(Payment payment) => payment.Id;

    // #163: the argument is an unwrap the path condition proves non-null.
    [Verified]
    public static int Guarded(Payment? payment)
    {
        if (payment is null)
        {
            return 0;
        }
        return Use(payment);
    }

    [Verified]
    public static int IdOrZero(Payment? payment) => payment != null ? payment.Id : 0;
}

public static class Decimals
{
    [Verified]
    public static bool AtLeastOne(decimal amount) => amount >= 1.0m;

    [Verified]
    public static bool SameAmount(Payment a, Payment b) => a.Amount == b.Amount;

    [Verified]
    public static bool SamePayment(Payment a, Payment b) => a == b;

    [Verified]
    public static decimal Negate(decimal amount) => -amount;

    [Verified]
    public static decimal Largest(decimal a, decimal b) => Math.Max(a, b);

    [Verified]
    public static decimal Smallest(decimal a, decimal b) => Math.Min(a, b);

    [Verified]
    public static decimal Size(decimal amount) => Math.Abs(amount);
}
