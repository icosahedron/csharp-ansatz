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

// #218: records with nullable fields (int?, decimal? and a nullable record), compared as the CLR's generated Equals
// compares them, read after a null test in a body and in a Spec expression, and updated with `with`.
public sealed record Fee(int? Days, decimal? Amount);

public sealed record Refund(Payment? Original);

public static class Refunds
{
    [Verified]
    public static bool SameFee(Fee a, Fee b) => a == b;

    [Verified]
    public static bool SameRefund(Refund a, Refund b) => a == b;

    [Verified]
    public static int DaysOrZero(Fee fee) => fee.Days ?? 0;

    [Verified]
    public static Fee Waived(Fee fee)
    {
        Spec.Ensures<Fee>(r => r.Amount is null);
        return fee with { Amount = null };
    }

    [Verified]
    public static int OriginalIdOrZero(Refund refund)
    {
        Spec.Requires(refund.Original is null || refund.Original.Id > 0);
        Spec.Ensures<int>(r => r >= 0);
        if (refund.Original is null) return 0;
        return refund.Original.Id;
    }
}
