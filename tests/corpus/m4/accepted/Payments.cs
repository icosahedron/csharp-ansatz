// The design's Validate example (design §5.1), with int in place of decimal (design §11, M4 row).
using Warrant;

namespace Claims;

public enum PaymentStatus { Pending, Processed, Failed }

public sealed record Payment(int Id, int Amount, PaymentStatus Status);

public enum PaymentResult { Valid, InvalidAmount, InvalidStatus }

public static class Payments
{
    [Verified]
    public static PaymentResult Validate(Payment p)
    {
        if (p.Amount <= 0) return PaymentResult.InvalidAmount;
        if (p.Status != PaymentStatus.Pending) return PaymentResult.InvalidStatus;
        return PaymentResult.Valid;
    }

    [Theorem]
    static Proof RejectsZero() =>
        Prove.That(Validate(new Payment(1, 0, PaymentStatus.Pending)) == PaymentResult.InvalidAmount);

    [Theorem]
    static Proof AcceptsPending() =>
        Prove.That(Validate(new Payment(2, 10, PaymentStatus.Pending)) == PaymentResult.Valid);

    [Theorem]
    static Proof RejectsProcessed() =>
        Prove.That(Validate(new Payment(3, 10, PaymentStatus.Processed)) != PaymentResult.Valid);
}
