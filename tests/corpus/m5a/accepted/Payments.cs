// Design §5.1's ValidImpliesPositive with int amounts (plan Success Criteria), proved by unfolding Validate and simp.
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
    static Proof ValidImpliesPositive(Payment p) =>
        Prove.That(Spec.Implies(Validate(p) == PaymentResult.Valid, p.Amount > 0))
             .By(Tactic.Unfold(nameof(Validate)), Tactic.Simp());
}
