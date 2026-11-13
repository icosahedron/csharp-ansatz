// The tutorial's running example (docs/proving/tutorial.md, docs/m4/README.md).
using Warrant;

namespace Payouts;

public static class PayoutRules
{
    [Verified]
    public static int Payout(int loss, int deductible, int limit)
    {
        // A deductible is never negative, so loss - deductible cannot overflow (#244).
        Spec.Requires(deductible >= 0);
        if (loss <= deductible) return 0;
        var covered = loss - deductible;
        return covered > limit ? limit : covered;
    }
}

static class PayoutTheorems
{
    [Theorem]
    static Proof CappedAtTheLimit() =>
        Prove.That(PayoutRules.Payout(loss: 1000, deductible: 250, limit: 500) == 500);

    [Theorem]
    static Proof NothingBelowTheDeductible() =>
        Prove.That(PayoutRules.Payout(loss: 100, deductible: 250, limit: 500) == 0);
}
