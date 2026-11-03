// A [Closed] enum and a switch expression over it (design D12, docs/m4/05).
using Warrant;

namespace Claims;

[Closed]
public enum ClaimStatus { Open, Paid, Denied, Withdrawn }

public static class ClaimStatuses
{
    [Verified]
    public static int Priority(ClaimStatus s) => s switch
    {
        ClaimStatus.Open => 2,
        ClaimStatus.Paid or ClaimStatus.Withdrawn => 0,
        _ => 1,
    };

    [Verified]
    public static bool IsFinal(ClaimStatus s) => s != ClaimStatus.Open;

    [Theorem]
    static Proof OpenIsUrgent() => Prove.That(Priority(ClaimStatus.Open) == 2);

    [Theorem]
    static Proof DeniedTakesTheDefault() => Prove.That(Priority(ClaimStatus.Denied) == 1);

    [Theorem]
    static Proof DeniedIsFinal() => Prove.That(IsFinal(ClaimStatus.Denied));

    [Theorem]
    static Proof OpenIsNotFinal() => Prove.That(!IsFinal(ClaimStatus.Open));
}
