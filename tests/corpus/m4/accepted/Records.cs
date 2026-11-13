// Records: construction, property reads, with, equality, and a verified instance property.
using Warrant;

namespace Claims;

public sealed record Point(int X, int Y);

public sealed record Assignment(int AdjusterId, bool Escalated, ClaimStatus Status)
{
    [Verified]
    public bool NeedsAlert => Escalated && AdjusterId == 0 && Status == ClaimStatus.Open;
}

public sealed record Claim(int Number, Payment Payment, Outcome Outcome);

public static class Records
{
    [Verified]
    public static Point Move(Point p, int dx)
    {
        // p.X + dx must not overflow (#244).
        Spec.Requires(p.X > -1000000 && p.X < 1000000 && dx > -1000000 && dx < 1000000);
        return p with { X = p.X + dx };
    }

    [Verified]
    public static bool SamePlace(Point a, Point b) => a == b;

    [Verified]
    public static int Distance(Point p)
    {
        // Neither -p.X nor the sum may overflow (#244).
        Spec.Requires(p.X > -1000000 && p.X < 1000000 && p.Y > -1000000 && p.Y < 1000000);
        return (p.X < 0 ? -p.X : p.X) + (p.Y < 0 ? -p.Y : p.Y);
    }

    // A record field of record type and one of closed-class type: both are assumed non-null.
    [Verified]
    public static int Amount(Claim c) => c.Outcome == Outcome.Matched ? c.Payment.Amount : 0;

    [Theorem]
    static Proof MoveChangesX() => Prove.That(Move(new Point(1, 2), 3) == new Point(4, 2));

    [Theorem]
    static Proof MoveKeepsY() => Prove.That(Move(new Point(1, 2), 3).Y == 2);

    [Theorem]
    static Proof DifferentPoints() => Prove.That(!SamePlace(new Point(1, 2), new Point(2, 1)));

    [Theorem]
    static Proof UnassignedEscalationAlerts() =>
        Prove.That(new Assignment(0, true, ClaimStatus.Open).NeedsAlert);
}
