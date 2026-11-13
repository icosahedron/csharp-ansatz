// Reassignment, if without else, join points, a nested return and a switch statement (docs/m4/05).
using Warrant;

namespace Corpus;

public static class Locals
{
    // One local changes and neither branch returns: a let of an ite.
    [Verified]
    public static int Fee(int price, bool rush)
    {
        // price + fee must not overflow (#244).
        Spec.Requires(price <= 1000000);
        var fee = 10;
        if (rush) fee = fee * 2;
        return price + fee;
    }

    // Two locals change: a join point.
    [Verified]
    public static int Shipping(int weight, bool express, bool member)
    {
        // weight * 2 + 15 must not overflow (#244).
        Spec.Requires(weight >= 0 && weight <= 1000000);
        var cost = weight * 2;
        var bonus = 0;
        if (express)
        {
            cost = cost + 15;
            bonus = 1;
        }
        // cost and bonus are known on each path into the join point (#255), so these are bounded too.
        if (member) return cost - 5;
        return cost + bonus;
    }

    // Both branches can fall through and neither changes a local the rest reads, but the
    // then-branch can return: dropping the if would lose `return 1` (plan KTD7).
    [Verified]
    public static int NestedReturn(bool c, bool d)
    {
        var other = 0;
        if (c)
        {
            if (d) return 1;
        }
        else
        {
            other = other + 1;
        }
        return 2;
    }

    [Verified]
    public static int Steps(int x)
    {
        // Wraps on purpose (StepsAddThree), so the block is unchecked (#244).
        var n = x;
        unchecked
        {
            n += 3;
            n++;
            n -= 1;
        }
        return n;
    }

    // A switch statement without default falls through to the next statement.
    [Verified]
    public static int Bucket(int code)
    {
        var result = 0;
        switch (code)
        {
            case 1:
                result = 10;
                break;
            case >= 5 and < 9:
                return 20;
        }
        // result is 0 or 10 here, which the join point knows (#255).
        return result + 1;
    }

    [Theorem]
    static Proof RushDoublesTheFee() => Prove.That(Fee(100, true) == 120);

    [Theorem]
    static Proof ExpressMember() => Prove.That(Shipping(10, true, true) == 30);

    [Theorem]
    static Proof NestedReturnTaken() => Prove.That(NestedReturn(true, true) == 1);

    [Theorem]
    static Proof NestedReturnNotTaken() => Prove.That(NestedReturn(true, false) == 2);

    [Theorem]
    static Proof StepsAddThree() => Prove.That(Steps(int.MaxValue) == int.MinValue + 2);

    [Theorem]
    static Proof BucketFallsThrough() => Prove.That(Bucket(3) == 1);

    [Theorem]
    static Proof BucketBreaks() => Prove.That(Bucket(1) == 11);

    [Theorem]
    static Proof BucketReturns() => Prove.That(Bucket(6) == 20);
}
