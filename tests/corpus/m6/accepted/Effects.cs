// M6 U7's new constructs that need no contract: the modelled Math members that cannot throw, and a throw statement of
// a user exception type that only chains to a System exception.
using System;
using Warrant;

namespace Corpus.M6;

public sealed class RejectedPayment : Exception
{
    public RejectedPayment(string message) : base(message) { }
}

public static class Effects
{
    [Verified]
    public static int Biggest(int a, int b) => Math.Max(a, b);

    [Verified]
    public static long Smallest(long a, long b) => Math.Min(a, b);

    [Verified]
    public static int Guard(int amount)
    {
        if (amount < 0)
        {
            throw new RejectedPayment("negative");
        }
        return amount;
    }
}
