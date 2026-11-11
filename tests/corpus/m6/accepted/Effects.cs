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

    // % by a constant other than 0 and -1 cannot throw, so a leap-year test stays pure (KTD11).
    [Verified]
    public static bool DivisibleByFour(int year) => year % 4 == 0;

    // Throws on every path: the Spec.Ensures holds vacuously, and the report lists the throw (KTD12, KTD20).
    [Verified]
    public static int Closed(int amount)
    {
        Spec.Ensures<int>(r => r > amount);
        throw new InvalidOperationException("closed");
    }
}
