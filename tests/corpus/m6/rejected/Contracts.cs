// What M6 U8 rejects in contracts, one construct per member: the order and place of the leading Spec statements and the
// type Spec.Ensures binds (KTD8), KTD11's rejections, and [ProofFor] methods that supply no script (KTD16).
using System;
using Warrant;

namespace Corpus.M6.Rejected;

public static class Contracts
{
    [Verified]
    public static int EnsuresLate(int x)
    {
        var y = x;
        Spec.Ensures<int>(r => r == x);
        return y;
    }

    [Verified]
    public static int RequiresAfterEnsures(int x)
    {
        Spec.Ensures<int>(r => r == x);
        Spec.Requires(x > 0);
        return x;
    }

    [Verified]
    public static int DecreasesAfterRequires(int n)
    {
        Spec.Requires(n >= 0);
        Spec.Decreases(n);
        return n <= 0 ? 0 : DecreasesAfterRequires(n - 1);
    }

    [Verified]
    public static int Countdown(int n)
    {
        Spec.Decreases(n);
        Spec.Ensures<int>(r => r >= 0);
        return n <= 0 ? 0 : Countdown(n - 1);
    }

    [Verified]
    public static int Descend(int n)
    {
        Spec.Decreases(n);
        if (n < 0)
        {
            throw new ArgumentOutOfRangeException(nameof(n));
        }
        return n == 0 ? 0 : Descend(n - 1);
    }

    [Verified]
    public static int Widened(int x)
    {
        Spec.Ensures<long>(r => r >= 0);
        return x;
    }

    [Verified]
    public static int NoResult(int x)
    {
        Spec.Ensures(() => x >= 0);
        return x;
    }

    static bool Positive(int r) => r > 0;

    [Verified]
    public static int NotALambda(int x)
    {
        Spec.Ensures<int>(Positive);
        return x;
    }

    [Verified]
    public static int Scale(int x, int d) => x / d;

    [Verified]
    public static int Scaled(int x, int d)
    {
        Spec.Ensures<int>(r => r == Scale(x, d));
        return x / d;
    }

    [Verified]
    public static int Checked(int x) => x >= 0 ? x : throw new ArgumentException("negative");

    [Verified]
    public static int Next(int x) => unchecked(Checked(x) + 1);

    [Theorem]
    static Proof NextIsPositive(int x) => Prove.That(Next(x) > 0);

    [ProofFor("Missing")]
    static Proof MissingProof() => Prove.Contract().By(Tactic.Omega());

    [Verified]
    public static int Kept(int x)
    {
        Spec.Ensures<int>(r => r == x);
        return x;
    }

    [ProofFor(nameof(Kept))]
    static Proof KeptProof() => Prove.Contract().By(Tactic.Omega());

    [ProofFor(nameof(Kept))]
    static Proof KeptAgain() => Prove.Contract().By(Tactic.Simp());

    [Verified]
    public static int Bare(int x)
    {
        Spec.Ensures<int>(r => r == x);
        return x;
    }

    [ProofFor(nameof(Bare))]
    static Proof BareProof() => Prove.Contract();

    [Verified]
    public static int Given(int x)
    {
        Spec.Ensures<int>(r => r == x);
        return x;
    }

    [ProofFor(nameof(Given))]
    static Proof GivenProof(int x) => Prove.Contract().By(Tactic.Omega());

    [Verified]
    public static int Twin(int x) => x;

    [Verified]
    public static long Twin(long x) => x;

    [ProofFor(nameof(Twin))]
    static Proof TwinProof() => Prove.Contract().By(Tactic.Omega());

    public static int Plain(int x) => x;

    [ProofFor(nameof(Plain))]
    static Proof PlainProof() => Prove.Contract().By(Tactic.Omega());

    [Verified]
    public static int NoThrowAfterEnsures(int x)
    {
        Spec.Ensures<int>(r => r == x);
        Spec.NoThrow();
        return x;
    }
}
