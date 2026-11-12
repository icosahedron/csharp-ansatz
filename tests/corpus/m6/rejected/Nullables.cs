// What M6 U17 still rejects, one construct per member: the null-forgiving operator, lifted comparisons and arithmetic
// on nullable values (#76), decimal multiplication, and a nullable read or decimal arithmetic in a theorem statement (KTD11).
using Warrant;

namespace Corpus.M6.Rejected;

public sealed record Payment(int Id);

public static class Nullables
{
    [Verified]
    public static int Use(Payment payment) => payment.Id;

    [Verified]
    public static int Forgiven(Payment? payment) => Use(payment!);

    [Verified]
    public static bool LiftedLess(int? x) => x > 0;

    [Verified]
    public static bool LiftedEquals(int? x) => x == 5;

    [Verified]
    public static int? LiftedAdd(int? a, int? b) => a + b;

    [Theorem]
    static Proof ReadIsPositive(int? x) => Prove.That(x.Value > 0);
}

public static class Decimals
{
    [Verified]
    public static decimal Product(decimal a, decimal b) => a * b;

    [Theorem]
    static Proof AddingOneIsLarger(decimal d) => Prove.That(d + 1m > d);
}
