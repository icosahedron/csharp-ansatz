// The how-to guide's example (docs/proving/how-to.md).
using Warrant;

namespace Pricing;

public static class Discounts
{
    [Verified]
    public static int Discounted(int price, int discount)
    {
        // A discount is never negative, so price - discount cannot overflow (#244).
        Spec.Requires(discount >= 0);
        return discount >= price ? 0 : price - discount;
    }

    [Theorem]
    static Proof NeverNegativeHere() => Prove.That(Discounted(100, 150) >= 0);

    [Theorem]
    static Proof TakesTheDiscount() => Prove.That(Discounted(100, 30) == 70);
}
