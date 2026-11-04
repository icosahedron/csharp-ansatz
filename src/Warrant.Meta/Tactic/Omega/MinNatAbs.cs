using System.Numerics;

namespace Warrant.Meta.Omega;

/// <summary>
/// <c>List.minNatAbs</c> and <c>List.maxNatAbs</c> (Lean/Elab/Tactic/Omega/MinNatAbs.lean 95-100), which choose the
/// equality <c>omega</c> eliminates next.
/// </summary>
internal static class MinNatAbs
{
    /// <summary><c>minNatAbs</c>: the least non-zero absolute value of an entry, or 0 if every entry is 0.</summary>
    public static BigInteger Min(Coeffs xs)
    {
        BigInteger? min = null;
        foreach (var x in xs.Values)
        {
            var a = BigInteger.Abs(x);
            if (!a.IsZero && (min is null || a < min))
            {
                min = a;
            }
        }
        return min ?? BigInteger.Zero;
    }

    /// <summary><c>maxNatAbs</c>: the greatest absolute value of an entry, or 0 for the empty list.</summary>
    public static BigInteger Max(Coeffs xs)
    {
        var max = BigInteger.Zero;
        foreach (var x in xs.Values)
        {
            max = BigInteger.Max(max, BigInteger.Abs(x));
        }
        return max;
    }
}
