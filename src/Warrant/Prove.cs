using System;

namespace Warrant;

/// <summary>
/// States the claim of a <see cref="TheoremAttribute"/> method.
/// </summary>
public static class Prove
{
    /// <summary>
    /// States that <paramref name="claim"/> holds for every value of the theorem's parameters.
    /// Warrant reads the claim from source; the call is never meant to run.
    /// </summary>
    /// <param name="claim">The proposition the theorem asserts.</param>
    /// <returns>Never returns.</returns>
    /// <exception cref="InvalidOperationException">Always, because theorem methods are never executed.</exception>
    public static Proof That(bool claim) =>
        throw new InvalidOperationException("[Theorem] methods are never executed.");
}
