using System;

namespace Warrant;

/// <summary>
/// States the claim of a <see cref="TheoremAttribute"/> or <see cref="ProofForAttribute"/> method.
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

    /// <summary>
    /// The contract obligation of the method a <see cref="ProofForAttribute"/> method proves, for its script to attach
    /// to with <see cref="Proof.By(Tactic[])"/> (milestone M6). Warrant reads it from source; the call is never meant to run.
    /// </summary>
    /// <returns>Never returns.</returns>
    /// <exception cref="InvalidOperationException">Always, because proof methods are never executed.</exception>
    public static Proof Contract() =>
        throw new InvalidOperationException("[ProofFor] methods are never executed.");
}
