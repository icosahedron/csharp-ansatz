using System;
using System.Diagnostics;

namespace Warrant;

/// <summary>
/// Logical connectives, quantifiers and measures for use in specifications.
/// </summary>
public static class Spec
{
    /// <summary>
    /// Logical implication: <paramref name="premise"/> implies <paramref name="conclusion"/>.
    /// Valid only inside a theorem statement; a stray call elsewhere still computes the implication.
    /// </summary>
    /// <param name="premise">The hypothesis.</param>
    /// <param name="conclusion">What follows from the hypothesis.</param>
    /// <returns><c>!premise || conclusion</c>.</returns>
    public static bool Implies(bool premise, bool conclusion) => !premise || conclusion;

    /// <summary>
    /// Universal quantification: <paramref name="claim"/> holds for every value of <typeparamref name="T"/>.
    /// Valid only inside a theorem statement. It cannot be computed, so a call throws.
    /// </summary>
    /// <typeparam name="T">The type quantified over.</typeparam>
    /// <param name="claim">The claim, a lambda with one parameter.</param>
    /// <returns>Never returns.</returns>
    /// <exception cref="InvalidOperationException">Always, because a quantifier is never executed.</exception>
    public static bool ForAll<T>(Func<T, bool> claim) => throw NotExecuted();

    /// <summary>
    /// Existential quantification: <paramref name="claim"/> holds for some value of <typeparamref name="T"/>.
    /// Valid only inside a theorem statement. It cannot be computed, so a call throws.
    /// </summary>
    /// <typeparam name="T">The type quantified over.</typeparam>
    /// <param name="claim">The claim, a lambda with one parameter.</param>
    /// <returns>Never returns.</returns>
    /// <exception cref="InvalidOperationException">Always, because a quantifier is never executed.</exception>
    public static bool Exists<T>(Func<T, bool> claim) => throw NotExecuted();

    /// <summary>
    /// The measure of a recursive method: a value over the parameters, at least zero, that every recursive call
    /// decreases. It must be the first statement of the method's block body. The compiler removes the call unless
    /// <c>WARRANT_CONTRACTS</c> is defined, and a call that is kept does nothing.
    /// </summary>
    /// <param name="measure">The measure; an <c>int</c> widens implicitly.</param>
    [Conditional("WARRANT_CONTRACTS")]
    public static void Decreases(long measure)
    {
    }

    private static InvalidOperationException NotExecuted() =>
        new("Spec quantifiers are read by Warrant and never executed.");
}
