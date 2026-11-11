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

    /// <summary>
    /// The method's precondition: what it assumes of its parameters on entry. Warrant proves it at every verified call
    /// site and assumes it while proving the method (milestone M6). It must lead the method's block body, after any
    /// <see cref="Decreases(long)"/> and before any <c>Ensures</c>. The compiler removes the call unless
    /// <c>WARRANT_CONTRACTS</c> is defined, and a call that is kept does nothing, so nothing checks it at run time.
    /// </summary>
    /// <param name="condition">The precondition, over the parameters.</param>
    [Conditional("WARRANT_CONTRACTS")]
    public static void Requires(bool condition)
    {
    }

    /// <summary>
    /// The method's postcondition on a normal return, for a method that returns a value: <paramref name="condition"/>
    /// holds of the returned value. Warrant proves it for the method and assumes it at verified call sites (milestone
    /// M6). It must lead the method's block body, after any <c>Requires</c>. The compiler removes the call unless
    /// <c>WARRANT_CONTRACTS</c> is defined, and a call that is kept does nothing.
    /// </summary>
    /// <typeparam name="T">The method's return type, or the awaited type of its <c>Task&lt;T&gt;</c> or <c>ValueTask&lt;T&gt;</c>.</typeparam>
    /// <param name="condition">The postcondition, a lambda over the returned value, such as <c>r =&gt; r &gt;= 0</c>.</param>
    [Conditional("WARRANT_CONTRACTS")]
    public static void Ensures<T>(Func<T, bool> condition)
    {
    }

    /// <summary>
    /// The method's postcondition on a normal return, for a <c>void</c>, <c>Task</c> or <c>ValueTask</c> method.
    /// Warrant proves it for the method and assumes it at verified call sites (milestone M6). It must lead the method's
    /// block body, after any <c>Requires</c>. The compiler removes the call unless <c>WARRANT_CONTRACTS</c> is defined,
    /// and a call that is kept does nothing.
    /// </summary>
    /// <param name="condition">The postcondition, a lambda with no parameters.</param>
    [Conditional("WARRANT_CONTRACTS")]
    public static void Ensures(Func<bool> condition)
    {
    }

    /// <summary>
    /// An intermediate fact Warrant proves at this point of a verified method, and then uses (milestone M6). The
    /// <paramref name="script"/>, if any, proves it in place of the default procedure. The compiler removes the call
    /// unless <c>WARRANT_CONTRACTS</c> is defined, and a call that is kept does nothing, so nothing checks it at run time.
    /// </summary>
    /// <param name="condition">The fact, over the parameters and locals in scope.</param>
    /// <param name="script">The tactics that prove it, in order; none for the default procedure.</param>
    [Conditional("WARRANT_CONTRACTS")]
    public static void Assert(bool condition, params Tactic[] script)
    {
    }

    private static InvalidOperationException NotExecuted() =>
        new("Spec quantifiers are read by Warrant and never executed.");
}
