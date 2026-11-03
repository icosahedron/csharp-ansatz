namespace Warrant;

/// <summary>
/// Logical connectives for use inside theorem statements.
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
}
