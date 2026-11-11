namespace Warrant;

/// <summary>
/// A step of a proof script, for <see cref="Proof.By(Tactic[])"/>. Warrant reads tactics from source; they never run.
/// </summary>
/// <remarks>
/// Names follow one rule: <c>nameof(M)</c> names a C# member (a <see cref="VerifiedAttribute"/> member or a
/// <see cref="TheoremAttribute"/> method), <see cref="Lean.Const(string)"/> names a Lean declaration, and a string
/// literal names a hypothesis or variable in the goal.
/// </remarks>
public sealed class Tactic
{
    private Tactic()
    {
    }

    /// <summary>Moves <c>∀</c> variables and <c>→</c> hypotheses into the context, with the given names.</summary>
    /// <param name="names">The names, as string literals.</param>
    /// <returns>The tactic.</returns>
    public static Tactic Intro(params string[] names) => new();

    /// <summary>Closes the goal with a lemma or hypothesis.</summary>
    /// <param name="term">A hypothesis name, <c>nameof</c> of a theorem, or <see cref="Lean.Const(string)"/>.</param>
    /// <returns>The tactic.</returns>
    public static Tactic Exact(object term) => new();

    /// <summary>Reduces the goal with a lemma or hypothesis whose conclusion matches it.</summary>
    /// <param name="term">A hypothesis name, <c>nameof</c> of a theorem, or <see cref="Lean.Const(string)"/>.</param>
    /// <returns>The tactic.</returns>
    public static Tactic Apply(object term) => new();

    /// <summary>Splits the goal into one goal per constructor of a variable's type.</summary>
    /// <param name="target">The variable's name, as a string literal.</param>
    /// <returns>The tactic.</returns>
    public static Tactic Cases(object target) => new();

    /// <summary>Proves the goal by induction on a variable.</summary>
    /// <param name="target">The variable's name, as a string literal.</param>
    /// <returns>The tactic.</returns>
    public static Tactic Induction(object target) => new();

    /// <summary>Replaces calls to the named members by their definitions.</summary>
    /// <param name="names">The members, each written <c>nameof(M)</c>.</param>
    /// <returns>The tactic.</returns>
    public static Tactic Unfold(params string[] names) => new();

    /// <summary>Simplifies the goal with the default simp set plus the given lemmas.</summary>
    /// <param name="lemmas">Each <c>nameof</c> of a theorem or member, or <see cref="Lean.Const(string)"/>.</param>
    /// <returns>The tactic.</returns>
    public static Tactic Simp(params object[] lemmas) => new();

    /// <summary>Decides linear integer arithmetic over <c>int</c> and <c>long</c>.</summary>
    /// <returns>The tactic.</returns>
    public static Tactic Omega() => new();

    /// <summary>
    /// Runs Warrant's verification-condition generator on a contract obligation, leaving the conditions it cannot close
    /// for the steps after it (milestone M6). For a <see cref="ProofForAttribute"/> script, which starts at the
    /// obligation itself, and for <see cref="Spec.Assert(bool, Tactic[])"/>.
    /// </summary>
    /// <returns>The tactic.</returns>
    public static Tactic VcGen() => new();

    /// <summary>Runs a tactic on every open goal.</summary>
    /// <param name="tactic">The tactic.</param>
    /// <returns>The tactic.</returns>
    public static Tactic AllGoals(Tactic tactic) => new();

    /// <summary>Runs a tactic, and does nothing if it fails.</summary>
    /// <param name="tactic">The tactic.</param>
    /// <returns>The tactic.</returns>
    public static Tactic Try(Tactic tactic) => new();

    /// <summary>
    /// Sets options of a <see cref="Simp(object[])"/> step, as in <c>Tactic.Simp().With(decide: false)</c>;
    /// an option left null keeps its default.
    /// </summary>
    /// <param name="decide">Whether simp closes decidable goals by evaluation.</param>
    /// <param name="contextual">Whether simp uses a hypothesis while simplifying what it implies.</param>
    /// <returns>The tactic with the options.</returns>
    public Tactic With(bool? decide = null, bool? contextual = null) => this;
}
