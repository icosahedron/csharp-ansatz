using Warrant.Cic;

namespace Warrant.Meta;

/// <summary>
/// The result of simplifying a term <c>e</c> (Lean's <c>Simp.Result</c>): the new term and a proof of
/// <c>e = Expr</c>, or <see langword="null"/> when the change is by definition.
/// </summary>
/// <param name="Expr">The simplified term.</param>
/// <param name="Proof">The proof of <c>e = Expr</c>, or null for a definitional change.</param>
public sealed record SimpResult(Expr Expr, Expr? Proof = null)
{
    /// <summary>The proof, or <c>Eq.refl</c> (Lean's <c>Result.getProof</c>).</summary>
    public Expr GetProof(MetaM m)
    {
        ArgumentNullException.ThrowIfNull(m);
        return Proof ?? m.MkEqRefl(Expr);
    }

    /// <summary>
    /// <paramref name="next"/>, which simplifies this result's term, as a result for the original term (Lean's
    /// <c>Result.mkEqTrans</c>).
    /// </summary>
    public SimpResult MkEqTrans(MetaM m, SimpResult next)
    {
        ArgumentNullException.ThrowIfNull(m);
        ArgumentNullException.ThrowIfNull(next);
        return Proof is null ? next
            : next.Proof is null ? next with { Proof = Proof }
            : next with { Proof = m.MkEqTrans(Proof, next.Proof) };
    }

    /// <summary><c>Expr a</c>, with <c>congrFun</c> (Lean's <c>Simp.mkCongrFun</c>).</summary>
    public SimpResult MkCongrFun(MetaM m, Expr a)
    {
        ArgumentNullException.ThrowIfNull(m);
        return new(Cic.Expr.App(Expr, a), Proof is null ? null : m.MkCongrFun(Proof, a));
    }

    /// <summary><c>f₁ a₁</c> from <c>f</c> and <c>a</c> simplified, with <c>congr</c>, <c>congrArg</c> or <c>congrFun</c> (Lean's <c>Simp.mkCongr</c>).</summary>
    public static SimpResult MkCongr(MetaM m, SimpResult f, SimpResult a)
    {
        ArgumentNullException.ThrowIfNull(m);
        ArgumentNullException.ThrowIfNull(f);
        ArgumentNullException.ThrowIfNull(a);
        var e = Cic.Expr.App(f.Expr, a.Expr);
        return (f.Proof, a.Proof) switch
        {
            (null, null) => new(e),
            ({ } h, null) => new(e, m.MkCongrFun(h, a.Expr)),
            (null, { } h) => new(e, m.MkCongrArg(f.Expr, h)),
            ({ } h1, { } h2) => new(e, m.MkCongr(h1, h2)),
        };
    }

    /// <summary>This result applied to <paramref name="extraArgs"/>, with <c>congrFun</c> (Lean's <c>Result.addExtraArgs</c>).</summary>
    public SimpResult AddExtraArgs(MetaM m, IReadOnlyList<Expr> extraArgs)
    {
        ArgumentNullException.ThrowIfNull(extraArgs);
        var r = this;
        foreach (var a in extraArgs)
        {
            r = r.MkCongrFun(m, a);
        }
        return r;
    }
}

/// <summary>What a simplification procedure returns (Lean's <c>Simp.Step</c>).</summary>
internal enum SimpStepKind
{
    /// <summary>The result, without visiting it further.</summary>
    Done,

    /// <summary>The result, to be simplified again.</summary>
    Visit,

    /// <summary>Go on with the next procedure, or with the subterms, from <see cref="SimpStep.Result"/> if there is one.</summary>
    Continue,
}

/// <summary>A simplification procedure's answer (Lean's <c>Simp.Step</c>).</summary>
internal readonly record struct SimpStep(SimpStepKind Kind, SimpResult? Result)
{
    public static SimpStep Continue { get; } = new(SimpStepKind.Continue, null);

    public static SimpStep Done(SimpResult r) => new(SimpStepKind.Done, r);

    public static SimpStep Visit(SimpResult r) => new(SimpStepKind.Visit, r);
}

/// <summary>
/// <c>simp</c>'s configuration (Lean's <c>Simp.Config</c>, Init/MetaTypes.lean), with Lean's defaults except where
/// Warrant's <c>Tactic.Simp()</c> differs (plan Key Decisions): <see cref="Decide"/> and <see cref="Contextual"/> are on.
/// The options for ported features only are kept.
/// </summary>
public sealed record SimpConfig
{
    /// <summary>Warrant's defaults: Lean's, with <c>decide</c> and <c>contextual</c> on.</summary>
    public static SimpConfig Default { get; } = new();

    /// <summary>The most terms one run may visit (Lean's <c>maxSteps</c>).</summary>
    public int MaxSteps { get; init; } = 100_000;

    /// <summary>How deeply side conditions may be discharged by simp (Lean's <c>maxDischargeDepth</c>).</summary>
    public int MaxDischargeDepth { get; init; } = 2;

    /// <summary>Use an implication's premise while simplifying its conclusion (Lean's <c>contextual</c>).</summary>
    public bool Contextual { get; init; } = true;

    /// <summary>Close a closed proposition by evaluating <c>decide</c> (Lean's <c>decide</c>).</summary>
    public bool Decide { get; init; } = true;

    /// <summary>Cache results (Lean's <c>memoize</c>).</summary>
    public bool Memoize { get; init; } = true;

    /// <summary>Visit a rewritten term only once (Lean's <c>singlePass</c>).</summary>
    public bool SinglePass { get; init; }

    /// <summary>Beta-reduce (Lean's <c>beta</c>).</summary>
    public bool Beta { get; init; } = true;

    /// <summary>Reduce projections of constructors (Lean's <c>proj</c>).</summary>
    public bool Proj { get; init; } = true;

    /// <summary>Reduce recursors and matchers on constructors (Lean's <c>iota</c>).</summary>
    public bool Iota { get; init; } = true;

    /// <summary>Zeta-reduce <c>let</c> (Lean's <c>zeta</c>).</summary>
    public bool Zeta { get; init; } = true;

    /// <summary>Drop unused <c>let</c>s (Lean's <c>zetaUnused</c>).</summary>
    public bool ZetaUnused { get; init; } = true;

    /// <summary>Fail when nothing changed (Lean's <c>failIfUnchanged</c>).</summary>
    public bool FailIfUnchanged { get; init; } = true;

    /// <summary>A definitional lemma's rewrite carries no proof (Lean's <c>implicitDefEqProofs</c>).</summary>
    public bool ImplicitDefEqProofs { get; init; } = true;
}
