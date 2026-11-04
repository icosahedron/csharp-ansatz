using Warrant.Cic;
using Warrant.Kernel;

namespace Warrant.Meta;

// Lean/Meta/Tactic/Simp/Rewrite.lean: the default pre and post procedures, rewriting with a theorem
// and synthesizing its arguments, and the decide step.
public sealed partial class Simplifier
{
    // Lean's preDefault: rewritePre >> simpMatch >> the pre simprocs (reduceIte, reduceDIte) >> simpUsingDecide.
    // For unfold, Unfold.lean's pre: the equation lemma at reducible transparency, and done when it rewrites.
    private SimpStep Pre(Expr e) =>
        _unfold is { } thm ? UnfoldPre(e, thm) : AndThen(e, RewritePre, SimpMatch, ReduceIte, ReduceDIte, SimpUsingDecide);

    private SimpStep UnfoldPre(Expr e, SimpTheorem thm)
    {
        if (m.WithReducible(() => TryTheoremWithExtraArgs(e, thm, 0)) is not { } r)
        {
            return SimpStep.Continue;
        }
        return m.ReduceMatcher(r.Expr) is (ReduceMatcherKind.Reduced, { } reduced) ? SimpStep.Done(r with { Expr = reduced }) : SimpStep.Done(r);
    }

    // Lean's postDefault: rewritePost >> simpUsingDecide (the ground and arith steps are off by default).
    // For unfold, Simp.Methods' default post: done.
    private SimpStep Post(Expr e) => _unfold is null ? AndThen(e, RewritePost, SimpUsingDecide) : SimpStep.Done(new(e));

    // Lean's andThen, over a list: the first done or visit wins; continue passes its term on.
    private SimpStep AndThen(Expr e, params Func<Expr, SimpStep>[] procs)
    {
        SimpResult? acc = null;
        foreach (var proc in procs)
        {
            var step = proc(acc?.Expr ?? e);
            if (step.Kind != SimpStepKind.Continue)
            {
                return acc is null ? step : new SimpStep(step.Kind, acc.MkEqTrans(m, step.Result!));
            }
            if (step.Result is { } r)
            {
                acc = acc is null ? r : acc.MkEqTrans(m, r);
            }
        }
        return new SimpStep(SimpStepKind.Continue, acc);
    }

    private SimpStep RewritePre(Expr e)
    {
        foreach (var thms in _theorems)
        {
            if (Rewrite(e, thms.Pre) is { } r)
            {
                return SimpStep.Visit(r);
            }
        }
        return SimpStep.Continue;
    }

    private SimpStep RewritePost(Expr e)
    {
        foreach (var thms in _theorems)
        {
            if (Rewrite(e, thms.Post) is { } r)
            {
                return SimpStep.Visit(r);
            }
        }
        return SimpStep.Continue;
    }

    // Lean's rewrite? with an index: the candidates, highest priority first, the first that rewrites.
    private SimpResult? Rewrite(Expr e, DiscrTree<SimpTheorem> tree)
    {
        var candidates = WithIndexConfig(() => tree.GetMatchWithExtra(m, e));
        if (candidates.Count == 0)
        {
            return null;
        }
        foreach (var (thm, numExtra) in candidates.OrderByDescending(c => c.Value.Priority))
        {
            m.Budget.Tick();
            if (TryTheoremWithExtraArgs(e, thm, numExtra) is { } r)
            {
                return r;
            }
        }
        return null;
    }

    private SimpResult? TryTheoremWithExtraArgs(Expr e, SimpTheorem thm, int numExtraArgs) => m.WithNewMCtxDepth(() =>
    {
        var (val, type) = thm.Instantiate(m);
        var (xs, bis, body) = m.ForallMetaTelescopeReducing(type);
        body = m.Whnf(m.InstantiateMVars(body));
        if (!ExprOps.IsAppOfArity(body, SimpNames.Eq, 3))
        {
            return null;
        }
        var lhs = ((AppExpr)((AppExpr)body).Fn).Arg;
        return TryTheoremCore(lhs, xs, bis, val, body, e, thm, numExtraArgs);
    });

    private SimpResult? TryTheoremCore(Expr lhs, Expr[] xs, BinderInfo[] bis, Expr val, Expr type, Expr e, SimpTheorem thm, int numExtraArgs)
    {
        var extraArgs = new Expr[numExtraArgs];
        for (int i = numExtraArgs - 1; i >= 0; i--)
        {
            extraArgs[i] = ((AppExpr)e).Arg;
            e = ((AppExpr)e).Fn;
        }
        if (!WithMetaConfig(() => m.IsDefEq(lhs, e)))
        {
            return null;
        }
        if (!SynthesizeArgs(bis, xs))
        {
            return null;
        }
        Expr? proof = null;
        if (!(thm.Rfl && Config.ImplicitDefEqProofs))
        {
            proof = m.InstantiateMVars(ExprExtensions.MkAppN(val, xs)).HeadBeta();
            if (m.HasAssignableMVar(proof))
            {
                return null;
            }
        }
        var rhs = ((AppExpr)m.InstantiateMVars(type)).Arg;
        if (m.InstantiateMVars(e) == rhs || m.HasAssignableMVar(rhs))
        {
            return null;
        }
        return new SimpResult(rhs, proof).AddExtraArgs(m, extraArgs);
    }

    /// <summary>
    /// Fills the lemma arguments matching left unassigned (Lean's <c>synthesizeArgs</c>, with
    /// <c>tactic.skipAssignedInstances</c> on): an instance by synthesis, a proposition by the discharger.
    /// </summary>
    private bool SynthesizeArgs(IReadOnlyList<BinderInfo> bis, IReadOnlyList<Expr> xs)
    {
        for (int i = 0; i < xs.Count; i++)
        {
            var x = xs[i];
            if (m.InstantiateMVars(x) is not MVarExpr)
            {
                continue;
            }
            var type = m.InferType(x);
            if (m.IsClass(type) is not null && SynthesizeInstance(x, type))
            {
                continue;
            }
            if (m.IsProp(type) && !Discharge(x, type))
            {
                return false;
            }
        }
        return true;
    }

    private bool SynthesizeInstance(Expr x, Expr type) =>
        m.TrySynthInstance(type, out var val) == LBool.True && m.WithReducibleAndInstances(() => m.IsDefEq(x, val!));

    // Lean's discharge?': bounded depth, results computed inside not cached.
    private bool Discharge(Expr x, Expr type)
    {
        if (_dischargeDepth >= Config.MaxDischargeDepth)
        {
            return false;
        }
        _dischargeDepth++;
        var savedCache = _cache;
        _cache = new Dictionary<Expr, SimpResult>(savedCache);
        try
        {
            return DischargeDefault(type) is { } proof && m.IsDefEq(x, proof);
        }
        finally
        {
            _cache = savedCache;
            _dischargeDepth--;
        }
    }

    /// <summary>
    /// Warrant's discharger (Lean's <c>dischargeDefault?</c>): a hypothesis of the side condition's type, else simp the
    /// side condition to <c>True</c> (with <c>decide</c>, which settles a closed one), or to an equation that
    /// <c>rfl</c> closes.
    /// </summary>
    private Expr? DischargeDefault(Expr e)
    {
        e = e.ConsumeMData();
        if (DischargeUsingAssumption(e) is { } h)
        {
            return h;
        }
        var r = Simp(e);
        if (DischargeRfl(r.Expr) is { } p)
        {
            return Expr.App(Expr.Const(SimpNames.EqMpr, Level.Zero), e, r.Expr, r.GetProof(m), p);
        }
        return r.Expr.IsConstOf(SimpNames.True) ? m.MkOfEqTrue(r.GetProof(m)) : null;
    }

    // Lean's dischargeUsingAssumption?: without contextual, only hypotheses that were there when simp started.
    private Expr? DischargeUsingAssumption(Expr e)
    {
        foreach (var decl in m.LCtx.DeclsReversed())
        {
            if (decl.IsImplementationDetail || (!Config.Contextual && decl.Index >= _lctxInitSize))
            {
                continue;
            }
            if (WithMetaConfig(() => m.IsDefEq(e, decl.Type)))
            {
                return decl.ToExpr();
            }
        }
        return null;
    }

    // Lean's dischargeRfl: ∀ xs, a = b with a metavariable at the head of a side.
    private Expr? DischargeRfl(Expr e) => m.ForallTelescope(e, (xs, body) =>
    {
        if (!ExprOps.IsAppOfArity(body, SimpNames.Eq, 3) || body.GetAppArgs() is not [var t, var a, var b]
            || (a.GetAppFn() is not MVarExpr && b.GetAppFn() is not MVarExpr)
            || !WithMetaConfig(() => m.IsDefEq(a, b)))
        {
            return null;
        }
        return m.MkLambdaFVars(xs, Expr.App(Expr.Const(SimpNames.Rfl, m.GetLevel(t)), t, a));
    });

    /// <summary>
    /// Lean's <c>simpUsingDecide</c>: a closed proposition whose <c>decide</c> evaluates, at default transparency, to
    /// <c>true</c> or <c>false</c> becomes <c>True</c> or <c>False</c>, by <c>eq_true_of_decide</c> or
    /// <c>eq_false_of_decide</c> on <c>Eq.refl</c>, which the kernel checks by evaluating it again.
    /// </summary>
    private SimpStep SimpUsingDecide(Expr e)
    {
        if (!Config.Decide || e.HasFVar || e.HasExprMVar || e.HasLevelMVar || e.IsConstOf(SimpNames.True) || e.IsConstOf(SimpNames.False))
        {
            return SimpStep.Continue;
        }
        try
        {
            if (!m.IsProp(e))
            {
                return SimpStep.Continue;
            }
            var d = m.MkDecide(e);
            var r = m.WithDefault(() => m.Whnf(d));
            var inst = ((AppExpr)d).Arg;
            if (r.IsConstOf(SimpNames.BoolTrue))
            {
                var refl = m.MkEqRefl(Expr.Const(SimpNames.BoolTrue));
                return SimpStep.Done(new(Expr.Const(SimpNames.True), Expr.App(Expr.Const(SimpNames.EqTrueOfDecide), e, inst, refl)));
            }
            if (r.IsConstOf(SimpNames.BoolFalse))
            {
                var refl = m.MkEqRefl(Expr.Const(SimpNames.BoolFalse));
                return SimpStep.Done(new(Expr.Const(SimpNames.False), Expr.App(Expr.Const(SimpNames.EqFalseOfDecide), e, inst, refl)));
            }
            return SimpStep.Continue;
        }
        catch (MetaException ex) when (ex is not MetaResourceException)
        {
            return SimpStep.Continue;
        }
    }

    // Lean's simpMatch, for recursors and matchers on constructors; matcher equations are not ported.
    private SimpStep SimpMatch(Expr e)
    {
        if (!Config.Iota)
        {
            return SimpStep.Continue;
        }
        return WithMetaConfig(() => m.ReduceRecMatcher(e)) is { } reduced ? SimpStep.Visit(new(reduced)) : SimpStep.Continue;
    }
}
