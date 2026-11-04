using Warrant.Cic;
using Warrant.Kernel;

namespace Warrant.Meta;

// Lean/Meta/Tactic/Simp/Main.lean (congr, trySimpCongrTheorem?, processCongrHypothesis) and
// Types.lean (simpAppUsingCongr, congrArgs): simplifying inside an application.
public sealed partial class Simplifier
{
    private SimpResult SimpApp(Expr e) => IsOfNatNatLit(e) ? new(e) : Congr(e);

    private SimpResult Congr(Expr e)
    {
        if (e.GetAppFn() is ConstExpr f && Context.CongrTheorems.TryGetValue(f.Name, out var congrs))
        {
            foreach (var c in congrs)
            {
                if (TrySimpCongrTheorem(c, e) is { } r)
                {
                    return r;
                }
            }
        }
        // Lean's congrDefault tries an automatically generated congruence lemma first; that is not ported.
        return SimpAppUsingCongr(e);
    }

    /// <summary>The failure of a <c>@[congr]</c> lemma's hypothesis (Lean's <c>throwCongrHypothesisFailed</c>).</summary>
    private sealed class CongrHypothesisFailedException : MetaException
    {
        public CongrHypothesisFailedException()
            : base("congruence hypothesis failed")
        {
        }
    }

    // Lean's trySimpCongrTheorem?.
    private SimpResult? TrySimpCongrTheorem(CongrEntry c, Expr e) => m.WithNewMCtxDepth(() =>
    {
        if (m.Env.Find(c.Name) is null)
        {
            return null;
        }
        var thm = m.MkConstWithFreshMVarLevels(c.Name);
        var (xs, bis, type) = m.ForallMetaTelescopeReducing(m.InferType(thm));
        if (c.Hypotheses.Any(i => i >= xs.Length) || type is not AppExpr { Fn: AppExpr { Arg: var lhs } } typeApp)
        {
            return null;
        }
        bool isIff = type.IsAppOf(SimpNames.Iff);
        var rhs = typeApp.Arg;
        int numArgs = lhs.GetAppNumArgs();
        var extraArgs = new List<Expr>();
        var args = e.GetAppArgs();
        if (args.Length > numArgs)
        {
            e = ExprExtensions.MkAppRange(e.GetAppFn(), 0, numArgs, args);
            extraArgs.AddRange(args[numArgs..]);
        }
        if (!WithMetaConfig(() => m.IsDefEq(lhs, e)))
        {
            return null;
        }
        bool modified = false;
        foreach (int i in c.Hypotheses)
        {
            var h = xs[i];
            var hType = m.InstantiateMVars(m.InferType(h));
            try
            {
                if (ProcessCongrHypothesis(h, hType))
                {
                    modified = true;
                }
            }
            catch (MetaException ex) when (ex is not MetaResourceException)
            {
                return null;
            }
        }
        if (!modified || !SynthesizeArgs(bis, xs))
        {
            return null;
        }
        var eNew = m.InstantiateMVars(rhs);
        var proof = m.InstantiateMVars(ExprExtensions.MkAppN(thm, xs));
        if (isIff)
        {
            try
            {
                proof = m.MkPropExt(proof);
            }
            catch (MetaException ex) when (ex is not MetaResourceException)
            {
                return null;
            }
        }
        if (m.HasAssignableMVar(proof) || m.HasAssignableMVar(eNew))
        {
            return null;
        }
        return CongrArgs(new SimpResult(eNew, proof), extraArgs);
    });

    // Lean's processCongrHypothesis: simplify the hypothesis's left side and assign its right side.
    private bool ProcessCongrHypothesis(Expr h, Expr hType) => m.ForallTelescopeReducing(hType, (xs, body) => WithNewLemmas(xs, () =>
    {
        if (body is not AppExpr { Fn: AppExpr { Arg: var lhsRaw } } bodyApp || !body.IsAppOf(SimpNames.Eq))
        {
            // An `↔` hypothesis needs Lean's mkIffOfEq; Init's ite_congr and dite_congr have none.
            throw new CongrHypothesisFailedException();
        }
        var lhs = m.InstantiateMVars(lhsRaw);
        var r = Simp(lhs);
        var rhs = bodyApp.Arg;
        var val = m.MkLambdaFVars(rhs.GetAppArgs(), r.Expr);
        if (!WithMetaConfig(() => m.IsDefEq(rhs.GetAppFn(), val)))
        {
            throw new CongrHypothesisFailedException();
        }
        if (!m.IsDefEq(h, m.MkLambdaFVars(xs, r.GetProof(m))))
        {
            throw new CongrHypothesisFailedException();
        }
        return r.Proof is not null || (xs.Length > 0 && lhs != r.Expr);
    }));

    // Lean's congrArgs: simplify extra arguments after a congruence lemma.
    private SimpResult CongrArgs(SimpResult r, IReadOnlyList<Expr> args)
    {
        if (args.Count == 0)
        {
            return r;
        }
        var infos = m.GetFunInfoNArgs(r.Expr, args.Count).ParamInfo;
        for (int i = 0; i < args.Count; i++)
        {
            var arg = args[i];
            if (i < infos.Length && infos[i].IsInstance)
            {
                r = r.MkCongrFun(m, arg);
            }
            else if ((i < infos.Length && !infos[i].HasFwdDeps) || IsArrowType(r.Expr))
            {
                r = SimpResult.MkCongr(m, r, Simp(arg));
            }
            else
            {
                r = r.MkCongrFun(m, Dsimp(arg));
            }
        }
        return r;
    }

    private bool IsArrowType(Expr f) => m.WhnfD(m.InferType(f)) is ForallExpr { Body.HasLooseBVars: false };

    // Lean's simpAppUsingCongr: the function, then each argument, with congrArg, congrFun, congrFun' and congr.
    private SimpResult SimpAppUsingCongr(Expr e)
    {
        var f = e.GetAppFn();
        int numArgs = e.GetAppNumArgs();
        var infos = m.GetFunInfoNArgs(f, numArgs).ParamInfo;
        return Visit(e, numArgs);

        SimpResult Visit(Expr x, int i)
        {
            if (i == 0)
            {
                return Simp(f);
            }
            m.Budget.Tick();
            i--;
            var app = (AppExpr)x;
            var fr = Visit(app.Fn, i);
            var a = app.Arg;
            if (i < infos.Length && infos[i].IsInstance)
            {
                return MkCongrFun2(app, fr, a);
            }
            if ((i < infos.Length && !infos[i].HasFwdDeps) || IsArrowType(f))
            {
                return MkCongr2(app, fr, Simp(a));
            }
            return MkCongrFun2(app, fr, Dsimp(a));
        }
    }

    // Lean's mkCongrFun' (simpAppUsingCongr's helper).
    private SimpResult MkCongrFun2(AppExpr e, SimpResult r, Expr a)
    {
        var eNew = e.UpdateApp(r.Expr, a);
        if (r.Proof is not { } hf)
        {
            return new(eNew);
        }
        var α = m.InferType(a);
        var u = m.GetLevel(α);
        var v = m.GetLevel(m.InferType(e));
        if (m.WhnfD(m.InferType(e.Fn)) is not ForallExpr pi)
        {
            throw new MetaException($"failed to build congruence proof, function expected\n  {e.Fn}");
        }
        var β = Expr.Lam(pi.BinderName, α, pi.Body);
        return new(eNew, Expr.App(Expr.Const(SimpNames.CongrFun, u, v), α, β, e.Fn, r.Expr, hf, a));
    }

    // Lean's mkCongrPrefix.
    private Expr MkCongrPrefix(Name declName, AppExpr e)
    {
        var α = m.InferType(e.Arg);
        var β = m.InferType(e);
        return Expr.App(Expr.Const(declName, m.GetLevel(α), m.GetLevel(β)), α, β);
    }

    // Lean's mkCongr' (simpAppUsingCongr's helper).
    private SimpResult MkCongr2(AppExpr e, SimpResult r1, SimpResult r2)
    {
        var eNew = e.UpdateApp(r1.Expr, r2.Expr);
        return (r1.Proof, r2.Proof) switch
        {
            (null, null) => new(eNew),
            ({ } hf, null) => new(eNew, Expr.App(MkCongrPrefix(SimpNames.CongrFun2, e), e.Fn, r1.Expr, hf, r2.Expr)),
            (null, { } ha) => new(eNew, Expr.App(MkCongrPrefix(SimpNames.CongrArg, e), e.Arg, r2.Expr, r1.Expr, ha)),
            ({ } hf, { } ha) => new(eNew, Expr.App(MkCongrPrefix(SimpNames.Congr, e), e.Fn, r1.Expr, e.Arg, r2.Expr, hf, ha)),
        };
    }
}
