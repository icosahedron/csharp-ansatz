using Warrant.Cic;
using Warrant.Kernel;

namespace Warrant.Meta;

// Lean/Meta/Tactic/Simp/BuiltinSimprocs/Core.lean: the structural simprocs reduceIte and reduceDIte,
// hard-coded as pre procedures (KTD11). Lean's simproc registry is not ported.
public sealed partial class Simplifier
{
    /// <summary><c>if c then a else b</c> is <c>a</c> when <c>c</c> simplifies to <c>True</c>, <c>b</c> when to <c>False</c> (Lean's <c>reduceIte</c>).</summary>
    private SimpStep ReduceIte(Expr e)
    {
        if (!ExprOps.IsAppOfArity(e, SimpNames.Ite, 5) || e.GetAppFn() is not ConstExpr f)
        {
            return SimpStep.Continue;
        }
        var args = e.GetAppArgs();
        var r = Simp(args[1]);
        if (r.Expr.IsConstOf(SimpNames.True))
        {
            var pr = Expr.App(Expr.Const(SimpNames.IteEqLeftOfEqTrue, f.Levels), [.. args, r.GetProof(m)]);
            return SimpStep.Visit(new(args[3], pr));
        }
        if (r.Expr.IsConstOf(SimpNames.False))
        {
            var pr = Expr.App(Expr.Const(SimpNames.IteEqRightOfEqFalse, f.Levels), [.. args, r.GetProof(m)]);
            return SimpStep.Visit(new(args[4], pr));
        }
        return SimpStep.Continue;
    }

    /// <summary>
    /// <c>if h : c then t h else e h</c> is <c>t (of_eq_true …)</c> when <c>c</c> simplifies to <c>True</c>, and
    /// <c>e (of_eq_false …)</c> when to <c>False</c> (Lean's <c>reduceDIte</c>).
    /// </summary>
    private SimpStep ReduceDIte(Expr e)
    {
        if (!ExprOps.IsAppOfArity(e, SimpNames.Dite, 5) || e.GetAppFn() is not ConstExpr f)
        {
            return SimpStep.Continue;
        }
        var args = e.GetAppArgs();
        var c = args[1];
        var r = Simp(c);
        if (r.Expr.IsConstOf(SimpNames.True))
        {
            var pr = r.GetProof(m);
            var h = Expr.App(Expr.Const(SimpNames.OfEqTrue), c, pr);
            var prNew = Expr.App(Expr.Const(SimpNames.DiteEqLeftOfEqTrue, f.Levels), [.. args, pr]);
            return SimpStep.Visit(new(Expr.App(args[3], h).HeadBeta(), prNew));
        }
        if (r.Expr.IsConstOf(SimpNames.False))
        {
            var pr = r.GetProof(m);
            var h = Expr.App(Expr.Const(SimpNames.OfEqFalse), c, pr);
            var prNew = Expr.App(Expr.Const(SimpNames.DiteEqRightOfEqFalse, f.Levels), [.. args, pr]);
            return SimpStep.Visit(new(Expr.App(args[4], h).HeadBeta(), prNew));
        }
        return SimpStep.Continue;
    }
}
