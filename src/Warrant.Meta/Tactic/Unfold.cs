using Warrant.Cic;
using Warrant.Kernel;

namespace Warrant.Meta;

public sealed partial class MetaM
{
    /// <summary>
    /// Replaces each application of a definition (or theorem) satisfying <paramref name="p"/> by its value, beta-reduced,
    /// top-down and again inside each result (Lean's <c>deltaExpand</c> and <c>delta?</c>, Lean/Meta/Tactic/Delta.lean
    /// 13-26, over <c>Core.transform</c>).
    /// </summary>
    public Expr DeltaExpand(Expr e, Func<Name, bool> p)
    {
        ArgumentNullException.ThrowIfNull(e);
        ArgumentNullException.ThrowIfNull(p);
        var cache = new Dictionary<Expr, Expr>(ReferenceEqualityComparer.Instance);
        return Visit(e);

        Expr Visit(Expr x)
        {
            if (cache.TryGetValue(x, out var done))
            {
                return done;
            }
            Budget.Tick();
            var result = Delta(x) is { } expanded ? Visit(expanded) : x switch
            {
                AppExpr => ExprExtensions.MkAppN(Visit(x.GetAppFn()), [.. x.GetAppArgs().Select(Visit)]),
                BindingExpr b => b.UpdateBinding(Visit(b.BinderType), Visit(b.Body)),
                LetExpr l => l.UpdateLet(Visit(l.BinderType), Visit(l.Value), Visit(l.Body)),
                MDataExpr m => m.UpdateMData(Visit(m.Expr)),
                ProjExpr pr => pr.UpdateProj(Visit(pr.Struct)),
                _ => x,
            };
            cache[x] = result;
            return result;
        }

        Expr? Delta(Expr x)
        {
            if (x.GetAppFn() is not ConstExpr c || !p(c.Name) || Env.Find(c.Name) is not { } info
                || info is not (DefinitionInfo or TheoremInfo) || info.LevelParams.Count != c.Levels.Count)
            {
                return null;
            }
            return ExprOps.InstantiateValueLevelParams(info, c.Levels).BetaRev(x.GetAppRevArgs(), useZeta: true);
        }
    }

    /// <summary>
    /// <c>unfold f</c> on the goal, for a non-recursive <paramref name="declName"/>: delta-expands it in the goal's type and
    /// replaces the goal by a definitionally equal one, recorded with <c>@id</c> (Lean's <c>unfoldTarget</c> on its
    /// <c>deltaExpand</c> path, Lean/Meta/Tactic/Unfold.lean 19-37). A recursive definition unfolds through its equation
    /// lemma with simp's machinery, which comes with simp (chapter 5).
    /// </summary>
    /// <returns>The new goal.</returns>
    /// <exception cref="TacticException"><paramref name="declName"/> does not occur in the goal.</exception>
    public MVarId UnfoldTarget(MVarId mvarId, Name declName)
    {
        ArgumentNullException.ThrowIfNull(declName);
        return WithContext(mvarId, () =>
        {
            var target = this.InstantiateMVars(GetMVarType(mvarId));
            var unfolded = DeltaExpand(target, n => n == declName);
            if (unfolded == target)
            {
                throw new TacticException("unfold", mvarId, $"Tactic `unfold` failed to unfold `{PpConst(declName)}` in\n  {Pp(target)}");
            }
            return ReplaceTargetDefEq(mvarId, unfolded);
        });
    }
}
