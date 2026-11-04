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

    /// <summary>The last component of a definition's equation lemma, <c>f.$eq_def</c> (Lean's <c>f.eq_def</c>, M5a KTD15).</summary>
    public const string EquationLemmaComponent = "$eq_def";

    /// <summary>
    /// The equation lemma <c>f.$eq_def</c> of a recursive definition, when it has one (Lean's <c>getUnfoldEqnFor?</c>,
    /// which for a well-founded definition is <c>f.eq_def</c>).
    /// </summary>
    public Name? GetUnfoldEqnFor(Name declName)
    {
        ArgumentNullException.ThrowIfNull(declName);
        var name = declName.Append(EquationLemmaComponent);
        return Env.Find(name) is TheoremInfo ? name : null;
    }

    /// <summary>
    /// Unfolds <paramref name="declName"/> in <paramref name="e"/> (Lean's <c>Meta.unfold</c>, Lean/Meta/Tactic/Unfold.lean
    /// 19-30): a definition with an equation lemma is rewritten with it through simp's traversal, once at each occurrence
    /// and not again inside the result; any other is delta-expanded, a change by definition with no proof.
    /// </summary>
    public SimpResult Unfold(Expr e, Name declName)
    {
        ArgumentNullException.ThrowIfNull(e);
        if (GetUnfoldEqnFor(declName) is { } unfoldThm)
        {
            var theorem = MkSimpTheoremsFromConst(unfoldThm)[0];
            var context = new SimpContext(SimpConfig.Neutral, [], SimpContext.CongrTheoremsOf(Attributes));
            return new Simplifier(this, context, theorem).Run(e);
        }
        return new SimpResult(DeltaExpand(e, n => n == declName));
    }

    /// <summary>
    /// <c>unfold f</c> on the goal (Lean's <c>unfoldTarget</c>, Lean/Meta/Tactic/Unfold.lean 32-36): <see cref="Unfold"/>
    /// in the goal's type, and the goal replaced through the equation's proof, or by a definitionally equal one recorded
    /// with <c>@id</c> when there is none.
    /// </summary>
    /// <returns>The new goal.</returns>
    /// <exception cref="TacticException"><paramref name="declName"/> does not occur in the goal.</exception>
    public MVarId UnfoldTarget(MVarId mvarId, Name declName)
    {
        ArgumentNullException.ThrowIfNull(declName);
        return WithContext(mvarId, () =>
        {
            var target = this.InstantiateMVars(GetMVarType(mvarId));
            var r = Unfold(target, declName);
            if (r.Expr == target)
            {
                throw new TacticException("unfold", mvarId, $"Tactic `unfold` failed to unfold `{PpConst(declName)}` in\n  {Pp(target)}");
            }
            return ApplySimpResultToTarget(mvarId, target, r);
        });
    }
}
