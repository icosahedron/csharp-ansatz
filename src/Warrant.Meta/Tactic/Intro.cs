using Warrant.Cic;

namespace Warrant.Meta;

public sealed partial class MetaM
{
    /// <summary>
    /// Introduces <paramref name="n"/> binders of the goal's type, <c>∀</c> or <c>let</c>, as hypotheses (Lean's
    /// <c>introNCore</c> and <c>introNImp</c>, Lean/Meta/Tactic/Intro.lean 15-76 and 123): assigns
    /// <c>?g := fun xs => ?g'</c>, which <see cref="MkLambdaFVars"/> records as a delayed assignment, and returns the new
    /// hypotheses and the new goal <c>?g'</c>. When the type is not syntactically a binder, it is instantiated, stripped
    /// of annotations and put in weak head normal form, as Lean does.
    /// </summary>
    /// <param name="mvarId">The goal.</param>
    /// <param name="n">How many binders to introduce.</param>
    /// <param name="givenNames">
    /// The hypotheses' names, in order; <c>_</c> or a missing name keeps the binder's own name, which for a theorem's
    /// parameter is the C# parameter's (Lean's <c>introNP</c> with <c>preserveBinderNames</c>). Warrant does not make the
    /// hygienic <c>x✝</c> names Lean makes for unnamed introductions, so goals stay readable.
    /// </param>
    /// <returns>The new hypotheses and the new goal.</returns>
    /// <exception cref="TacticException">The type has fewer than <paramref name="n"/> binders, even after reduction.</exception>
    public (FVarId[] FVars, MVarId Goal) IntroN(MVarId mvarId, int n, IReadOnlyList<Name>? givenNames = null)
    {
        ArgumentOutOfRangeException.ThrowIfNegative(n);
        if (n == 0)
        {
            return ([], mvarId);
        }
        var names = givenNames ?? [];
        return WithContext(mvarId, () =>
        {
            CheckNotAssigned(mvarId, "introN");
            var type = GetMVarType(mvarId);
            var lctx = LCtx;
            var fvars = new List<Expr>();
            int j = 0;
            int i = n;
            while (true)
            {
                Budget.Tick();
                if (i == 0)
                {
                    var body = type.InstantiateRevRange(j, fvars.Count, fvars);
                    return WithLCtx(lctx, LocalInstances, () =>
                    {
                        var newMVar = MkFreshExprSyntheticOpaqueMVar(body.HeadBeta(), GetTag(mvarId));
                        Assign(mvarId, MkLambdaFVars(fvars, newMVar));
                        return (fvars.Select(f => ((FVarExpr)f).Id).ToArray(), newMVar.Id);
                    });
                }
                switch (type)
                {
                    case LetExpr let:
                        {
                            var t = let.BinderType.InstantiateRevRange(j, fvars.Count, fvars).HeadBeta();
                            var v = let.Value.InstantiateRevRange(j, fvars.Count, fvars);
                            var fvarId = MkFreshFVarId();
                            // Lean makes every introduced let a dependent local definition (Intro.lean 38-43).
                            lctx = lctx.MkLetDecl(fvarId, NameFor(n - i, let.BinderName), t, v);
                            fvars.Add(Expr.FVar(fvarId));
                            type = let.Body;
                            i--;
                            continue;
                        }
                    case ForallExpr f:
                        {
                            var d = f.BinderType.InstantiateRevRange(j, fvars.Count, fvars).HeadBeta();
                            var fvarId = MkFreshFVarId();
                            lctx = lctx.MkLocalDecl(fvarId, NameFor(n - i, f.BinderName), d, f.BinderInfo);
                            fvars.Add(Expr.FVar(fvarId));
                            type = f.Body;
                            i--;
                            continue;
                        }
                }
                var open = type.InstantiateRevRange(j, fvars.Count, fvars);
                type = WithLCtx(lctx, LocalInstances, () =>
                {
                    // Lean instantiates and strips annotations before whnf, which would also expand a let (Intro.lean 60-73).
                    var newType = CleanupAnnotations(this.InstantiateMVars(open));
                    if (newType is ForallExpr or LetExpr)
                    {
                        return newType;
                    }
                    newType = Whnf(newType);
                    return newType is ForallExpr
                        ? newType
                        : throw TacticException.Failed("introN", mvarId, "There are no additional binders or `let` bindings in the goal to introduce");
                });
                j = fvars.Count;
            }
        });

        Name NameFor(int index, Name binderName)
        {
            if (index < names.Count && names[index] is { IsAnonymous: false } given && given.ToString() != "_")
            {
                return given;
            }
            return binderName.IsAnonymous ? Name.From("a") : binderName;
        }
    }

    /// <summary>Introduces one binder (Lean's <c>MVarId.intro</c>), named <paramref name="name"/> or after the binder.</summary>
    /// <returns>The new hypothesis and the new goal.</returns>
    public (FVarId FVar, MVarId Goal) Intro1(MVarId mvarId, Name? name = null)
    {
        var (fvars, goal) = IntroN(mvarId, 1, name is null ? null : [name]);
        return (fvars[0], goal);
    }
}
