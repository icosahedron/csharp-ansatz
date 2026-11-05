using Warrant.Cic;
using Warrant.Meta.Omega;

namespace Warrant.Meta;

public sealed partial class MetaM
{
    /// <summary>
    /// <c>false_or_by_contra</c> (Lean's <c>MVarId.falseOrByContra</c>, Lean/Elab/Tactic/FalseOrByContra.lean 39, with
    /// <c>useClassical := none</c>): turns the goal into <c>False</c>, keeping what it says. A goal <c>False</c> stays; an
    /// implication or <c>¬ P</c> has its premise introduced, and the result is turned again; any other proposition
    /// <c>P</c> becomes <c>False</c> under the hypothesis <c>¬ P</c>, by <c>Decidable.byContradiction</c> when a
    /// <c>Decidable P</c> instance is found and by <c>Classical.byContradiction</c> otherwise; a goal that is not a
    /// proposition is closed by <c>False.elim</c> from a new goal <c>False</c>.
    /// </summary>
    /// <param name="mvarId">The goal.</param>
    /// <returns>The goal <c>False</c>.</returns>
    public MVarId? FalseOrByContra(MVarId mvarId)
    {
        var g = mvarId;
        while (true)
        {
            Budget.Tick();
            var gNow = g;
            var ty = WithContext(gNow, () => WhnfR(this.InstantiateMVars(GetMVarType(gNow))));
            if (ty is ConstExpr { Name: var n } && n == OmegaNames.False)
            {
                return g;
            }
            if (ty is ForallExpr || OmegaExprs.AppOf(ty, OmegaNames.Not, 1) is not null)
            {
                g = WithDefault(() => IntroN(gNow, 1)).Goal;
                continue;
            }
            return WithContext(gNow, () =>
            {
                if (IsProp(ty))
                {
                    var target = GetMVarType(gNow);
                    var notTarget = Expr.Forall(Name.Anonymous, Expr.App(Expr.Const(OmegaNames.Not), target), OmegaExprs.False);
                    var inst = TrySynthDecidable(target);
                    var h = MkFreshExprSyntheticOpaqueMVar(notTarget, GetTag(gNow));
                    Assign(gNow, inst is null
                        ? Expr.App(Expr.Const(OmegaNames.ClassicalByContradiction), target, h)
                        : Expr.App(Expr.Const(OmegaNames.DecidableByContradiction), target, inst, h));
                    // Lean's intro1 names the hypothesis inaccessibly (a✝), so it never takes a name the user can write.
                    return IntroN(h.Id, 1, [InaccessibleName]).Goal;
                }
                var falseGoal = MkFreshExprSyntheticOpaqueMVar(OmegaExprs.False, GetTag(gNow));
                Assign(gNow, Expr.App(Expr.Const(OmegaNames.FalseElim, GetLevel(GetMVarType(gNow))), GetMVarType(gNow), falseGoal));
                return falseGoal.Id;
            });
        }
    }

    private static readonly Name InaccessibleName = Name.From("a✝");

    /// <summary>A <c>Decidable p</c> instance, or null if instance synthesis finds none.</summary>
    private Expr? TrySynthDecidable(Expr p)
    {
        try
        {
            return SynthInstance(Expr.App(Expr.Const(OmegaNames.Decidable), p));
        }
        catch (IsDefEqStuckException)
        {
            return null;
        }
    }
}
