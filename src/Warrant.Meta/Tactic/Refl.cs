using Warrant.Cic;

namespace Warrant.Meta;

public sealed partial class MetaM
{
    /// <summary>
    /// Closes a goal <c>@Eq α a b</c> with <c>@Eq.refl α a</c> when <c>a</c> and <c>b</c> are definitionally equal at the
    /// current transparency (Lean's <c>MVarId.refl</c>, Lean/Meta/Tactic/Refl.lean 25). The goal's type is put in weak
    /// head normal form first.
    /// </summary>
    /// <exception cref="TacticException">The goal is not an equation, or its sides are not definitionally equal.</exception>
    public void Refl(MVarId mvarId) => WithContext(mvarId, () =>
    {
        CheckNotAssigned(mvarId, "refl");
        var targetType = GetMVarTypeWhnf(mvarId);
        if (!targetType.IsAppOf(TacticNames.Eq) || targetType.GetAppNumArgs() != 3)
        {
            throw TacticException.Failed("rfl", mvarId, $"equality expected\n  {Pp(targetType)}");
        }
        var args = targetType.GetAppArgs();
        var lhs = this.InstantiateMVars(args[1]);
        var rhs = this.InstantiateMVars(args[2]);
        if (!IsDefEq(lhs, rhs))
        {
            throw TacticException.Failed("rfl", mvarId, $"equality lhs\n  {Pp(lhs)}\nis not definitionally equal to rhs\n  {Pp(rhs)}");
        }
        var levels = ((ConstExpr)targetType.GetAppFn()).Levels;
        Assign(mvarId, Expr.App(Expr.Const(TacticNames.EqRefl, levels), args[0], lhs));
        return 0;
    });
}
