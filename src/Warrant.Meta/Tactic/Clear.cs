using Warrant.Cic;

namespace Warrant.Meta;

public sealed partial class MetaM
{
    /// <summary>
    /// Removes the hypothesis <paramref name="fvarId"/> from the goal (Lean's <c>MVarId.clear</c>,
    /// Lean/Meta/Tactic/Clear.lean 19): a new goal with the same type in the context without it, which the old goal is
    /// assigned to.
    /// </summary>
    /// <returns>The new goal.</returns>
    /// <exception cref="TacticException">The variable is unknown, or another hypothesis or the target depends on it.</exception>
    public MVarId Clear(MVarId mvarId, FVarId fvarId) => WithContext(mvarId, () =>
    {
        CheckNotAssigned(mvarId, "clear");
        var lctx = LCtx;
        if (!lctx.Contains(fvarId))
        {
            throw TacticException.Failed("clear", mvarId, $"unknown variable '{Pp(Expr.FVar(fvarId))}'");
        }
        var tag = GetTag(mvarId);
        foreach (var localDecl in lctx.Decls)
        {
            if (localDecl.FVarId != fvarId && this.LocalDeclDependsOn(localDecl, fvarId))
            {
                throw TacticException.Failed("clear", mvarId, $"variable '{Pp(localDecl.ToExpr())}' depends on '{Pp(Expr.FVar(fvarId))}'");
            }
        }
        var mvarDecl = GetMVarDecl(mvarId);
        if (this.DependsOn(mvarDecl.Type, fvarId))
        {
            throw TacticException.Failed("clear", mvarId, $"target depends on '{Pp(Expr.FVar(fvarId))}'");
        }
        var localInsts = LocalInstances;
        for (int i = 0; i < localInsts.Length; i++)
        {
            if (localInsts[i].FVar is FVarExpr f && f.Id == fvarId)
            {
                localInsts = localInsts.RemoveAt(i);
                break;
            }
        }
        var newMVar = MkFreshExprMVarAt(lctx.Erase(fvarId), localInsts, mvarDecl.Type, MetavarKind.SyntheticOpaque, tag);
        Assign(mvarId, newMVar);
        return newMVar.Id;
    });

    /// <summary>
    /// <see cref="Clear"/>, or the goal unchanged when the hypothesis cannot be cleared (Lean's <c>MVarId.tryClear</c>,
    /// Clear.lean 49).
    /// </summary>
    public MVarId TryClear(MVarId mvarId, FVarId fvarId)
    {
        var saved = SaveState();
        try
        {
            return Clear(mvarId, fvarId);
        }
        catch (MetaException ex) when (Combinators.IsRecoverable(ex))
        {
            Restore(saved);
            return mvarId;
        }
    }
}
