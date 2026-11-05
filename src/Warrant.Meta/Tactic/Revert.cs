using Warrant.Cic;

namespace Warrant.Meta;

public sealed partial class MetaM
{
    /// <summary>
    /// Moves the hypotheses <paramref name="fvarIds"/>, and every hypothesis that depends on them, back into the goal as
    /// <c>∀</c> binders (Lean's <c>MVarId.revert</c>, Lean/Meta/Tactic/Revert.lean 19): assigns <c>?g := ?g' xs</c> for a
    /// new goal <c>?g' : ∀ xs, target</c> with the old goal's tag.
    /// </summary>
    /// <param name="mvarId">The goal.</param>
    /// <param name="fvarIds">The hypotheses to revert.</param>
    /// <param name="preserveOrder">Keep the reverted hypotheses in context order, failing if that is impossible.</param>
    /// <param name="clearAuxDeclsInsteadOfRevert">Clear an auxiliary declaration among <paramref name="fvarIds"/> instead of failing.</param>
    /// <returns>The reverted hypotheses, in binder order, and the new goal.</returns>
    /// <exception cref="TacticException">A hypothesis is an auxiliary declaration.</exception>
    public (FVarId[] Reverted, MVarId Goal) Revert(MVarId mvarId, IReadOnlyList<FVarId> fvarIds, bool preserveOrder = false, bool clearAuxDeclsInsteadOfRevert = false)
    {
        ArgumentNullException.ThrowIfNull(fvarIds);
        if (fvarIds.Count == 0)
        {
            return ([], mvarId);
        }
        return WithContext(mvarId, () =>
        {
            CheckNotAssigned(mvarId, "revert");
            if (!clearAuxDeclsInsteadOfRevert)
            {
                foreach (var fvarId in fvarIds)
                {
                    if (GetLocalDecl(fvarId).IsAuxDecl)
                    {
                        throw new TacticException("revert", mvarId, $"Failed to revert `{Pp(Expr.FVar(fvarId))}`: It is an auxiliary declaration created to represent a recursive reference to an in-progress definition");
                    }
                }
            }
            var toRevert = CollectForwardDeps([.. fvarIds.Select(f => (Expr)Expr.FVar(f))], preserveOrder);
            var goal = mvarId;
            var toRevertNew = new List<Expr>();
            foreach (var x in toRevert)
            {
                var id = ((FVarExpr)x).Id;
                if (GetLocalDecl(id).IsAuxDecl)
                {
                    goal = Clear(goal, id);
                }
                else
                {
                    toRevertNew.Add(x);
                }
            }
            var tag = GetTag(goal);
            // A natural metavariable, so that MetavarContext.revert assigns it.
            SetMVarKind(goal, MetavarKind.Natural);
            Expr e;
            Expr[] reverted;
            try
            {
                (e, reverted) = RevertCore(toRevertNew, goal, preserveOrder);
            }
            finally
            {
                SetMVarKind(goal, MetavarKind.SyntheticOpaque);
            }
            var newGoal = ((MVarExpr)e.GetAppFn()).Id;
            SetMVarKind(newGoal, MetavarKind.SyntheticOpaque);
            SetTag(newGoal, tag);
            return (reverted.Select(r => ((FVarExpr)r).Id).ToArray(), newGoal);
        });
    }
}
