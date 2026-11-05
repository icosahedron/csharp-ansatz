using Warrant.Cic;

namespace Warrant.Meta;

public sealed partial class MetaM
{
    /// <summary>
    /// The number of binders of <paramref name="e"/> after reduction, and whether its conclusion is headed by a
    /// metavariable (Lean's <c>getExpectedNumArgsAux</c>, Lean/Meta/Tactic/Apply.lean 21).
    /// </summary>
    public (int NumArgs, bool HasMVarHead) GetExpectedNumArgsAux(Expr e) =>
        WithDefault(() => ForallTelescopeReducing(e, (xs, body) => (xs.Length, body.GetAppFn() is MVarExpr)));

    /// <summary>
    /// <c>apply e</c> (Lean's <c>MVarId.apply</c>, Apply.lean 169 with the default <c>ApplyConfig</c>): tries
    /// <c>e ?a₁ … ?aᵢ</c> for increasing <c>i</c> until its type unifies with the goal's (with first-order and
    /// quasi-pattern approximation), assigns the goal, and returns the arguments unification did not assign as new goals,
    /// those no other new goal's type mentions first (<c>ApplyNewGoals.nonDependentFirst</c>).
    /// </summary>
    /// <remarks>
    /// Lean synthesizes every instance-implicit argument (<c>synthAppInstances</c>, Apply.lean 40). Until instance
    /// synthesis exists (U16), an instance argument that unification leaves unassigned fails the tactic with a message
    /// saying so, and one it assigned is left to the kernel's check of the whole proof.
    /// </remarks>
    /// <param name="mvarId">The goal.</param>
    /// <param name="e">The function or lemma to apply.</param>
    /// <param name="term">How messages name <paramref name="e"/>, e.g. <c>'Eq.symm'</c>; null for "the term".</param>
    /// <returns>The new goals.</returns>
    /// <exception cref="TacticException">No number of arguments makes the types unify, or an instance stays unassigned.</exception>
    public IReadOnlyList<MVarId> Apply(MVarId mvarId, Expr e, string? term = null)
    {
        ArgumentNullException.ThrowIfNull(e);
        return WithContext(mvarId, () =>
        {
            CheckNotAssigned(mvarId, "apply");
            var targetType = GetMVarType(mvarId);
            var eType = InferType(e);
            var (numArgs, hasMVarHead) = GetExpectedNumArgsAux(eType);
            int lower = hasMVarHead ? numArgs : Math.Max(0, numArgs - GetExpectedNumArgsAux(targetType).NumArgs);
            int upper = numArgs + 1;

            Expr[]? newMVars = null;
            BinderInfo[]? binderInfos = null;
            for (int i = lower; i < upper; i++)
            {
                var saved = SaveState();
                var (mvars, bis, conclusion) = ForallMetaTelescopeReducing(eType, i);
                if (ApproxDefEq(() => IsDefEqGuarded(conclusion, targetType)))
                {
                    (newMVars, binderInfos) = (mvars, bis);
                    break;
                }
                Restore(saved);
            }
            if (newMVars is null || binderInfos is null)
            {
                throw ApplyError(mvarId, eType, lower == 0 ? null : ForallMetaTelescopeReducing(eType, lower).Type, targetType, term);
            }

            // synthAppInstances, without synthesis (see remarks).
            for (int i = 0; i < newMVars.Length; i++)
            {
                if (binderInfos[i] == BinderInfo.InstImplicit && !MCtx.IsAssigned(((MVarExpr)newMVars[i]).Id))
                {
                    throw TacticException.Failed("apply", mvarId, $"failed to synthesize instance\n  {Pp(InferType(newMVars[i]))}\ninstance synthesis is not available yet, so an instance argument must be determined by the goal");
                }
            }

            var f = this.InstantiateMVars(e);
            Assign(mvarId, ExprExtensions.MkAppN(f, newMVars));
            var unassigned = new List<Expr>();
            var unassignedInfos = new List<BinderInfo>();
            for (int i = 0; i < newMVars.Length; i++)
            {
                if (!MCtx.IsAssigned(((MVarExpr)newMVars[i]).Id))
                {
                    unassigned.Add(newMVars[i]);
                    unassignedInfos.Add(binderInfos[i]);
                }
            }
            AppendParentTag(mvarId, unassigned, unassignedInfos);
            var newIds = ReorderGoals(unassigned);
            var result = newIds.Concat(this.GetMVarsNoDelayed(f).Where(id => !newIds.Contains(id))).ToList();
            foreach (var id in result)
            {
                HeadBetaType(id);
            }
            return (IReadOnlyList<MVarId>)result;
        });
    }

    /// <summary><see cref="Apply"/> of a constant at fresh universe metavariables (Lean's <c>MVarId.applyConst</c>, Apply.lean 234).</summary>
    public IReadOnlyList<MVarId> ApplyConst(MVarId mvarId, Name c) => Apply(mvarId, MkConstWithFreshMVarLevels(c), $"'{PpConst(c)}'");

    /// <summary>Lean's <c>throwApplyError</c> (Apply.lean 29).</summary>
    private TacticException ApplyError(MVarId mvarId, Expr eType, Expr? conclusionType, Expr targetType, string? term)
    {
        var what = term ?? "the term";
        var message = $"could not unify the {(conclusionType is null ? "type" : "conclusion")} of {what}\n  {Pp(conclusionType ?? eType)}\nwith the goal\n  {Pp(targetType)}";
        if (conclusionType is not null)
        {
            message += $"\n\nNote: The full type of {what} is\n  {Pp(eType)}";
        }
        return TacticException.Failed("apply", mvarId, message);
    }

    /// <summary>
    /// Gives the new goals the parent goal's tag: a single goal inherits it, several get it as a prefix (Lean's
    /// <c>appendParentTag</c>, Apply.lean 108).
    /// </summary>
    private void AppendParentTag(MVarId mvarId, List<Expr> newMVars, List<BinderInfo> binderInfos)
    {
        var parentTag = GetTag(mvarId);
        if (newMVars.Count == 1)
        {
            SetTag(((MVarExpr)newMVars[0]).Id, parentTag);
            return;
        }
        if (parentTag.IsAnonymous)
        {
            return;
        }
        for (int i = 0; i < newMVars.Count; i++)
        {
            var id = ((MVarExpr)newMVars[i]).Id;
            if (!MCtx.IsAssigned(id) && binderInfos[i] != BinderInfo.InstImplicit)
            {
                SetTag(id, AppendTag(parentTag, GetTag(id)));
            }
        }
    }

    /// <summary>Lean's <c>appendTag</c>: the parent's tag followed by the child's components.</summary>
    private static Name AppendTag(Name parent, Name child)
    {
        if (child.IsAnonymous)
        {
            return parent;
        }
        var components = new Stack<string>();
        for (var n = child; n is { IsAnonymous: false }; n = n.Prefix)
        {
            components.Push(n.StringComponent);
        }
        var result = parent;
        while (components.Count > 0)
        {
            result = result.Append(components.Pop());
        }
        return result;
    }

    /// <summary>Lean's <c>reorderGoals</c> with <c>nonDependentFirst</c> (Apply.lean 140-153).</summary>
    private List<MVarId> ReorderGoals(List<Expr> mvars)
    {
        var nonDeps = new List<MVarId>();
        var deps = new List<MVarId>();
        foreach (var mvar in mvars)
        {
            var id = ((MVarExpr)mvar).Id;
            bool dependedOn = mvars.Any(other => other != mvar && InferType(other) is { HasExprMVar: true } otherType
                && CollectMVars.Collect(otherType, new CollectMVarsState()).Result.Contains(id));
            (dependedOn ? deps : nonDeps).Add(id);
        }
        return [.. nonDeps, .. deps];
    }
}
