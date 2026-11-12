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
    /// Every instance-implicit argument is synthesized with <see cref="SynthInstance"/>, also one unification already
    /// assigned, which must then agree with the instance found (<c>synthAppInstances</c> with Lean's default
    /// <c>synthAssignedInstances := true</c>, Apply.lean 40; M6 U3).
    /// </remarks>
    /// <param name="mvarId">The goal.</param>
    /// <param name="e">The function or lemma to apply.</param>
    /// <param name="term">How messages name <paramref name="e"/>, e.g. <c>'Eq.symm'</c>; null for "the term".</param>
    /// <returns>The new goals.</returns>
    /// <exception cref="TacticException">
    /// No number of arguments makes the types unify, an instance argument has no instance, or the instance found does not
    /// agree with the one unification assigned.
    /// </exception>
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

            SynthAppInstances(mvarId, newMVars, binderInfos);

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

    /// <summary>
    /// Lean's <c>synthAppInstances</c> (Apply.lean 40) with <c>synthAssignedInstances := true</c> and
    /// <c>allowSynthFailures := false</c>: synthesizes every instance-implicit argument and unifies it with the instance
    /// found. An argument whose synthesis fails, or is stuck on a metavariable, is tried again in a further round while
    /// a round makes progress after its first failure, since solving one instance can assign another's out-parameters
    /// (Lean's <c>step</c>); when a round makes none, the first failure is the error.
    /// </summary>
    private void SynthAppInstances(MVarId mvarId, Expr[] newMVars, BinderInfo[] binderInfos)
    {
        var todo = new List<Expr>();
        for (int i = 0; i < newMVars.Length; i++)
        {
            if (binderInfos[i] == BinderInfo.InstImplicit)
            {
                todo.Add(newMVars[i]);
            }
        }
        while (todo.Count > 0)
        {
            Expr? firstFailure = null;
            bool progressAfterFailure = false;
            var postponed = new List<Expr>();
            foreach (var mvar in todo)
            {
                var mvarType = InferType(mvar);
                Expr? val;
                try
                {
                    val = SynthInstance(mvarType);
                }
                catch (IsDefEqStuckException)
                {
                    val = null;
                }
                if (val is null)
                {
                    firstFailure ??= mvarType;
                    postponed.Add(mvar);
                    continue;
                }
                if (postponed.Count > 0)
                {
                    progressAfterFailure = true;
                }
                if (!IsDefEq(mvar, val))
                {
                    throw TacticException.Failed("apply", mvarId, "failed to assign synthesized instance");
                }
            }
            if (firstFailure is null)
            {
                return;
            }
            if (!progressAfterFailure)
            {
                throw TacticException.Failed("apply", mvarId, $"failed to synthesize\n  {Pp(this.InstantiateMVars(firstFailure))}");
            }
            todo = postponed;
        }
    }

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
