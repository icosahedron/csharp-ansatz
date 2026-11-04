using Warrant.Cic;
using Warrant.Kernel;

namespace Warrant.Meta;

/// <summary>What <see cref="MetaM.SimpGoal"/> left: the goal and the hypotheses it simplified.</summary>
/// <param name="FVarIds">The simplified hypotheses, in the order given.</param>
/// <param name="Goal">The new goal.</param>
public sealed record SimpGoalResult(IReadOnlyList<FVarId> FVarIds, MVarId Goal);

// Lean/Meta/Tactic/Simp/Main.lean and Types.lean: applying a simp result to a goal's target or to a
// hypothesis, simpGoal, and `simp at *`; Lean/Meta/Tactic/Replace.lean and Assert.lean for the goal
// operations they need.
public sealed partial class MetaM
{
    /// <summary>
    /// Simplifies the target of <paramref name="mvarId"/> (Lean's <c>simpTarget</c>): a target that becomes <c>True</c>
    /// closes the goal with <c>of_eq_true</c>; otherwise the goal is replaced through <c>Eq.mpr</c>.
    /// </summary>
    /// <returns>The new goal, or null when the goal was closed.</returns>
    public MVarId? SimpTarget(MVarId mvarId, SimpContext context, bool mayCloseGoal = true)
    {
        ArgumentNullException.ThrowIfNull(context);
        return WithContext(mvarId, () =>
        {
            CheckNotAssigned(mvarId, "simp");
            var target = this.InstantiateMVars(GetMVarType(mvarId));
            var r = new Simplifier(this, context).Run(target);
            if (mayCloseGoal && r.Expr.IsConstOf(SimpNames.True))
            {
                Assign(mvarId, r.Proof is { } proof ? MkOfEqTrue(proof) : Expr.Const(SimpNames.TrueIntro));
                return (MVarId?)null;
            }
            return ApplySimpResultToTarget(mvarId, target, r);
        });
    }

    /// <summary>The goal with target <c>r.Expr</c> (Lean's <c>applySimpResultToTarget</c>).</summary>
    public MVarId ApplySimpResultToTarget(MVarId mvarId, Expr target, SimpResult r)
    {
        ArgumentNullException.ThrowIfNull(r);
        return r.Proof is { } proof ? ReplaceTargetEq(mvarId, r.Expr, proof)
            : target != r.Expr ? ReplaceTargetDefEq(mvarId, r.Expr)
            : mvarId;
    }

    /// <summary>
    /// Replaces the goal by one of type <paramref name="targetNew"/>, given <c>eqProof : target = targetNew</c>, through
    /// <c>Eq.mpr</c> (Lean's <c>MVarId.replaceTargetEq</c>).
    /// </summary>
    public MVarId ReplaceTargetEq(MVarId mvarId, Expr targetNew, Expr eqProof) => WithContext(mvarId, () =>
    {
        CheckNotAssigned(mvarId, "replaceTarget");
        var mvarNew = MkFreshExprSyntheticOpaqueMVar(targetNew, GetTag(mvarId));
        var target = GetMVarType(mvarId);
        var u = GetLevel(target);
        var eq = MkEq(target, targetNew);
        Assign(mvarId, Expr.App(Expr.Const(SimpNames.EqMpr, u), target, targetNew, MkExpectedPropHint(eqProof, eq), mvarNew));
        return mvarNew.Id;
    });

    /// <summary>
    /// Replaces the type of the hypothesis <paramref name="fvarId"/> by the definitionally equal <paramref name="typeNew"/>
    /// (Lean's <c>MVarId.replaceLocalDeclDefEq</c>).
    /// </summary>
    public MVarId ReplaceLocalDeclDefEq(MVarId mvarId, FVarId fvarId, Expr typeNew) => WithContext(mvarId, () =>
    {
        if (typeNew == GetLocalDecl(fvarId).Type)
        {
            return mvarId;
        }
        var decl = GetMVarDecl(mvarId);
        var mvarNew = MkFreshExprMVarAt(decl.LCtx.SetType(fvarId, typeNew), decl.LocalInstances, decl.Type, MetavarKind.SyntheticOpaque, decl.UserName);
        Assign(mvarId, mvarNew);
        return mvarNew.Id;
    });

    /// <summary>
    /// Adds the hypotheses <paramref name="hyps"/>, each a name, type and proof, to the goal (Lean's
    /// <c>MVarId.assertHypotheses</c>).
    /// </summary>
    public (FVarId[] FVarIds, MVarId Goal) AssertHypotheses(MVarId mvarId, IReadOnlyList<(Name UserName, Expr Type, Expr Value)> hyps)
    {
        ArgumentNullException.ThrowIfNull(hyps);
        if (hyps.Count == 0)
        {
            return ([], mvarId);
        }
        return WithContext(mvarId, () =>
        {
            CheckNotAssigned(mvarId, "assertHypotheses");
            var target = GetMVarType(mvarId);
            var targetNew = target;
            for (int i = hyps.Count - 1; i >= 0; i--)
            {
                targetNew = Expr.Forall(hyps[i].UserName, hyps[i].Type, targetNew);
            }
            var mvarNew = MkFreshExprSyntheticOpaqueMVar(targetNew, GetTag(mvarId));
            Assign(mvarId, ExprExtensions.MkAppN(mvarNew, [.. hyps.Select(h => h.Value)]));
            return IntroN(mvarNew.Id, hyps.Count, [.. hyps.Select(h => h.UserName)]);
        });
    }

    /// <summary>
    /// Simplifies the hypotheses <paramref name="fvarIdsToSimp"/> and, with <paramref name="simplifyTarget"/>, the
    /// target (Lean's <c>simpGoal</c>). A hypothesis that becomes <c>False</c> closes the goal; one that changes is
    /// replaced by its simplified form, proved with <c>Eq.mp</c>.
    /// </summary>
    /// <returns>The new goal and the simplified hypotheses, or null when the goal was closed.</returns>
    /// <exception cref="TacticException">With <see cref="SimpConfig.FailIfUnchanged"/>, nothing changed.</exception>
    public SimpGoalResult? SimpGoal(MVarId mvarId, SimpContext context, bool simplifyTarget = true, IReadOnlyList<FVarId>? fvarIdsToSimp = null)
    {
        ArgumentNullException.ThrowIfNull(context);
        fvarIdsToSimp ??= [];
        return WithContext(mvarId, () =>
        {
            CheckNotAssigned(mvarId, "simp");
            var mvarIdNew = mvarId;
            var toAssert = new List<(Name, Expr, Expr)>();
            var replaced = new List<FVarId>();
            foreach (var fvarId in fvarIdsToSimp)
            {
                var decl = GetLocalDecl(fvarId);
                var type = this.InstantiateMVars(decl.Type);
                var r = new Simplifier(this, context).Run(type);
                if (r.Proof is not null)
                {
                    if (ApplySimpResult(mvarIdNew, decl.ToExpr(), type, r) is not { } applied)
                    {
                        return null;
                    }
                    toAssert.Add((decl.UserName, applied.Type, applied.Value));
                }
                else
                {
                    if (r.Expr.IsConstOf(SimpNames.False))
                    {
                        Assign(mvarIdNew, MkFalseElim(GetMVarType(mvarIdNew), decl.ToExpr()));
                        return null;
                    }
                    mvarIdNew = ReplaceLocalDeclDefEq(mvarIdNew, fvarId, r.Expr);
                    replaced.Add(fvarId);
                }
            }
            if (simplifyTarget)
            {
                if (SimpTarget(mvarIdNew, context) is not { } next)
                {
                    return null;
                }
                mvarIdNew = next;
            }
            var (fvarIdsNew, asserted) = AssertHypotheses(mvarIdNew, toAssert);
            mvarIdNew = asserted;
            foreach (var fvarId in fvarIdsToSimp.Where(f => !replaced.Contains(f)).Reverse())
            {
                mvarIdNew = TryClear(mvarIdNew, fvarId);
            }
            if (context.Config.FailIfUnchanged && mvarId == mvarIdNew)
            {
                throw new TacticException("simp", mvarId, "`simp` made no progress");
            }
            return new SimpGoalResult(fvarIdsNew, mvarIdNew);
        });
    }

    /// <summary>
    /// <c>simp at *</c>: simplifies every hypothesis that is a proposition no other hypothesis depends on, then the
    /// target (Lean's <c>simpLocation</c> with a wildcard, through <c>getNondepPropHyps</c>). The omega-prep step uses
    /// it (U18).
    /// </summary>
    /// <returns>The new goal, or null when the goal was closed.</returns>
    public SimpGoalResult? SimpAll(MVarId mvarId, SimpContext context)
    {
        ArgumentNullException.ThrowIfNull(context);
        var hyps = WithContext(mvarId, () => GetNondepPropHyps(mvarId));
        return SimpGoal(mvarId, context, simplifyTarget: true, hyps);
    }

    // Lean's getNondepPropHyps: propositions in the context that no other hypothesis mentions.
    private List<FVarId> GetNondepPropHyps(MVarId mvarId)
    {
        var decls = GetMVarDecl(mvarId).LCtx.Decls.Where(d => !d.IsImplementationDetail).ToList();
        var result = new List<FVarId>();
        foreach (var d in decls)
        {
            if (!IsProp(d.Type))
            {
                continue;
            }
            bool mentioned = decls.Any(o => o.FVarId != d.FVarId
                && (Mentions(o.Type, d.FVarId) || (o is LDecl l && Mentions(l.Value, d.FVarId))));
            if (!mentioned)
            {
                result.Add(d.FVarId);
            }
        }
        return result;

        static bool Mentions(Expr e, FVarId x) => e.HasFVar && ExprOps.Find(e, (y, _) => y is FVarExpr f && f.Id == x) is not null;
    }

    // Lean's applySimpResult: the hypothesis `val : type` as a proof of `r.Expr`, or the goal closed by False.
    private (Expr Value, Expr Type)? ApplySimpResult(MVarId mvarId, Expr val, Expr type, SimpResult r)
    {
        if (r.Expr.IsConstOf(SimpNames.False))
        {
            var target = GetMVarType(mvarId);
            Assign(mvarId, MkFalseElim(target, r.Proof is { } eqProof
                ? Expr.App(Expr.Const(SimpNames.EqMp, Level.Zero), type, r.Expr, eqProof, val)
                : val));
            return null;
        }
        if (r.Proof is { } proof)
        {
            return (Expr.App(Expr.Const(SimpNames.EqMp, GetLevel(type)), type, r.Expr, proof, val), r.Expr);
        }
        return r.Expr != type ? (MkExpectedTypeHint(val, r.Expr), r.Expr) : (val, r.Expr);
    }
}
