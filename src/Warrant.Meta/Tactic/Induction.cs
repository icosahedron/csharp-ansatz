using System.Collections.Immutable;
using Warrant.Cic;
using Warrant.Kernel;

namespace Warrant.Meta;

/// <summary>
/// One goal <c>induction</c> leaves (Lean's <c>InductionSubgoal</c>, Lean/Meta/Tactic/Induction.lean 46): the goal, the
/// hypotheses it introduced for the constructor's fields, and what the old goal's hypotheses became in it.
/// </summary>
/// <param name="MVarId">The goal.</param>
/// <param name="Fields">The new hypotheses for the fields (and induction hypotheses) of the minor premise.</param>
/// <param name="Subst">The major premise, its indices and the reverted hypotheses, mapped to their replacements.</param>
public sealed record InductionSubgoal(MVarId MVarId, ImmutableArray<Expr> Fields, FVarSubst Subst);

public sealed partial class MetaM
{
    /// <summary>
    /// Eliminates the hypothesis <paramref name="majorFVarId"/> with <paramref name="recursorName"/>, <c>T.rec</c> or an
    /// auxiliary recursor such as <c>T.casesOn</c> (Lean's <c>MVarId.induction</c>, Induction.lean 203): reverts the major
    /// premise's indices, the major premise and what depends on them, introduces the indices and the major premise again,
    /// applies the recursor with the motive abstracted from the target, and makes one goal per minor premise with its
    /// fields, induction hypotheses and the reverted hypotheses introduced. The minor premises' binder names name the goals
    /// (<c>case zero</c>, <c>case succ</c>) and their fields' binder names the new hypotheses; Warrant keeps them as they
    /// are where Lean would make them inaccessible, so goals stay readable.
    /// </summary>
    /// <param name="mvarId">The goal.</param>
    /// <param name="majorFVarId">The hypothesis to eliminate.</param>
    /// <param name="recursorName">The eliminator.</param>
    /// <returns>The new goals, one per minor premise.</returns>
    /// <exception cref="TacticException">The goal or hypothesis does not fit the eliminator.</exception>
    public IReadOnlyList<InductionSubgoal> Induction(MVarId mvarId, FVarId majorFVarId, Name recursorName)
    {
        ArgumentNullException.ThrowIfNull(recursorName);
        return WithContext(mvarId, () =>
        {
            CheckNotAssigned(mvarId, "induction");
            RefuseUnassignedMVars("induction", mvarId);
            var majorLocalDecl = GetLocalDecl(majorFVarId);
            var recursorInfo = MkRecursorInfo(recursorName);
            var majorType = WhnfUntil(majorLocalDecl.Type, recursorInfo.TypeName)
                ?? throw UnexpectedMajorType("induction", mvarId, majorLocalDecl.Type);
            var majorTypeArgs = majorType.GetAppArgs();
            foreach (var paramPos in recursorInfo.ParamsPos)
            {
                if (paramPos is { } p && p >= majorTypeArgs.Length)
                {
                    throw TacticException.Failed("induction", mvarId, $"major premise type is ill-formed\n  {Pp(majorType)}");
                }
            }
            var indices = GetMajorTypeIndices(mvarId, "induction", recursorInfo, majorType);
            var target = GetMVarType(mvarId);
            if (!recursorInfo.DepElim && this.DependsOn(target, majorFVarId))
            {
                throw TacticException.Failed("induction", mvarId, $"recursor '{PpConst(recursorName)}' does not support dependent elimination, but conclusion depends on major premise");
            }
            // Revert the indices and the major premise, preserving their order, and introduce them again.
            var (reverted, goal) = Revert(mvarId, [.. indices.Select(i => ((FVarExpr)i).Id), majorFVarId], preserveOrder: true);
            (var newIndices, goal) = IntroN(goal, indices.Length);
            (var newMajor, goal) = Intro1(goal);
            var baseSubst = FVarSubst.Empty.Insert(majorFVarId, Expr.FVar(newMajor));
            for (int i = 0; i < indices.Length; i++)
            {
                baseSubst = baseSubst.Insert(((FVarExpr)indices[i]).Id, Expr.FVar(newIndices[i]));
            }
            Expr[] indexFVars = [.. newIndices.Select(i => (Expr)Expr.FVar(i))];
            var major = Expr.FVar(newMajor);
            var g = goal;
            return WithContext(g, () =>
            {
                var recursor = MkRecursorAppPrefix(g, "induction", newMajor, recursorInfo, indexFVars);
                return Finalize(g, recursorInfo, reverted, major, indexFVars, baseSubst, recursor);
            });
        });
    }

    /// <summary>
    /// Fails if the goal's target or a hypothesis has a metavariable that is not assigned. <c>cases</c> and
    /// <c>induction</c> revert hypotheses into the target and abstract it into a motive; Warrant refuses rather than
    /// build a motive over a hole (Ansatz did the same).
    /// </summary>
    private void RefuseUnassignedMVars(string tactic, MVarId mvarId)
    {
        if (this.InstantiateMVars(GetMVarType(mvarId)).HasExprMVar
            || LCtx.Decls.Any(d => this.InstantiateMVars(d.Type).HasExprMVar || (d.GetValue(allowNondep: true) is { } v && this.InstantiateMVars(v).HasExprMVar)))
        {
            throw TacticException.Failed(tactic, mvarId, "the goal has metavariables that are not assigned yet");
        }
    }

    private TacticException UnexpectedMajorType(string tactic, MVarId mvarId, Expr majorType) =>
        TacticException.Failed(tactic, mvarId, $"unexpected major premise type\n  {Pp(majorType)}");

    /// <summary>
    /// The indices of the major premise's type, each of which must be a distinct free variable that the arguments before it
    /// do not mention (Lean's <c>getMajorTypeIndices</c>, Induction.lean 136).
    /// </summary>
    private Expr[] GetMajorTypeIndices(MVarId mvarId, string tactic, MetaRecursorInfo recursorInfo, Expr majorType)
    {
        var majorTypeArgs = majorType.GetAppArgs();
        return [.. recursorInfo.IndicesPos.Select(idxPos =>
        {
            if (idxPos >= majorTypeArgs.Length)
            {
                throw TacticException.Failed(tactic, mvarId, $"major premise type is ill-formed\n  {Pp(majorType)}");
            }
            var idx = majorTypeArgs[idxPos];
            if (idx is not FVarExpr idxFVar)
            {
                throw TacticException.Failed(tactic, mvarId, $"major premise type index {Pp(idx)} is not a variable\n  {Pp(majorType)}");
            }
            for (int i = 0; i < majorTypeArgs.Length; i++)
            {
                var arg = majorTypeArgs[i];
                if (i != idxPos && arg == idx)
                {
                    throw TacticException.Failed(tactic, mvarId, $"'{Pp(idx)}' is an index in major premise, but it occurs more than once\n  {Pp(majorType)}");
                }
                if (i < idxPos && this.DependsOn(arg, idxFVar.Id))
                {
                    throw TacticException.Failed(tactic, mvarId, $"'{Pp(idx)}' is an index in major premise, but it occurs in previous arguments\n  {Pp(majorType)}");
                }
                if (i > idxPos && recursorInfo.IndicesPos.Contains(i) && arg is FVarExpr argFVar
                    && this.LocalDeclDependsOn(GetLocalDecl(idxFVar.Id), argFVar.Id))
                {
                    throw TacticException.Failed(tactic, mvarId, $"'{Pp(idx)}' is an index in major premise, but it depends on index occurring at position #{i + 1}");
                }
            }
            return idx;
        })];
    }

    /// <summary>
    /// The recursor applied to the parameters and the motive, <c>fun indices x => target</c> (Lean's
    /// <c>mkRecursorAppPrefix</c>, Induction.lean 166).
    /// </summary>
    private Expr MkRecursorAppPrefix(MVarId mvarId, string tactic, FVarId majorFVarId, MetaRecursorInfo recursorInfo, Expr[] indices)
    {
        var major = Expr.FVar(majorFVarId);
        var target = GetMVarType(mvarId);
        var targetLevel = LevelOps.Normalize(this.InstantiateLevelMVars(GetLevel(target)));
        var majorLocalDecl = GetLocalDecl(majorFVarId);
        var majorType = WhnfUntil(majorLocalDecl.Type, recursorInfo.TypeName)
            ?? throw UnexpectedMajorType(tactic, mvarId, majorLocalDecl.Type);
        if (majorType.GetAppFn() is not ConstExpr { Levels: var majorTypeFnLevels })
        {
            throw TacticException.Failed(tactic, mvarId, "major premise is not of the form (C ...)");
        }
        var recursorLevels = new List<Level>();
        bool foundTargetLevel = false;
        foreach (var univPos in recursorInfo.UnivLevelPos)
        {
            if (univPos.MajorTypeIndex is not { } idx)
            {
                recursorLevels.Add(targetLevel);
                foundTargetLevel = true;
            }
            else if (idx >= majorTypeFnLevels.Count)
            {
                throw TacticException.Failed(tactic, mvarId, "ill-formed recursor");
            }
            else
            {
                recursorLevels.Add(majorTypeFnLevels[idx]);
            }
        }
        if (!foundTargetLevel && targetLevel.Kind != LevelKind.Zero)
        {
            throw TacticException.Failed(tactic, mvarId, $"recursor `{PpConst(recursorInfo.RecursorName)}` can only eliminate into `Prop`");
        }
        Expr recursor = Expr.Const(recursorInfo.RecursorName, recursorLevels.ToEquatableArray());
        recursor = AddRecParams(mvarId, majorType.GetAppArgs(), recursorInfo.ParamsPos, recursor);
        var motive = target;
        if (recursorInfo.DepElim)
        {
            motive = Expr.Lam(Name.From("x"), InferType(major), AbstractM(motive, [major]));
        }
        motive = MkLambdaFVars(indices, motive);
        return Expr.App(recursor, motive);
    }

    /// <summary>The recursor applied to its parameters, an instance-implicit one synthesized (Lean's <c>addRecParams</c>, Induction.lean 23).</summary>
    private Expr AddRecParams(MVarId mvarId, Expr[] majorTypeArgs, ImmutableArray<int?> paramsPos, Expr recursor)
    {
        foreach (var pos in paramsPos)
        {
            if (pos is { } p)
            {
                recursor = p < majorTypeArgs.Length ? Expr.App(recursor, majorTypeArgs[p]) : throw TacticException.Failed("induction", mvarId, "ill-formed recursor");
                continue;
            }
            if (WhnfForall(InferType(recursor)) is not ForallExpr f)
            {
                throw TacticException.Failed("induction", mvarId, "ill-formed recursor");
            }
            Expr? param;
            try
            {
                param = SynthInstance(f.BinderType);
            }
            catch (MetaException ex) when (Combinators.IsRecoverable(ex))
            {
                param = null;
            }
            recursor = Expr.App(recursor, param ?? throw TacticException.Failed("induction", mvarId, "failed to generate type class instance parameter"));
        }
        return recursor;
    }

    /// <summary>
    /// Applies the recursor to the indices, the major premise and a new goal per minor premise, assigns the goal, and
    /// introduces each new goal's fields and reverted hypotheses (Lean's <c>finalize</c>, Induction.lean 57).
    /// </summary>
    private List<InductionSubgoal> Finalize(
        MVarId mvarId, MetaRecursorInfo recursorInfo, FVarId[] reverted, Expr major, Expr[] indices, FVarSubst baseSubst, Expr recursor)
    {
        var target = GetMVarType(mvarId);
        int initialArity = GetTargetArity(target);
        var recursorType = InferType(recursor);
        int numMinors = recursorInfo.ProduceMotive.Length;
        int pos = recursorInfo.NumParams + 1;
        int minorIdx = 0;
        bool consumedMajor = false;
        var subgoals = new List<InductionSubgoal>();
        while (true)
        {
            Budget.Tick();
            recursorType = WhnfForall(recursorType);
            if (recursorType is not ForallExpr f || pos >= recursorInfo.NumArgs)
            {
                if (!consumedMajor)
                {
                    throw TacticException.Failed("induction", mvarId, "ill-formed recursor");
                }
                Assign(mvarId, recursor);
                return subgoals;
            }
            if (pos == recursorInfo.FirstIndexPos)
            {
                foreach (var index in indices)
                {
                    recursor = Expr.App(recursor, index);
                    recursorType = GetTypeBody(mvarId, recursorType, index);
                }
                recursor = Expr.App(recursor, major);
                recursorType = GetTypeBody(mvarId, recursorType, major);
                consumedMajor = true;
                pos += 1 + indices.Length;
                continue;
            }
            var tag = GetTag(mvarId);
            if (minorIdx >= numMinors)
            {
                throw TacticException.Failed("induction", mvarId, "ill-formed recursor");
            }
            var d = f.BinderType.HeadBeta();
            var minorTag = numMinors == 1 ? tag : AppendTag(tag, f.BinderName);
            if (f.BinderInfo == BinderInfo.InstImplicit)
            {
                Expr? inst;
                try
                {
                    inst = SynthInstance(d);
                }
                catch (MetaException ex) when (Combinators.IsRecoverable(ex))
                {
                    inst = null;
                }
                if (inst is not null)
                {
                    recursor = Expr.App(recursor, inst);
                    recursorType = GetTypeBody(mvarId, recursorType, inst);
                }
                else
                {
                    // A goal for the instance when synthesis fails.
                    var instMVar = MkFreshExprSyntheticOpaqueMVar(d, minorTag);
                    recursor = Expr.App(recursor, instMVar);
                    recursorType = GetTypeBody(mvarId, recursorType, instMVar);
                    subgoals.Add(new InductionSubgoal(instMVar.Id, [], FVarSubst.Empty));
                }
            }
            else
            {
                int arity = GetTargetArity(d);
                if (arity < initialArity)
                {
                    throw TacticException.Failed("induction", mvarId, "ill-formed recursor");
                }
                int nparams = arity - initialArity; // the minor premise's fields and induction hypotheses
                int nextra = reverted.Length - indices.Length - 1; // the reverted hypotheses that depend on the major premise
                var mvar = MkFreshExprSyntheticOpaqueMVar(d, minorTag);
                recursor = Expr.App(recursor, mvar);
                recursorType = GetTypeBody(mvarId, recursorType, mvar);
                var newGoal = TryClear(mvar.Id, ((FVarExpr)major).Id);
                (var fields, newGoal) = IntroN(newGoal, nparams);
                (var extra, newGoal) = IntroN(newGoal, nextra);
                var subst = baseSubst;
                for (int i = indices.Length + 1; i < reverted.Length; i++)
                {
                    subst = subst.Insert(reverted[i], Expr.FVar(extra[i - indices.Length - 1]));
                }
                subgoals.Add(new InductionSubgoal(newGoal, [.. fields.Select(x => (Expr)Expr.FVar(x))], subst));
            }
            pos++;
            minorIdx++;
        }
    }

    private Expr GetTypeBody(MVarId mvarId, Expr type, Expr x) =>
        WhnfForall(type) is ForallExpr f ? ExprOps.Instantiate(f.Body, x) : throw TacticException.Failed("induction", mvarId, "ill-formed recursor");

    /// <summary>The number of <c>∀</c> binders of <paramref name="e"/>, through metadata and head beta-redexes (Lean's <c>getTargetArity</c>).</summary>
    private static int GetTargetArity(Expr e)
    {
        int arity = 0;
        while (true)
        {
            switch (e)
            {
                case MDataExpr m:
                    e = m.Expr;
                    continue;
                case ForallExpr f:
                    arity++;
                    e = f.Body;
                    continue;
            }
            if (e.IsHeadBetaTarget())
            {
                e = e.HeadBeta();
                continue;
            }
            return arity;
        }
    }

    /// <summary><paramref name="e"/> in weak head normal form if that is a <c>∀</c>, else unchanged (Lean's <c>whnfForall</c>).</summary>
    public Expr WhnfForall(Expr e)
    {
        var r = Whnf(e);
        return r is ForallExpr ? r : e;
    }
}
