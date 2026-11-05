using System.Collections.Immutable;
using Warrant.Cic;

namespace Warrant.Meta;

/// <summary>
/// A tactic could not make progress on its goal (Lean's <c>throwTacticEx</c>, Lean/Meta/Tactic/Util.lean 46). The message
/// keeps Lean's wording, <c>Tactic `x` failed: …</c>; the goal it failed on is kept apart so the caller prints it with
/// its own names.
/// </summary>
public sealed class TacticException : MetaException
{
    /// <summary>Creates the exception.</summary>
    public TacticException()
    {
    }

    /// <summary>Creates the exception with a message.</summary>
    public TacticException(string message)
        : base(message)
    {
    }

    /// <summary>Creates the exception with a message and inner exception.</summary>
    public TacticException(string message, Exception innerException)
        : base(message, innerException)
    {
    }

    /// <summary>Creates the exception with a whole message.</summary>
    /// <param name="tactic">The tactic's name, as Lean spells it (<c>apply</c>, <c>introN</c>, …).</param>
    /// <param name="goal">The goal it failed on, or null.</param>
    /// <param name="message">The message.</param>
    public TacticException(string tactic, MVarId? goal, string message)
        : base(message)
    {
        Tactic = tactic;
        Goal = goal;
    }

    /// <summary>The tactic's name, as Lean spells it; null when not known.</summary>
    public string? Tactic { get; }

    /// <summary>The goal the tactic failed on; null when there is none.</summary>
    public MVarId? Goal { get; }

    /// <summary>Lean's <c>throwTacticEx tactic goal msg</c>: <c>Tactic `tactic` failed: detail</c>.</summary>
    /// <param name="tactic">The tactic's name.</param>
    /// <param name="goal">The goal.</param>
    /// <param name="detail">What went wrong.</param>
    /// <returns>The exception, to throw.</returns>
    public static TacticException Failed(string tactic, MVarId goal, string detail) =>
        new(tactic, goal, $"Tactic `{tactic}` failed: {detail}");
}

/// <summary>A saved <see cref="TacticM"/> state: the metavariable context and the goal list (Lean's <c>Tactic.SavedState</c>).</summary>
/// <param name="Meta">Meta's backtrackable state.</param>
/// <param name="Goals">The goal list.</param>
public sealed record TacticSavedState(SavedState Meta, ImmutableList<MVarId> Goals);

/// <summary>
/// The tactic monad: a <see cref="MetaM"/> and the list of goals (Lean's <c>Elab.Tactic.TacticM</c>, Lean/Elab/Tactic/Basic.lean
/// 50), with the goal-list operations a tactic uses. Each Warrant tactic is a Meta-level <c>MVarId</c> operation lifted
/// over the main goal (<see cref="LiftMetaTactic"/>, KTD6).
/// </summary>
/// <remarks>
/// Lean's <c>TacticM</c> also carries the elaborator's state; Warrant has no term elaborator, so a tactic's arguments are
/// already terms. Saving and restoring is O(1) because the metavariable context is immutable.
/// </remarks>
public sealed class TacticM
{
    /// <summary>Creates the monad over <paramref name="meta"/> with the goals <paramref name="goals"/>.</summary>
    /// <param name="meta">The Meta computation the tactics run in.</param>
    /// <param name="goals">The initial goals.</param>
    public TacticM(MetaM meta, IEnumerable<MVarId> goals)
    {
        Meta = meta ?? throw new ArgumentNullException(nameof(meta));
        Goals = [.. goals ?? throw new ArgumentNullException(nameof(goals))];
    }

    /// <summary>The Meta computation.</summary>
    public MetaM Meta { get; }

    /// <summary>The goals, main goal first (Lean's <c>getGoals</c>/<c>setGoals</c>); may contain solved goals until pruned.</summary>
    public ImmutableList<MVarId> Goals { get; set; }

    /// <summary>Saves the metavariable context and the goals (Lean's <c>Tactic.saveState</c>).</summary>
    public TacticSavedState SaveState() => new(Meta.SaveState(), Goals);

    /// <summary>Restores a saved state (Lean's <c>SavedState.restore</c>).</summary>
    public void Restore(TacticSavedState saved)
    {
        ArgumentNullException.ThrowIfNull(saved);
        Meta.Restore(saved.Meta);
        Goals = saved.Goals;
    }

    /// <summary>
    /// Charges one step of tactic fuel for running a tactic (Lean's <c>checkSystem</c> at each tactic), so a script whose
    /// tactics do no Meta work still runs under the budget.
    /// </summary>
    public void Step() => Meta.Budget.Tick();

    /// <summary>The goals that are not assigned yet (Lean's <c>getUnsolvedGoals</c>).</summary>
    public ImmutableList<MVarId> GetUnsolvedGoals() => [.. Goals.Where(g => !Meta.MCtx.IsAssignedOrDelayedAssigned(g))];

    /// <summary>Drops the goals unification has solved (Lean's <c>pruneSolvedGoals</c>).</summary>
    public void PruneSolvedGoals() => Goals = GetUnsolvedGoals();

    /// <summary>
    /// The first unsolved goal, dropping solved goals before it (Lean's <c>getMainGoal</c>, Basic.lean 491).
    /// </summary>
    /// <exception cref="TacticException">No goals remain.</exception>
    public MVarId GetMainGoal()
    {
        while (!Goals.IsEmpty)
        {
            var goal = Goals[0];
            if (!Meta.MCtx.IsAssignedOrDelayedAssigned(goal))
            {
                return goal;
            }
            Goals = Goals.RemoveAt(0);
        }
        throw new TacticException("no goals to be proved");
    }

    /// <summary>
    /// Replaces the first goal, which <see cref="GetMainGoal"/> has made the main goal, by <paramref name="goals"/>, which go
    /// first (Lean's <c>replaceMainGoal</c>, Basic.lean 486).
    /// </summary>
    public void ReplaceMainGoal(IEnumerable<MVarId> goals)
    {
        ArgumentNullException.ThrowIfNull(goals);
        if (Goals.IsEmpty)
        {
            throw new TacticException("no goals to be proved");
        }
        Goals = Goals.RemoveAt(0).InsertRange(0, goals);
    }

    /// <summary>Runs <paramref name="k"/> in the main goal's local context (Lean's <c>withMainContext</c>, Basic.lean 526).</summary>
    public T WithMainContext<T>(Func<T> k) => Meta.WithContext(GetMainGoal(), k);

    /// <summary>
    /// Runs a Meta-level tactic on the main goal and puts the goals it returns in its place (Lean's <c>liftMetaTactic</c>,
    /// Basic.lean 570).
    /// </summary>
    public void LiftMetaTactic(Func<MVarId, IReadOnlyList<MVarId>> tactic)
    {
        ArgumentNullException.ThrowIfNull(tactic);
        ReplaceMainGoal(WithMainContext(() => tactic(GetMainGoal())));
    }

    /// <summary>Like <see cref="LiftMetaTactic"/> for a tactic that leaves at most one goal (Lean's <c>liftMetaTactic1</c>).</summary>
    public void LiftMetaTactic1(Func<MVarId, MVarId?> tactic)
    {
        ArgumentNullException.ThrowIfNull(tactic);
        LiftMetaTactic(g => tactic(g) is { } next ? [next] : []);
    }

    /// <summary>Like <see cref="LiftMetaTactic"/> for a tactic that closes the goal (Lean's <c>liftMetaFinishingTactic</c>).</summary>
    public void LiftMetaFinishingTactic(Action<MVarId> tactic)
    {
        ArgumentNullException.ThrowIfNull(tactic);
        LiftMetaTactic(g =>
        {
            tactic(g);
            return [];
        });
    }

    /// <summary>
    /// Closes the main goal with <paramref name="val"/> (Lean's <c>closeMainGoal</c>, Basic.lean 561): with
    /// <paramref name="checkUnassigned"/>, <paramref name="val"/> must have no unassigned metavariables; the assignment
    /// must pass the occurs and scope checks.
    /// </summary>
    /// <exception cref="TacticException">A check fails.</exception>
    public void CloseMainGoal(string tacticName, Expr val, bool checkUnassigned = true)
    {
        ArgumentNullException.ThrowIfNull(val);
        var goal = GetMainGoal();
        Meta.WithContext(goal, () =>
        {
            if (checkUnassigned)
            {
                Meta.EnsureHasNoMVars(tacticName, goal, val);
            }
            if (!Meta.CheckedAssign(goal, val))
            {
                throw TacticException.Failed(tacticName, goal, $"attempting to close the goal using\n  {Meta.Pp(val)}\nthis is often due to a recursion or a hypothesis that is not in scope (occurs check failure)");
            }
            return 0;
        });
        ReplaceMainGoal([]);
    }
}

public sealed partial class MetaM
{
    /// <summary>
    /// How messages name translated constants and record fields (KTD7). The engine sets it from the translation, so a
    /// tactic's error message reads in C# names, as the goals do.
    /// </summary>
    public NotationNames? DisplayNames { get; init; }

    /// <summary>Prints <paramref name="e"/> in the current local context with <see cref="DisplayNames"/>, for messages.</summary>
    public string Pp(Expr e)
    {
        ArgumentNullException.ThrowIfNull(e);
        return new Notation(Env, MCtx, DisplayNames).Print(this.InstantiateMVars(e), LCtx);
    }

    /// <summary>A constant's name as messages print it: its C# name when translated, else its Lean name.</summary>
    public string PpConst(Name name)
    {
        ArgumentNullException.ThrowIfNull(name);
        return DisplayNames?.Constant?.Invoke(name) ?? name.ToString();
    }

    /// <summary>The goal's tag (Lean's <c>MVarId.getTag</c>, Util.lean 23).</summary>
    public Name GetTag(MVarId mvarId) => GetMVarDecl(mvarId).UserName;

    /// <summary>Sets the goal's tag (Lean's <c>MVarId.setTag</c>, Util.lean 26).</summary>
    public void SetTag(MVarId mvarId, Name tag) => SetMVarUserName(mvarId, tag);

    /// <summary>A fresh goal (Lean's <c>mkFreshExprSyntheticOpaqueMVar</c>, Util.lean 36).</summary>
    public MVarExpr MkFreshExprSyntheticOpaqueMVar(Expr type, Name? tag = null) =>
        MkFreshExprMVar(type, MetavarKind.SyntheticOpaque, tag ?? Name.Anonymous);

    /// <summary>Fails if the goal is already assigned (Lean's <c>MVarId.checkNotAssigned</c>, Util.lean 65).</summary>
    /// <exception cref="TacticException">It is assigned.</exception>
    public void CheckNotAssigned(MVarId mvarId, string tacticName)
    {
        if (MCtx.IsAssignedOrDelayedAssigned(mvarId))
        {
            throw new TacticException(tacticName, mvarId, $"`{tacticName}` failed, metavariable has already been assigned");
        }
    }

    /// <summary>The goal's type (Lean's <c>MVarId.getType</c>).</summary>
    public Expr GetMVarType(MVarId mvarId) => GetMVarDecl(mvarId).Type;

    /// <summary>The goal's type, instantiated and in weak head normal form (Lean's <c>MVarId.getType'</c>, Util.lean 80).</summary>
    public Expr GetMVarTypeWhnf(MVarId mvarId) => Whnf(this.InstantiateMVars(GetMVarType(mvarId)));

    /// <summary>Beta-reduces the head of the goal's type (Lean's <c>MVarId.headBetaType</c>).</summary>
    public void HeadBetaType(MVarId mvarId) => SetMVarType(mvarId, GetMVarType(mvarId).HeadBeta());

    /// <summary>
    /// Fails if <paramref name="e"/> has an unassigned metavariable (Lean's <c>ensureHasNoMVars</c>), which would otherwise
    /// leave a hole in the proof.
    /// </summary>
    /// <exception cref="TacticException">It has one.</exception>
    public void EnsureHasNoMVars(string tacticName, MVarId goal, Expr e)
    {
        var instantiated = this.InstantiateMVars(e);
        if (instantiated.HasExprMVar)
        {
            throw TacticException.Failed(tacticName, goal, $"the term has holes that were not filled\n  {Pp(instantiated)}");
        }
    }

    /// <summary>
    /// <c>@id.{u} expectedType e</c>, a term of <paramref name="expectedType"/> that records the type a definitional change
    /// moved from (Lean's <c>mkExpectedTypeHint</c>, Lean/Meta/AppBuilder.lean 35).
    /// </summary>
    public Expr MkExpectedTypeHint(Expr e, Expr expectedType) =>
        Expr.App(Expr.Const(TacticNames.Id, GetLevel(expectedType)), expectedType, e);

    /// <summary>
    /// Replaces the goal by one whose type is <paramref name="targetNew"/>, definitionally equal to the old type, through
    /// <c>@id</c> (Lean's <c>MVarId.replaceTargetDefEq</c>, Lean/Meta/Tactic/Replace.lean 45).
    /// </summary>
    /// <returns>The new goal, or <paramref name="mvarId"/> when nothing changed.</returns>
    public MVarId ReplaceTargetDefEq(MVarId mvarId, Expr targetNew) => WithContext(mvarId, () =>
    {
        CheckNotAssigned(mvarId, "change");
        var target = GetMVarType(mvarId);
        if (target == targetNew)
        {
            return mvarId;
        }
        target = this.InstantiateMVars(target);
        targetNew = this.InstantiateMVars(targetNew);
        if (target == targetNew)
        {
            SetMVarType(mvarId, target);
            return mvarId;
        }
        var mvarNew = MkFreshExprSyntheticOpaqueMVar(targetNew, GetTag(mvarId));
        Assign(mvarId, MkExpectedTypeHint(mvarNew, target));
        return mvarNew.Id;
    });
}

/// <summary>The Init constants the basic tactics put into proofs; <c>Warrant.Engine.EmittedConstants</c> lists them all (KTD29).</summary>
public static class TacticNames
{
    /// <summary><c>id</c>: the expected-type hint of a definitional change (<c>unfold</c>'s delta path).</summary>
    public static readonly Name Id = Name.From("id");

    /// <summary><c>Eq</c>.</summary>
    public static readonly Name Eq = Name.From("Eq");

    /// <summary><c>Eq.refl</c>: the proof <c>rfl</c> builds.</summary>
    public static readonly Name EqRefl = Name.From("Eq", "refl");
}
