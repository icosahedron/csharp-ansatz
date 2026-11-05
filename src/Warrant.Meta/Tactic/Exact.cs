using Warrant.Cic;
using Warrant.Kernel;

namespace Warrant.Meta;

/// <summary>The <c>exact</c> tactic (KTD6).</summary>
public static class ExactTactic
{
    /// <summary>
    /// <c>exact e</c>: closes the main goal with <paramref name="e"/>, a hypothesis or a constant (Lean's <c>evalExact</c>,
    /// Lean/Elab/Tactic/ElabTerm.lean 100, through <c>closeMainGoalUsing</c> and <c>elabTermEnsuringType</c>).
    /// </summary>
    /// <remarks>
    /// <para>
    /// Warrant has no term elaborator (KTD6), so this does what <c>elabApp</c> does for a bare identifier: it inserts a
    /// fresh metavariable for each leading implicit, strict-implicit or instance-implicit binder of <paramref name="e"/>'s
    /// type, then unifies the type with the goal, letting unification assign goals (<c>withAssignableSyntheticOpaque</c>).
    /// No hole may remain afterwards.
    /// </para>
    /// <para>
    /// Lean synthesizes the instance arguments; until instance synthesis exists (U16), an instance argument that
    /// unification did not assign fails the tactic with a message saying so. One it did assign is left to the kernel,
    /// which checks the whole proof.
    /// </para>
    /// </remarks>
    /// <param name="t">The tactic state.</param>
    /// <param name="e">The term: a free variable of the goal's context, or a constant at fresh universe metavariables.</param>
    /// <exception cref="TacticException">The types do not unify, or a hole remains.</exception>
    public static void Exact(this TacticM t, Expr e)
    {
        ArgumentNullException.ThrowIfNull(t);
        ArgumentNullException.ThrowIfNull(e);
        var m = t.Meta;
        var goal = t.GetMainGoal();
        var term = m.WithContext(goal, () =>
        {
            var target = m.InstantiateMVars(m.GetMVarType(goal));
            var (applied, holes) = InsertImplicitArgs(m, e);
            var type = m.InferType(applied);
            if (!m.WithAssignableSyntheticOpaque(() => m.IsDefEq(type, target)))
            {
                throw TacticException.Failed("exact", goal, TypeMismatch(m, applied, type, target));
            }
            foreach (var (hole, isInstance) in holes)
            {
                if (!m.MCtx.IsAssigned(hole.Id))
                {
                    var holeType = m.Pp(m.GetMVarType(hole.Id));
                    throw TacticException.Failed("exact", goal, isInstance
                        ? $"failed to synthesize instance\n  {holeType}\ninstance synthesis is not available yet, so an instance argument must be determined by the goal"
                        : $"don't know how to synthesize implicit argument\n  {holeType}");
                }
            }
            return m.InstantiateMVars(applied);
        });
        t.CloseMainGoal("exact", term, checkUnassigned: true);
    }

    /// <summary>
    /// Lean's <c>type mismatch</c> error (<c>Term.throwTypeMismatchError</c>): the term, its type and the expected type.
    /// </summary>
    internal static string TypeMismatch(MetaM m, Expr e, Expr type, Expr expected) =>
        $"type mismatch\n  {m.Pp(e)}\nhas type\n  {m.Pp(type)}\nbut is expected to have type\n  {m.Pp(expected)}";

    /// <summary>
    /// Applies <paramref name="e"/> to fresh metavariables for its leading non-explicit binders, as <c>elabApp</c> does for an
    /// identifier with no arguments; instance-implicit ones are synthetic, the others natural.
    /// </summary>
    private static (Expr Applied, List<(MVarExpr Hole, bool IsInstance)> Holes) InsertImplicitArgs(MetaM m, Expr e)
    {
        var holes = new List<(MVarExpr, bool)>();
        var type = m.InferType(e);
        while (true)
        {
            m.Budget.Tick();
            if (type is not ForallExpr)
            {
                type = m.Whnf(type);
            }
            if (type is not ForallExpr { BinderInfo: not BinderInfo.Default } f)
            {
                return (e, holes);
            }
            bool isInstance = f.BinderInfo == BinderInfo.InstImplicit;
            var hole = m.MkFreshExprMVar(f.BinderType, isInstance ? MetavarKind.Synthetic : MetavarKind.Natural, f.BinderName);
            holes.Add((hole, isInstance));
            e = Expr.App(e, hole);
            type = ExprOps.Instantiate(f.Body, hole);
        }
    }
}
