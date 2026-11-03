using Warrant.Cic;

namespace Warrant.Meta;

/// <summary>Tactic combinators (Lean/Elab/Tactic/BuiltinTactic.lean): <c>all_goals</c>, <c>try</c> and <c>first</c>.</summary>
public static class Combinators
{
    /// <summary>
    /// Runs <paramref name="tactic"/> on each unsolved goal by itself and collects the goals each leaves (Lean's
    /// <c>evalAllGoals</c>, BuiltinTactic.lean 229). A failure on any goal propagates, as Lean's does outside error
    /// recovery; an enclosing <see cref="Try"/> restores the state.
    /// </summary>
    public static void AllGoals(this TacticM t, Action tactic)
    {
        ArgumentNullException.ThrowIfNull(t);
        ArgumentNullException.ThrowIfNull(tactic);
        var goalsNew = new List<MVarId>();
        foreach (var goal in t.Goals)
        {
            if (t.Meta.MCtx.IsAssignedOrDelayedAssigned(goal))
            {
                continue;
            }
            t.Goals = [goal];
            tactic();
            goalsNew.AddRange(t.GetUnsolvedGoals());
        }
        t.Goals = [.. goalsNew];
    }

    /// <summary>
    /// Runs <paramref name="tactic"/>; if it fails with a tactic error, restores the state and goals as they were (Lean's
    /// <c>try tac</c>, the macro <c>first | tac | skip</c>). Running out of fuel or time is not a tactic error and
    /// propagates, as Lean's runtime exceptions do.
    /// </summary>
    /// <returns>Whether <paramref name="tactic"/> succeeded.</returns>
    public static bool Try(this TacticM t, Action tactic) => t.First(tactic, () => { });

    /// <summary>
    /// Runs the first of <paramref name="tactics"/> that succeeds, restoring the state before each attempt (Lean's
    /// <c>first</c>, BuiltinTactic.lean 631); the last one's failure propagates.
    /// </summary>
    /// <returns>Whether the first alternative succeeded.</returns>
    public static bool First(this TacticM t, params Action[] tactics)
    {
        ArgumentNullException.ThrowIfNull(t);
        ArgumentNullException.ThrowIfNull(tactics);
        if (tactics.Length == 0)
        {
            throw new ArgumentException("first needs at least one alternative.", nameof(tactics));
        }
        var saved = t.SaveState();
        for (int i = 0; i < tactics.Length - 1; i++)
        {
            try
            {
                tactics[i]();
                return i == 0;
            }
            catch (MetaException ex) when (IsRecoverable(ex))
            {
                t.Restore(saved);
            }
        }
        tactics[^1]();
        return tactics.Length == 1;
    }

    /// <summary>Whether a failure is one <c>try</c> and <c>first</c> recover from: any Meta error except running out of budget.</summary>
    public static bool IsRecoverable(Exception ex) => ex is MetaException and not MetaResourceException;
}
