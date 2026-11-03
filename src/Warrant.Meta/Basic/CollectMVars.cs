using Warrant.Cic;

namespace Warrant.Meta;

/// <summary>The state of a metavariable collection: what was visited and what was found (Lean's <c>CollectMVars.State</c>).</summary>
public sealed class CollectMVarsState
{
    /// <summary>The subterms already visited.</summary>
    internal HashSet<Expr> VisitedExpr { get; } = [];

    /// <summary>The metavariables found, in order of first occurrence.</summary>
    public List<MVarId> Result { get; } = [];
}

/// <summary>Collection of the metavariables in a term (ports of Lean's <c>Lean/Util/CollectMVars.lean</c> and <c>Lean/Meta/CollectMVars.lean</c>).</summary>
public static class CollectMVars
{
    /// <summary>Adds the metavariables occurring syntactically in <paramref name="e"/> to <paramref name="s"/> (Lean's <c>Expr.collectMVars</c>).</summary>
    public static CollectMVarsState Collect(Expr e, CollectMVarsState s)
    {
        ArgumentNullException.ThrowIfNull(e);
        ArgumentNullException.ThrowIfNull(s);
        var pending = new Stack<Expr>();
        pending.Push(e);
        while (pending.Count > 0)
        {
            var x = pending.Pop();
            if (!x.HasExprMVar || !s.VisitedExpr.Add(x))
            {
                continue;
            }
            // Children are pushed in reverse so they are visited left to right, as in Lean.
            switch (x)
            {
                case ProjExpr p:
                    pending.Push(p.Struct);
                    break;
                case BindingExpr b:
                    pending.Push(b.Body);
                    pending.Push(b.BinderType);
                    break;
                case LetExpr l:
                    pending.Push(l.Body);
                    pending.Push(l.Value);
                    pending.Push(l.BinderType);
                    break;
                case AppExpr a:
                    pending.Push(a.Arg);
                    pending.Push(a.Fn);
                    break;
                case MDataExpr m:
                    pending.Push(m.Expr);
                    break;
                case MVarExpr mv:
                    s.Result.Add(mv.Id);
                    break;
            }
        }
        return s;
    }

    /// <summary>
    /// Adds the unassigned metavariables of <paramref name="e"/>, after instantiation, to
    /// <paramref name="s"/>; for a delayed-assigned one, also those of its pending metavariable
    /// (Lean's <c>Meta.collectMVars</c>).
    /// </summary>
    public static void CollectMVarsM(this IMonadMCtx m, Expr e, CollectMVarsState s)
    {
        ArgumentNullException.ThrowIfNull(m);
        ArgumentNullException.ThrowIfNull(s);
        e = m.InstantiateMVars(e);
        int resultSavedSize = s.Result.Count;
        Collect(e, s);
        int end = s.Result.Count;
        for (int i = resultSavedSize; i < end; i++)
        {
            if (m.MCtx.GetDelayedMVarAssignment(s.Result[i]) is { } d)
            {
                m.CollectMVarsM(Expr.MVar(d.MVarIdPending), s);
            }
        }
    }

    /// <summary>The metavariables of <paramref name="e"/>, as <see cref="CollectMVarsM"/> finds them (Lean's <c>getMVars</c>).</summary>
    public static MVarId[] GetMVars(this IMonadMCtx m, Expr e)
    {
        var s = new CollectMVarsState();
        m.CollectMVarsM(e, s);
        return [.. s.Result];
    }

    /// <summary><see cref="GetMVars"/> without the delayed-assigned ones (Lean's <c>getMVarsNoDelayed</c>).</summary>
    public static MVarId[] GetMVarsNoDelayed(this IMonadMCtx m, Expr e)
    {
        ArgumentNullException.ThrowIfNull(m);
        return [.. m.GetMVars(e).Where(id => !m.MCtx.IsDelayedAssigned(id))];
    }
}
