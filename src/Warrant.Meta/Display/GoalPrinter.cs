using System.Text;
using Warrant.Cic;
using Warrant.Kernel;

namespace Warrant.Meta;

/// <summary>
/// Prints goals in Lean's layout (a port of <c>Lean/Meta/PPGoal.lean</c>'s <c>ppGoal</c>, KTD7):
/// an optional <c>case tag</c> line, the visible hypotheses in context order with consecutive
/// hypotheses of the same type sharing a line (<c>a b : Int32</c>), local definitions as
/// <c>x : T := v</c>, then <c>⊢ goal</c>. Terms go through <see cref="Notation"/>.
/// </summary>
/// <remarks>
/// Lean's options take their defaults: auxiliary and implementation-detail hypotheses are hidden,
/// and a local definition's value shows unless it is non-atomic and deeper than the threshold
/// (255 for a tactic goal, 0 otherwise), when it prints as <c>⋯</c>. Lean's 120-column line
/// breaking is not ported: each hypothesis is one line.
/// </remarks>
/// <param name="env">Supplies the binder infos that decide which arguments are hidden.</param>
/// <param name="names">Display names for translated constants and record fields.</param>
public sealed class GoalPrinter(KernelEnvironment env, NotationNames? names = null)
{
    /// <summary>Lean's <c>pp.showLetValues.tactic.threshold</c> (255), capped at 254 as <c>shouldShowLetValue</c> does.</summary>
    private const int TacticLetValueDepth = 254;

    /// <summary>Prints the goal <paramref name="goal"/> of <paramref name="mctx"/>.</summary>
    /// <param name="mctx">The metavariable context declaring the goal.</param>
    /// <param name="goal">The goal.</param>
    /// <returns>The goal's text, lines separated by <c>\n</c>; <c>unknown goal</c> if it is not declared.</returns>
    public string PpGoal(MetavarContext mctx, MVarId goal)
    {
        ArgumentNullException.ThrowIfNull(mctx);
        if (mctx.FindDecl(goal) is not { } decl)
        {
            return "unknown goal";
        }
        var notation = new Notation(env, mctx, names);
        var lctx = decl.LCtx;
        bool tactic = decl.Kind == MetavarKind.SyntheticOpaque;
        var lines = new List<string>();
        var pending = new List<Name>();
        Expr? prevType = null;

        void PushPending()
        {
            if (pending.Count > 0 && prevType is not null)
            {
                lines.Add($"{string.Join(' ', pending)} : {notation.Print(prevType, lctx)}");
            }
            pending.Clear();
            prevType = null;
        }

        foreach (var localDecl in lctx.Decls)
        {
            if (localDecl.IsImplementationDetail)
            {
                continue;
            }
            var type = mctx.InstantiateMVars(localDecl.Type).Result;
            if (localDecl is LDecl { Nondep: false } let)
            {
                PushPending();
                var line = $"{let.UserName} : {notation.Print(type, lctx)}";
                var value = mctx.InstantiateMVars(let.Value).Result;
                line += ShouldShowLetValue(tactic, value) ? $" := {notation.Print(value, lctx)}" : " := ⋯";
                lines.Add(line);
                continue;
            }
            if (prevType is not null && prevType != type)
            {
                PushPending();
            }
            pending.Add(localDecl.UserName);
            prevType = type;
        }
        PushPending();
        lines.Add("⊢ " + notation.Print(decl.Type, lctx));

        var text = string.Join('\n', lines);
        return decl.UserName.IsAnonymous ? text : $"case {decl.UserName}\n{text}";
    }

    /// <summary>Prints several goals, separated by a blank line as Lean's "unsolved goals" message separates them.</summary>
    /// <param name="mctx">The metavariable context declaring the goals.</param>
    /// <param name="goals">The goals.</param>
    /// <returns>The text.</returns>
    public string PpGoals(MetavarContext mctx, IEnumerable<MVarId> goals)
    {
        ArgumentNullException.ThrowIfNull(goals);
        var sb = new StringBuilder();
        foreach (var goal in goals)
        {
            if (sb.Length > 0)
            {
                sb.Append("\n\n");
            }
            sb.Append(PpGoal(mctx, goal));
        }
        return sb.ToString();
    }

    /// <summary>Lean's <c>ppGoal.shouldShowLetValue</c> with the options' defaults.</summary>
    private static bool ShouldShowLetValue(bool tactic, Expr value) =>
        IsAtomic(value) || ApproxDepth(value, tactic ? TacticLetValueDepth + 1 : 1) <= (tactic ? TacticLetValueDepth : 0);

    /// <summary>Lean's <c>Expr.isAtomic</c>.</summary>
    private static bool IsAtomic(Expr e) =>
        e.Kind is ExprKind.Const or ExprKind.Sort or ExprKind.BVar or ExprKind.NatLit or ExprKind.StrLit or ExprKind.MVar or ExprKind.FVar;

    /// <summary>The depth of <paramref name="e"/> (Lean's <c>approxDepth</c>), counted no further than <paramref name="cap"/>.</summary>
    private static int ApproxDepth(Expr e, int cap)
    {
        if (cap == 0)
        {
            return 0;
        }
        return e switch
        {
            AppExpr a => 1 + Math.Max(ApproxDepth(a.Fn, cap - 1), ApproxDepth(a.Arg, cap - 1)),
            BindingExpr b => 1 + Math.Max(ApproxDepth(b.BinderType, cap - 1), ApproxDepth(b.Body, cap - 1)),
            LetExpr l => 1 + Math.Max(ApproxDepth(l.BinderType, cap - 1), Math.Max(ApproxDepth(l.Value, cap - 1), ApproxDepth(l.Body, cap - 1))),
            MDataExpr m => 1 + ApproxDepth(m.Expr, cap - 1),
            ProjExpr p => 1 + ApproxDepth(p.Struct, cap - 1),
            _ => 0,
        };
    }
}
