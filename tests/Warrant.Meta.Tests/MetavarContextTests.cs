using Warrant.Cic;
using Warrant.Kernel;
using static Warrant.Meta.Tests.MetaTestSupport;

namespace Warrant.Meta.Tests;

/// <summary>
/// Checked assignment, depths, backtracking and instantiation of the metavariable context
/// (KTD3, KTD4; docs/m5a/02, "The metavariable context").
/// </summary>
public class MetavarContextTests
{
    private static readonly Expr Nat = Expr.Const(N("Nat"));
    private static readonly Expr F = Expr.Const(N("f"));
    private static readonly Expr G = Expr.Const(N("g"));
    private static readonly Expr C = Expr.Const(N("c"));

    [Fact]
    public void CheckedAssignFailsTheOccursCheck()
    {
        var m = NewMeta();
        var hole = m.MkFreshExprMVar(Nat);
        var other = m.MkFreshExprMVar(Nat);

        Assert.False(m.CheckedAssign(hole.Id, Expr.App(F, hole)));
        Assert.False(m.IsAssigned(hole.Id));
        // Also through another metavariable's assignment.
        m.Assign(other.Id, Expr.App(G, hole));
        Assert.False(m.CheckedAssign(hole.Id, Expr.App(F, other)));
        Assert.False(m.IsAssigned(hole.Id));

        var fresh = m.MkFreshExprMVar(Nat);
        Assert.True(m.CheckedAssign(hole.Id, Expr.App(F, fresh)));
        Assert.Equal(Expr.App(F, fresh), m.MCtx.GetExprAssignment(hole.Id));
    }

    [Fact]
    public void CheckedAssignFailsTheScopeCheck()
    {
        var m = NewMeta();
        var outer = m.MkFreshExprMVar(Nat);
        m.WithLocalDeclD(N("y"), Nat, y =>
        {
            // y is not in ?outer's context, so it may not appear in its value.
            Assert.False(m.CheckedAssign(outer.Id, y));
            Assert.False(m.CheckedAssign(outer.Id, Expr.App(F, y)));
            Assert.False(m.IsAssigned(outer.Id));

            // A hole whose context has y may use it, and an out-of-scope beta-redex argument is
            // reduced away.
            var inner = m.MkFreshExprMVar(Nat);
            Assert.True(m.CheckedAssign(inner.Id, Expr.App(F, y)));
            Assert.True(m.CheckedAssign(outer.Id, Expr.App(Expr.Lam(N("z"), Nat, C), y)));
            Assert.Equal(C, m.MCtx.GetExprAssignment(outer.Id));
            return 0;
        });

        // A dependent local definition out of scope is replaced by its value.
        var outer2 = m.MkFreshExprMVar(Nat);
        m.WithLetDecl(N("z"), Nat, C, z =>
        {
            Assert.True(m.CheckedAssign(outer2.Id, Expr.App(F, z)));
            Assert.Equal(Expr.App(F, C), m.MCtx.GetExprAssignment(outer2.Id));
            return 0;
        });

        // A hole with a larger context may not appear in the value of one with a smaller context.
        var small = m.MkFreshExprMVar(Nat);
        var big = m.WithLocalDeclD(N("y"), Nat, _ => m.MkFreshExprMVar(Nat));
        Assert.False(m.CheckedAssign(small.Id, big));
    }

    [Fact]
    public void WithNewMCtxDepthMakesOuterMVarsReadOnly()
    {
        var m = NewMeta();
        var outer = m.MkFreshExprMVar(Nat);
        var outerLevel = m.MkFreshLevelMVar().MVarId!.Value;
        var goal = m.MkFreshExprMVar(Nat, MetavarKind.SyntheticOpaque);
        Assert.True(m.MCtx.IsAssignable(outer.Id));
        Assert.False(m.IsReadOnlyOrSyntheticOpaque(outer.Id));
        Assert.True(m.IsReadOnlyOrSyntheticOpaque(goal.Id));
        Assert.False(m.WithAssignableSyntheticOpaque(() => m.IsReadOnlyOrSyntheticOpaque(goal.Id)));

        var before = m.MCtx;
        m.WithNewMCtxDepth(() =>
        {
            Assert.Equal(1, m.MCtx.Depth);
            Assert.False(m.MCtx.IsAssignable(outer.Id));
            Assert.True(m.IsReadOnly(outer.Id));
            Assert.True(m.IsReadOnlyOrSyntheticOpaque(outer.Id));
            Assert.True(m.IsReadOnly(outerLevel));
            var inner = m.MkFreshExprMVar(Nat);
            Assert.True(m.MCtx.IsAssignable(inner.Id));
            Assert.False(m.IsReadOnlyOrSyntheticOpaque(inner.Id));
            m.Assign(inner.Id, C);
            return 0;
        });
        Assert.False(m.WithNewMCtxDepth(() => m.IsReadOnly(outerLevel), allowLevelAssignments: true));

        // Lean 4.35.0 restores the whole context on exit.
        Assert.Same(before, m.MCtx);
        Assert.True(m.MCtx.IsAssignable(outer.Id));
    }

    [Fact]
    public void SaveAssignRestoreLeavesTheContextAsBefore()
    {
        var m = NewMeta();
        var hole = m.MkFreshExprMVar(Nat);
        var saved = m.SaveState();

        Assert.True(m.CheckedAssign(hole.Id, C));
        var extra = m.MkFreshExprMVar(Nat);
        Assert.True(m.IsAssigned(hole.Id));

        m.Restore(saved);
        Assert.Same(saved.MCtx, m.MCtx);
        Assert.False(m.IsAssigned(hole.Id));
        Assert.Null(m.MCtx.FindDecl(extra.Id));
        Assert.Equal(hole, m.InstantiateMVars(hole));
    }

    [Fact]
    public void InstantiateMVarsBetaReducesAssignedHeadsAndInstantiatesLevels()
    {
        var m = NewMeta();
        var fn = m.MkFreshExprMVar(Expr.Forall(N("x"), Nat, Nat));
        m.Assign(fn.Id, Expr.Lam(N("x"), Nat, Expr.App(F, Expr.BVar(0))));
        Assert.Equal(Expr.App(F, C), m.InstantiateMVars(Expr.App(fn, C)));

        var u = m.MkFreshLevelMVar();
        var v = m.MkFreshLevelMVar();
        m.AssignLevelMVar(u.MVarId!.Value, Level.Succ(v));
        m.AssignLevelMVar(v.MVarId!.Value, Level.Zero);
        Assert.Equal(Expr.Sort(Level.One), m.InstantiateMVars(Expr.Sort(u)));
        Assert.Equal(Expr.Const(N("PUnit"), Level.One), m.InstantiateMVars(Expr.Const(N("PUnit"), u)));
        // Path compression: ?u's assignment is now the instantiated one.
        Assert.Equal(Level.One, m.MCtx.GetLevelAssignment(u.MVarId!.Value));
    }

    [Fact]
    public void InstantiateMVarsOnADeepChainOfAssignmentsIsLinear()
    {
        // ?m₀ := g ?m₁ ?m₁, ?m₁ := g ?m₂ ?m₂, …, ?mₙ := c. The term this denotes is a DAG of 2n
        // edges but a tree of 2ⁿ leaves, so only sharing-aware instantiation finishes.
        const int Depth = 10_000;
        var m = NewMeta();
        var holes = new MVarExpr[Depth + 1];
        for (int i = 0; i <= Depth; i++)
        {
            holes[i] = m.MkFreshExprMVar(Nat);
        }
        for (int i = 0; i < Depth; i++)
        {
            m.Assign(holes[i].Id, Expr.App(G, holes[i + 1], holes[i + 1]));
        }
        m.Assign(holes[Depth].Id, C);

        var expected = C;
        for (int i = 0; i < Depth; i++)
        {
            expected = Expr.App(G, expected, expected);
        }

        var (result, used) = KernelThread.Run(() =>
        {
            long start = m.Budget.FuelUsed;
            var r = m.InstantiateMVars(holes[0]);
            return (r, m.Budget.FuelUsed - start);
        });
        Assert.True(expected.Equals(result));
        Assert.InRange(used, Depth, 4L * Depth);

        // The instantiated values were written back, so doing it again costs one step.
        long again = KernelThread.Run(() =>
        {
            long start = m.Budget.FuelUsed;
            m.InstantiateMVars(holes[0]);
            return m.Budget.FuelUsed - start;
        });
        Assert.Equal(1, again);
    }

    [Fact]
    public void MetaFuelRunsOutAsAMetaResourceException()
    {
        var m = NewMeta(new MetaLimits(10));
        var holes = new MVarExpr[50];
        for (int i = 0; i < holes.Length; i++)
        {
            holes[i] = m.MkFreshExprMVar(Nat);
        }
        for (int i = 0; i + 1 < holes.Length; i++)
        {
            m.Assign(holes[i].Id, Expr.App(F, holes[i + 1]));
        }
        var ex = Assert.Throws<MetaResourceException>(() => m.InstantiateMVars(holes[0]));
        Assert.Contains("tactic fuel exhausted", ex.Message, StringComparison.Ordinal);

        var late = NewMeta(new MetaLimits(1_000_000) { Deadline = DateTimeOffset.UtcNow.AddSeconds(-1) });
        var hole = late.MkFreshExprMVar(Nat);
        late.Assign(hole.Id, Expr.App(F, C));
        Assert.Throws<MetaResourceException>(() => late.InstantiateMVars(Expr.App(F, hole)));
    }
}
