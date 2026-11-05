using Warrant.Cic;
using Warrant.Kernel;
using static Warrant.Meta.Tests.MetaTestSupport;

namespace Warrant.Meta.Tests;

/// <summary>
/// <c>mkLambdaFVars</c> over goals and the delayed assignments it creates (KTD3, docs/m5a/02): a
/// goal is replaced by <c>?n x</c>, and instantiation substitutes it only once the goal is solved
/// with a ground term. Every finished proof is admitted by the kernel.
/// </summary>
public class DelayedAssignmentTests
{
    [Fact]
    public void MkLambdaFVarsOverAGoalMakesADelayedAssignmentThatInstantiatesOnceSolved()
    {
        var m = NewMeta();
        m.WithLocalDeclD(N("P"), Expr.Prop, p => m.WithLocalDeclD(N("x"), p, x =>
        {
            var g = m.MkFreshExprMVar(p, MetavarKind.SyntheticOpaque);
            var lam = m.MkLambdaFVars([x], g);

            // fun (x : P) => ?n x, with ?n #[x] := ?g and ?g itself untouched.
            var body = Assert.IsType<AppExpr>(Assert.IsType<LamExpr>(lam).Body);
            Assert.Equal(Expr.BVar(0), body.Arg);
            var n = Assert.IsType<MVarExpr>(body.Fn).Id;
            var d = m.MCtx.GetDelayedMVarAssignment(n);
            Assert.NotNull(d);
            Assert.Equal(g.Id, d.MVarIdPending);
            Assert.Equal<Expr>([x], d.FVars);
            Assert.False(m.IsAssigned(g.Id));
            // ?n : ∀ (x : P), P lives in a context without x.
            var nDecl = m.GetMVarDecl(n);
            Assert.False(nDecl.LCtx.ContainsFVar(x));
            Assert.Equal(MetavarKind.SyntheticOpaque, nDecl.Kind);
            Assert.Equal(Expr.Forall(N("x"), p, p), nDecl.Type);

            Assert.True(m.WithContext(g.Id, () => m.CheckedAssign(g.Id, x)));
            var r = m.InstantiateMVars(lam);
            Assert.Equal(Expr.Lam(N("x"), p, Expr.BVar(0)), r);

            var proof = m.MkLambdaFVars([p], r);
            KernelAdmits("test.idLam", IdPropType, proof);
            return 0;
        }));
    }

    [Fact]
    public void ADelayedMVarWaitsForItsPendingGoal()
    {
        var m = NewMeta();
        var g = m.MkFreshExprMVar(IdPropType, MetavarKind.SyntheticOpaque);
        var (p, g1) = Intro(m, g.Id, "P");
        var (h, g2) = Intro(m, g1, "h");

        // ?g := fun P => ?n₁ P, where ?n₁ #[P] := ?g₁ := fun h => ?n₂ h and ?n₂ #[h] := ?g₂ is open.
        var open = m.InstantiateMVars(g);
        Assert.True(open.HasExprMVar);
        var openBody = Assert.IsType<AppExpr>(Assert.IsType<LamExpr>(open).Body);
        Assert.True(m.IsDelayedAssigned(Assert.IsType<MVarExpr>(openBody.Fn).Id));

        // The pending goal is assigned, but to a term that still has a hole: still not substituted.
        var k = m.WithContext(g2, () => m.MkFreshExprMVar(p));
        m.Assign(g2, k);
        Assert.True(m.InstantiateMVars(g).HasExprMVar);
        Assert.Contains(k.Id, m.GetMVars(g));

        // Once the hole is filled with a ground term, the whole proof is ground.
        Assert.True(m.WithContext(k.Id, () => m.CheckedAssign(k.Id, h)));
        var proof = m.InstantiateMVars(g);
        Assert.Equal(Expr.Lam(N("P"), Expr.Prop, Expr.Lam(N("h"), Expr.BVar(0), Expr.BVar(0))), proof);
        Assert.Empty(m.GetMVars(g));
        KernelAdmits("test.introIntro", IdPropType, proof);
    }

    [Fact]
    public void ANaturalMVarIsAssignedRatherThanDelayed()
    {
        var m = NewMeta();
        m.WithLocalDeclD(N("P"), Expr.Prop, p => m.WithLocalDeclD(N("x"), p, x =>
        {
            var hole = m.MkFreshExprMVar(p);
            var lam = m.MkLambdaFVars([x], hole);

            // ?hole := ?n x for a fresh natural ?n : ∀ (x : P), P outside x's scope.
            var app = Assert.IsType<AppExpr>(m.MCtx.GetExprAssignment(hole.Id));
            Assert.Equal(x, app.Arg);
            var n = Assert.IsType<MVarExpr>(app.Fn).Id;
            Assert.Equal(MetavarKind.Natural, m.GetMVarKind(n));
            Assert.False(m.IsDelayedAssigned(n));
            Assert.Equal(Expr.Lam(N("x"), p, Expr.App(Expr.MVar(n), Expr.BVar(0))), lam);

            // Assigning ?n a lambda is beta-reduced away by instantiation.
            m.Assign(n, Expr.Lam(N("y"), p, Expr.BVar(0)));
            Assert.Equal(Expr.Lam(N("x"), p, Expr.BVar(0)), m.InstantiateMVars(lam));
            return 0;
        }));
    }

    [Fact]
    public void ForallTelescopeAndMkForallFVarsRoundTrip()
    {
        var m = NewMeta();
        var back = m.ForallTelescope(IdPropType, (xs, body) =>
        {
            Assert.Equal(2, xs.Length);
            Assert.Equal(xs[0], body);
            Assert.Equal(xs[0], m.GetFVarLocalDecl(xs[1]).Type);
            return m.MkForallFVars(xs, body);
        });
        Assert.Equal(IdPropType, back);
        Assert.True(m.LCtx.IsEmpty);
    }

    [Fact]
    public void CollectForwardDepsAddsTheVariablesThatDependOnTheReverted()
    {
        var m = NewMeta();
        var nat = Expr.Const(N("Nat"));
        m.WithLocalDeclD(N("α"), Expr.Type, a => m.WithLocalDeclD(N("n"), nat, n => m.WithLocalDeclD(N("x"), a, x =>
        {
            Assert.Equal([a, x], m.CollectForwardDeps([a], preserveOrder: false));
            Assert.Equal([n], m.CollectForwardDeps([n], preserveOrder: false));
            Assert.True(m.HasForwardDeps(((FVarExpr)a).Id));
            Assert.False(m.HasForwardDeps(((FVarExpr)n).Id));
            // A hole whose context has α may depend on it.
            var hole = m.MkFreshExprMVar(nat);
            Assert.True(m.DependsOn(hole, ((FVarExpr)a).Id));
            return 0;
        })));
    }
}
