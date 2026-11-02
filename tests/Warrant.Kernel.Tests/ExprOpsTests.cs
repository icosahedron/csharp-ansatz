using Warrant.Cic;

namespace Warrant.Kernel.Tests;

public class ExprOpsTests
{
    private static readonly Name X = Name.Parse("x");
    private static readonly Expr Nat = Expr.Const(Name.Parse("Nat"));
    private static readonly Expr F = Expr.Const(Name.Parse("f"));
    private static readonly Expr A = Expr.Const(Name.Parse("a"));
    private static readonly Expr B = Expr.Const(Name.Parse("b"));

    [Fact]
    public void InstantiateReplacesAndLowers()
    {
        // f #0 #1 #2 with #0 := a, #1 := b  →  f a b #0
        var e = Expr.App(F, Expr.BVar(0), Expr.BVar(1), Expr.BVar(2));
        Assert.Equal(Expr.App(F, A, B, Expr.BVar(0)), ExprOps.Instantiate(e, [A, B]));
        // InstantiateRev gives the innermost binder the last element.
        Assert.Equal(Expr.App(F, B, A, Expr.BVar(0)), ExprOps.InstantiateRev(e, [A, B]));
    }

    [Fact]
    public void InstantiateLiftsUnderBinders()
    {
        // fun x => f #0 #1   with #0 := #5 (a loose variable)  →  fun x => f #0 #6
        var e = Expr.Lam(X, Nat, Expr.App(F, Expr.BVar(0), Expr.BVar(1)));
        Assert.Equal(Expr.Lam(X, Nat, Expr.App(F, Expr.BVar(0), Expr.BVar(6))), ExprOps.Instantiate(e, Expr.BVar(5)));
    }

    [Fact]
    public void AbstractInvertsInstantiate()
    {
        var x = Expr.FVar(new FVarId(Name.Parse("_t.1")));
        var y = Expr.FVar(new FVarId(Name.Parse("_t.2")));
        var body = Expr.App(F, x, Expr.Lam(X, Nat, Expr.App(F, y, Expr.BVar(0))));
        var abs = ExprOps.Abstract(body, [x, y]);
        Assert.Equal(Expr.App(F, Expr.BVar(1), Expr.Lam(X, Nat, Expr.App(F, Expr.BVar(1), Expr.BVar(0)))), abs);
        Assert.False(abs.HasFVar);
        Assert.Equal(body, ExprOps.InstantiateRev(abs, [x, y]));
    }

    [Fact]
    public void LiftAndLower()
    {
        var e = Expr.Lam(X, Nat, Expr.App(F, Expr.BVar(0), Expr.BVar(1), Expr.BVar(3)));
        var lifted = ExprOps.LiftLooseBVars(e, 0, 2);
        Assert.Equal(Expr.Lam(X, Nat, Expr.App(F, Expr.BVar(0), Expr.BVar(3), Expr.BVar(5))), lifted);
        Assert.Equal(e, ExprOps.LowerLooseBVars(lifted, 2, 2));
        Assert.True(ExprOps.HasLooseBVar(e, 0));
        Assert.True(ExprOps.HasLooseBVar(e, 2));
        Assert.False(ExprOps.HasLooseBVar(e, 1));
    }

    [Fact]
    public void BetaReduction()
    {
        var k = Expr.Lam(X, Nat, Expr.Lam(Name.Parse("y"), Nat, Expr.BVar(1))); // fun x y => x
        Assert.Equal(A, ExprOps.HeadBetaReduce(Expr.App(k, A, B)));
        Assert.Equal(Expr.App(A, Expr.Const(Name.Parse("c"))), ExprOps.HeadBetaReduce(Expr.App(k, A, B, Expr.Const(Name.Parse("c")))));
        Assert.Equal(A, ExprOps.CheapBetaReduce(Expr.App(k, A, B)));
        var dup = Expr.Lam(X, Nat, Expr.App(F, Expr.BVar(0), Expr.BVar(0)));
        Assert.Equal(Expr.App(dup, A), ExprOps.CheapBetaReduce(Expr.App(dup, A))); // needs substitution: left alone
    }

    [Fact]
    public void InstantiateLevelParams()
    {
        var u = Name.Parse("u");
        var e = Expr.Forall(X, Expr.Sort(Level.Param(u)), Expr.Const(Name.Parse("List"), Level.Param(u)));
        var r = ExprOps.InstantiateLevelParams(e, EquatableArray.Create(u), EquatableArray.Create(Level.One));
        Assert.Equal(Expr.Forall(X, Expr.Sort(Level.One), Expr.Const(Name.Parse("List"), Level.One)), r);
        Assert.False(r.HasLevelParam);
    }

    [Fact]
    public void ConsumeTypeAnnotations()
    {
        var opt = Expr.App(Expr.Const(KernelNames.OptParam, Level.One), Nat, A);
        var outer = Expr.App(Expr.Const(KernelNames.OutParam, Level.One), opt);
        Assert.Equal(Nat, ExprOps.ConsumeTypeAnnotations(outer));
        Assert.Same(Nat, ExprOps.ConsumeTypeAnnotations(Nat));
    }

    [Fact]
    public void InferImplicitMarksDependedOnBinders()
    {
        // (α : Type) → (a : α) → α   →   {α : Type} → (a : α) → α
        var t = Expr.Forall(Name.Parse("α"), Expr.Type, Expr.Forall(Name.Parse("a"), Expr.BVar(0), Expr.BVar(1)));
        var r = (ForallExpr)ExprOps.InferImplicit(t, int.MaxValue, strict: true);
        Assert.Equal(BinderInfo.Implicit, r.BinderInfo);
        Assert.Equal(BinderInfo.Default, ((ForallExpr)r.Body).BinderInfo);
    }

    [Fact]
    public void AlphaEqualityIgnoresBinderAnnotations()
    {
        var a = Expr.Lam(X, Nat, Expr.BVar(0));
        var b = Expr.Lam(Name.Parse("y"), Nat, Expr.BVar(0), BinderInfo.Implicit);
        Assert.NotEqual(a, b);
        Assert.True(a.AlphaEquals(b));
        Assert.False(a.AlphaEquals(Expr.Forall(X, Nat, Expr.BVar(0))));
        Assert.True(Expr.AlphaComparer.Equals(a, b));
        Assert.Equal(Expr.AlphaComparer.GetHashCode(a), Expr.AlphaComparer.GetHashCode(b));
    }
}
