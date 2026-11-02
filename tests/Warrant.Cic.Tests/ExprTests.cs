using System.Diagnostics;
using System.Numerics;
using Warrant.Cic;

namespace Warrant.Cic.Tests;

public class ExprTests
{
    private static readonly Name X = Name.Parse("x");
    private static readonly Name Y = Name.Parse("y");
    private static readonly Expr Nat = Expr.Const(Name.Parse("Nat"));

    [Fact]
    public void LooseBVarRangeTracksBinders()
    {
        Assert.Equal(1, Expr.BVar(0).LooseBVarRange);
        Assert.Equal(3, Expr.BVar(2).LooseBVarRange);
        Assert.Equal(0, Expr.Lam(X, Nat, Expr.BVar(0)).LooseBVarRange);
        Assert.Equal(1, Expr.Lam(X, Nat, Expr.BVar(1)).LooseBVarRange);
        Assert.Equal(2, Expr.Forall(X, Expr.BVar(1), Expr.BVar(0)).LooseBVarRange);
        Assert.Equal(1, Expr.Let(X, Nat, Expr.BVar(0), Expr.BVar(0)).LooseBVarRange);
        Assert.Equal(4, Expr.App(Expr.BVar(3), Expr.BVar(1)).LooseBVarRange);
        Assert.Equal(1, Expr.Proj(Name.Parse("Prod"), 0, Expr.BVar(0)).LooseBVarRange);
        Assert.False(Nat.HasLooseBVars);
    }

    [Fact]
    public void FreeVariableAndLevelParamFlagsPropagate()
    {
        var fvar = Expr.FVar(new FVarId(Name.Parse("_fvar.1")));
        Assert.True(Expr.App(Nat, fvar).HasFVar);
        Assert.False(Expr.App(Nat, Nat).HasFVar);

        var u = Level.Param(Name.Parse("u"));
        Assert.True(Expr.Sort(u).HasLevelParam);
        Assert.True(Expr.Lam(X, Expr.Const(Name.Parse("List"), u), Expr.BVar(0)).HasLevelParam);
        Assert.False(Expr.Prop.HasLevelParam);
    }

    [Fact]
    public void EqualityIsExactButHashIgnoresBinderAnnotations()
    {
        var a = Expr.Lam(X, Nat, Expr.BVar(0));
        var b = Expr.Lam(Y, Nat, Expr.BVar(0));
        var c = Expr.Lam(X, Nat, Expr.BVar(0), BinderInfo.Implicit);
        Assert.Equal(a, Expr.Lam(Name.Parse("x"), Expr.Const(Name.Parse("Nat")), Expr.BVar(0)));
        Assert.NotEqual(a, b);
        Assert.NotEqual(a, c);
        Assert.Equal(a.GetHashCode(), b.GetHashCode());
        Assert.Equal(a.GetHashCode(), c.GetHashCode());
        Assert.NotEqual<Expr>(Expr.Lam(X, Nat, Expr.BVar(0)), Expr.Forall(X, Nat, Expr.BVar(0)));
    }

    [Fact]
    public void LiteralsCompareByValue()
    {
        var big = BigInteger.Pow(2, 200);
        Assert.Equal(Expr.NatLit(big), Expr.NatLit(BigInteger.Pow(2, 200)));
        Assert.NotEqual(Expr.NatLit(big), Expr.NatLit(big + 1));
        Assert.Equal(Expr.StrLit("héllo"), Expr.StrLit("héllo"));
        Assert.Throws<ArgumentOutOfRangeException>(() => Expr.NatLit(-1));
        Assert.Throws<ArgumentOutOfRangeException>(() => Expr.BVar(-1));
    }

    [Fact]
    public void MDataComparesAnnotations()
    {
        var data = new KVMap(EquatableArray.Create(new KVMapEntry("noindent", "true")));
        Assert.Equal(Expr.MData(data, Nat), Expr.MData(new KVMap(EquatableArray.Create(new KVMapEntry("noindent", "true"))), Nat));
        Assert.NotEqual(Expr.MData(data, Nat), Expr.MData(KVMap.Empty, Nat));
    }

    [Fact]
    public void ApplicationSpines()
    {
        var f = Expr.Const(Name.Parse("f"));
        var e = Expr.App(f, Nat, Expr.BVar(0), Expr.Prop);
        Assert.Same(f, e.GetAppFn());
        Assert.Equal(3, e.GetAppNumArgs());
        Assert.Equal([Nat, Expr.BVar(0), Expr.Prop], e.GetAppArgs());
        Assert.Same(f, Expr.App(f, ReadOnlySpan<Expr>.Empty));
    }

    [Fact]
    public void EqualityHandlesVeryDeepTermsWithoutRecursion()
    {
        // Far deeper than any recursive implementation could survive on a 1 MB stack.
        static Expr Build(int depth)
        {
            Expr e = Expr.BVar(0);
            for (int i = 0; i < depth; i++)
            {
                e = Expr.Lam(X, Nat, Expr.App(e, Expr.BVar(0)));
            }
            return e;
        }

        var a = Build(200_000);
        var b = Build(200_000);
        Assert.NotSame(a, b);
        Assert.Equal(a, b);
        Assert.NotEqual(a, Expr.Lam(Y, Nat, ((LamExpr)b).Body));
    }

    [Fact]
    public void EqualityIsLinearOnSharedDags()
    {
        // e(n) = e(n-1) e(n-1): 2^60 nodes as a tree, 61 as a DAG. Two separately built copies
        // must compare in time proportional to the DAG, not the tree.
        static Expr Build(int n)
        {
            Expr e = Nat;
            for (int i = 0; i < n; i++)
            {
                e = Expr.App(e, e);
            }
            return e;
        }

        var a = Build(60);
        var b = Build(60);
        var sw = Stopwatch.StartNew();
        Assert.Equal(a, b);
        Assert.True(sw.Elapsed < TimeSpan.FromSeconds(5), $"comparison took {sw.Elapsed}");
    }

    [Fact]
    public void ToStringIsReadable()
    {
        var e = Expr.Lam(X, Nat, Expr.App(Expr.Const(Name.Parse("Nat.succ")), Expr.BVar(0)), BinderInfo.Implicit);
        Assert.Equal("(fun {x : Nat} => (Nat.succ #0))", e.ToString());
        Assert.Equal("Sort u+1", Expr.Sort(Level.Succ(Level.Param(Name.Parse("u")))).ToString());
        Assert.Equal("Prop", Expr.Prop.ToString());
    }
}
