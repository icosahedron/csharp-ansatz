using System.Numerics;
using Warrant.Cic;
using static Warrant.Meta.Tests.MetaTestSupport;

namespace Warrant.Meta.Tests;

/// <summary>Terms over the bundle's Init constants, as Lean 4.35.0's elaborator writes them.</summary>
internal static class InitTerms
{
    public static Expr C(string name, params Level[] levels) => Expr.Const(N(name), levels);

    public static Expr Nat { get; } = C("Nat");

    public static Expr Int32T { get; } = C("Int32");

    /// <summary><c>@OfNat.ofNat Nat n (instOfNatNat n)</c>.</summary>
    public static Expr NatLit(BigInteger n) => Expr.App(C("OfNat.ofNat", Level.Zero), Nat, Expr.NatLit(n), Expr.App(C("instOfNatNat"), Expr.NatLit(n)));

    /// <summary><c>@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) a b</c>.</summary>
    public static Expr NatAdd(Expr a, Expr b) =>
        Expr.App(C("HAdd.hAdd", Level.Zero, Level.Zero, Level.Zero), Nat, Nat, Nat, Expr.App(C("instHAdd", Level.Zero), Nat, C("instAddNat")), a, b);

    /// <summary><c>@OfNat.ofNat Int32 n (Int32.instOfNat n)</c>, as M4 translates an <c>int</c> literal.</summary>
    public static Expr Int32Lit(BigInteger n) => Expr.App(C("OfNat.ofNat", Level.Zero), Int32T, Expr.NatLit(n), Expr.App(C("Int32.instOfNat"), Expr.NatLit(n)));

    /// <summary><c>@HAdd.hAdd Int32 Int32 Int32 (@instHAdd Int32 instAddInt32) a b</c>, as M4 translates <c>a + b</c>.</summary>
    public static Expr Int32Add(Expr a, Expr b) =>
        Expr.App(C("HAdd.hAdd", Level.Zero, Level.Zero, Level.Zero), Int32T, Int32T, Int32T, Expr.App(C("instHAdd", Level.Zero), Int32T, C("instAddInt32")), a, b);
}

/// <summary>
/// Meta's <c>whnf</c> at each transparency (plan U6, KTD3, KTD5; docs/m5a/02 "Transparency"), over
/// the bundle and the attribute sidecar. Every test runs with the kernel check of assignments on.
/// </summary>
public sealed class WhnfTests(AttributeSidecarFixture fixture) : IClassFixture<AttributeSidecarFixture>
{
    private MetaM NewMeta()
    {
        var m = fixture.NewMeta();
        m.DebugCheckAssignments = true;
        return m;
    }

    [Fact]
    public void CanUnfoldDefaultIsLeansTable()
    {
        var m = NewMeta();
        // One constant per status, from the sidecar (the facts the loader test pins down).
        var reducible = m.GetConstInfo(N("GT.gt"));
        var instanceReducible = m.GetConstInfo(N("Nat.add"));
        var implicitReducible = m.GetConstInfo(N("Int32.add"));
        var semireducible = m.GetConstInfo(N("Int32.decEq"));
        var irreducible = m.GetConstInfo(N("Nat.gcd"));
        Assert.Equal(ReducibilityStatus.InstanceReducible, m.GetReducibilityStatus(instanceReducible.Name));
        Assert.Equal(ReducibilityStatus.Irreducible, m.GetReducibilityStatus(irreducible.Name));

        // Rows: none, reducible, instances, implicit, default, all.
        // Columns: reducible, instanceReducible, implicitReducible, semireducible, irreducible.
        bool[][] expected =
        [
            [false, false, false, false, false],
            [true, false, false, false, false],
            [true, true, false, false, false],
            [true, true, true, false, false],
            [true, true, true, true, false],
            [true, true, true, true, true],
        ];
        var modes = Enum.GetValues<TransparencyMode>();
        Assert.Equal(6, modes.Length);
        ConstantInfo[] infos = [reducible, instanceReducible, implicitReducible, semireducible, irreducible];
        for (int i = 0; i < modes.Length; i++)
        {
            var cfg = MetaConfig.Default with { Transparency = modes[i] };
            Assert.Equal(expected[i], infos.Select(info => m.CanUnfoldDefault(cfg, info)).ToArray());
        }
        Assert.True(TransparencyMode.None.Lt(TransparencyMode.Reducible));
        Assert.True(TransparencyMode.Instances.Lt(TransparencyMode.Implicit));
        Assert.False(TransparencyMode.All.Lt(TransparencyMode.Default));
    }

    [Fact]
    public void AtReducibleGtUnfoldsButInt32AddDoesNot()
    {
        var m = NewMeta();
        m.WithLocalDeclD(N("a"), InitTerms.Int32T, a => m.WithLocalDeclD(N("b"), InitTerms.Int32T, b =>
        {
            var gt = Expr.App(InitTerms.C("GT.gt", Level.Zero), InitTerms.Int32T, InitTerms.C("instLTInt32"), a, b);
            var lt = Expr.App(InitTerms.C("LT.lt", Level.Zero), InitTerms.Int32T, InitTerms.C("instLTInt32"), b, a);
            Assert.Equal(lt, m.WhnfR(gt));

            var add = Expr.App(InitTerms.C("Int32.add"), a, b);
            Assert.Same(add, m.WhnfR(add));
            Assert.Null(m.WithReducible(() => m.UnfoldDefinition(add)));
            Assert.Null(m.WithReducibleAndInstances(() => m.UnfoldDefinition(add)));
            // Int32.add is implicit-reducible: it unfolds from `implicit` up.
            Assert.NotNull(m.WithImplicit(() => m.UnfoldDefinition(add)));
            Assert.NotNull(m.WithDefault(() => m.UnfoldDefinition(add)));
            return 0;
        }));
    }

    [Fact]
    public void NatAddIsInstanceReducible()
    {
        var m = NewMeta();
        m.WithLocalDeclD(N("x"), InitTerms.Nat, x =>
        {
            var add = Expr.App(InitTerms.C("Nat.add"), x, x);
            Assert.Null(m.WithReducible(() => m.UnfoldDefinition(add)));
            Assert.NotNull(m.WithReducibleAndInstances(() => m.UnfoldDefinition(add)));
            return 0;
        });
    }

    [Fact]
    public void ATheoremNeverUnfolds()
    {
        var m = NewMeta();
        Assert.IsType<TheoremInfo>(m.GetConstInfo(N("Nat.le_refl")));
        var app = Expr.App(InitTerms.C("Nat.le_refl"), InitTerms.NatLit(3));
        foreach (var mode in Enum.GetValues<TransparencyMode>())
        {
            Assert.Null(m.WithTransparency(mode, () => m.UnfoldDefinition(app)));
            Assert.Null(m.WithTransparency(mode, () => m.GetUnfoldableConst(N("Nat.le_refl"))));
            Assert.Same(app, m.WithTransparency(mode, () => m.Whnf(app)));
        }
    }

    [Fact]
    public void WhnfRReducesAnInitMatchThroughItsMatcherInfo()
    {
        var m = NewMeta();
        // Int.neg's `match` on `Int.ofNat n | Int.negSucc n`, compiled to Int.neg.match_1.
        var info = m.GetMatcherInfo(N("Int.neg.match_1"));
        Assert.NotNull(info);
        Assert.Equal((0, 1, 2), (info.NumParams, info.NumDiscrs, info.NumAlts));
        // The sidecar marks it instance-reducible, not reducible.
        Assert.False(m.IsReducible(N("Int.neg.match_1")));

        var motive = Expr.Lam(N("x"), InitTerms.C("Int"), InitTerms.Nat);
        var alt1 = Expr.Lam(N("n"), InitTerms.Nat, Expr.BVar(0));
        var alt2 = Expr.Lam(N("n"), InitTerms.Nat, Expr.App(InitTerms.C("Nat.succ"), Expr.BVar(0)));
        Expr Match(Expr discr) => Expr.App(InitTerms.C("Int.neg.match_1", Level.One), motive, discr, alt1, alt2);

        var e = Match(Expr.App(InitTerms.C("Int.ofNat"), Expr.NatLit(5)));
        // The matcher is not reducible and never delta-unfolds; whnfCore reduces it through its info.
        Assert.Null(m.WithReducible(() => m.UnfoldDefinition(e)));
        Assert.Equal(Expr.NatLit(5), m.WhnfR(e));
        Assert.Equal(Expr.NatLit(5), m.WithReducible(() => m.WhnfCore(e)));

        var e2 = Match(Expr.App(InitTerms.C("Int.negSucc"), Expr.NatLit(5)));
        Assert.Equal(Expr.NatLit(6), m.WhnfR(e2));
    }

    [Fact]
    public void WhnfFollowsAssignedMetavariablesAndReducesNatLiterals()
    {
        var m = NewMeta();
        var mv = m.MkFreshExprMVar(InitTerms.Nat);
        Assert.Same(mv, m.Whnf(mv));
        m.Assign(mv.Id, InitTerms.NatAdd(InitTerms.NatLit(2), InitTerms.NatLit(3)));
        Assert.Equal(Expr.NatLit(5), m.Whnf(mv));
        Assert.Equal(Expr.NatLit(5), m.Whnf(Expr.App(InitTerms.C("Nat.add"), Expr.NatLit(2), Expr.NatLit(3))));
    }

    [Fact]
    public void InferTypeOfAnApplicationInstantiatesThePiType()
    {
        var m = NewMeta();
        Assert.Equal(InitTerms.Nat, m.InferType(InitTerms.NatAdd(InitTerms.NatLit(1), InitTerms.NatLit(2))));
        Assert.Equal(Expr.Prop, m.InferType(Expr.App(InitTerms.C("LT.lt", Level.Zero), InitTerms.Int32T, InitTerms.C("instLTInt32"), InitTerms.Int32Lit(1), InitTerms.Int32Lit(2))));
        Assert.True(m.IsProof(Expr.App(InitTerms.C("Nat.le_refl"), InitTerms.NatLit(3))));
    }
}
