using Warrant.Cic;
using Warrant.Kernel;
using static Warrant.Meta.Tests.InitTerms;
using static Warrant.Meta.Tests.MetaTestSupport;

namespace Warrant.Meta.Tests;

/// <summary>
/// Instance resolution over the sidecar's instances (plan U16, KTD10; docs/m5a/05 "Instances"), as
/// Lean 4.35.0 resolves the same problems.
/// </summary>
public sealed class InstanceTests(AttributeSidecarFixture fixture) : IClassFixture<AttributeSidecarFixture>
{
    private static readonly Expr IntT = C("Int");

    private MetaM NewMeta()
    {
        var m = fixture.NewMeta();
        m.DebugCheckAssignments = true;
        return m;
    }

    private static Expr Decidable(Expr p) => Expr.App(C("Decidable"), p);

    private static Expr Int32Le(Expr a, Expr b) => Expr.App(C("LE.le", Level.Zero), Int32T, C("instLEInt32"), a, b);

    [Fact]
    public void DecidableLeAtInt32IsInt32DecLe()
    {
        var m = NewMeta();
        m.WithLocalDeclD(N("a"), Int32T, a => m.WithLocalDeclD(N("b"), Int32T, b =>
        {
            var result = m.SynthInstance(Decidable(Int32Le(a, b)));
            Assert.Equal(Expr.App(C("Int32.decLe"), a, b), result);
            return 0;
        }));
    }

    [Fact]
    public void DecidableEqOnAnOpenEnumGoesThroughItsReducibleAbbreviation()
    {
        var m = NewMeta();
        // An open enum translates to a reducible abbreviation of Int32 (docs/m5a/05).
        var payment = N("Corpus.PaymentResult");
        Kernel.Kernel.Add(m.Env, new DefinitionDecl(new DefinitionInfo(
            payment, [], Expr.Sort(Level.One), Int32T, ReducibilityHints.Abbrev, DefinitionSafety.Safe, [payment])));
        var paymentT = Expr.Const(payment);
        var query = Expr.App(C("DecidableEq", Level.One), paymentT);

        // Semireducible, the abbreviation hides Int32 from instance resolution.
        Assert.Null(m.SynthInstance(query));

        m.Attributes.SetReducibilityStatus(payment, ReducibilityStatus.Reducible);
        Assert.Equal(C("instDecidableEqInt32"), m.SynthInstance(query));
        m.WithLocalDeclD(N("x"), paymentT, x => m.WithLocalDeclD(N("y"), paymentT, y =>
        {
            var eq = Expr.App(C("Eq", Level.One), paymentT, x, y);
            Assert.Equal(Expr.App(C("instDecidableEqInt32"), x, y), m.SynthInstance(Decidable(eq)));
            return 0;
        }));
    }

    [Fact]
    public void OfNatInt32FiveIsInt32InstOfNat()
    {
        var m = NewMeta();
        var query = Expr.App(C("OfNat", Level.Zero), Int32T, Expr.NatLit(5));
        var result = m.SynthInstance(query);
        Assert.Equal(Expr.App(C("Int32.instOfNat"), Expr.NatLit(5)), result);
        Assert.True(m.IsDefEq(m.InferType(result!), query));
    }

    [Fact]
    public void AnOutParameterIsAssignedByTheInstanceFound()
    {
        var m = NewMeta();
        // HAdd Int Int ?γ, as elaborating `a + b` at Int poses it.
        var w = m.MkFreshLevelMVar();
        var gamma = m.MkFreshExprMVar(Expr.Sort(Level.Succ(w)));
        var query = Expr.App(Expr.Const(N("HAdd"), Level.Zero, Level.Zero, w), IntT, IntT, gamma);
        var result = m.SynthInstance(query);
        Assert.Equal(Expr.App(C("instHAdd", Level.Zero), IntT, C("Int.instAdd")), m.InstantiateMVars(result!));
        Assert.Equal(IntT, m.InstantiateMVars(gamma));
        Assert.Equal(Level.Zero, m.InstantiateLevelMVars(w));
    }

    [Fact]
    public void ASearchBeyondTheDepthBoundFailsCleanly()
    {
        var m = NewMeta();
        // instance loop {p : Prop} [Decidable p] : Decidable p, tried before every other instance:
        // each subgoal is the goal again.
        var loop = N("Corpus.loopDecidable");
        var p = N("p");
        var type = Expr.Forall(p, Expr.Prop, Expr.Forall(N("inst"), Decidable(Expr.BVar(0)), Decidable(Expr.BVar(1)), BinderInfo.InstImplicit), BinderInfo.Implicit);
        var value = Expr.Lam(p, Expr.Prop, Expr.Lam(N("inst"), Decidable(Expr.BVar(0)), Expr.BVar(0), BinderInfo.InstImplicit), BinderInfo.Implicit);
        Kernel.Kernel.Add(m.Env, new DefinitionDecl(new DefinitionInfo(loop, [], type, value, ReducibilityHints.Regular(1), DefinitionSafety.Safe, [loop])));
        m.Attributes.AddInstance(loop, N("Decidable"), priority: 2000);
        m.SynthInstanceLimits = new SynthInstanceLimits(MaxDepth: 8);

        m.WithLocalDeclD(N("q"), Expr.Prop, q =>
        {
            // No instance decides an opaque proposition: the loop is cut at depth 8 and the search fails.
            Assert.Null(m.SynthInstance(Decidable(q)));
            // The loop is still tried first, and bottoms out in instDecidableTrue at the bound.
            Assert.NotNull(m.SynthInstance(Decidable(C("True"))));
            return 0;
        });
    }

    [Fact]
    public void UnificationSynthesizesAPendingInstance()
    {
        var m = NewMeta();
        // @decide (2 ≤ 3) ?inst =?= true: decide is stuck on ?inst until it is synthesized.
        var le = Expr.App(C("LE.le", Level.Zero), Nat, C("instLENat"), NatLit(2), NatLit(3));
        var inst = m.MkFreshExprMVar(Decidable(le), MetavarKind.Synthetic);
        var decide = Expr.App(C("Decidable.decide"), le, inst);
        Assert.True(m.WithDefault(() => m.IsDefEq(decide, C("Bool.true"))));
        Assert.Equal(Expr.App(C("Nat.decLe"), NatLit(2), NatLit(3)), m.InstantiateMVars(inst));
    }
}
