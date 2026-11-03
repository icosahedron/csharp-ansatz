using Warrant.Cic;
using Warrant.Kernel;
using static Warrant.Meta.Tests.InitTerms;
using static Warrant.Meta.Tests.MetaTestSupport;

namespace Warrant.Meta.Tests;

/// <summary>
/// Meta's <c>isDefEq</c>: assignment, Miller patterns, transparency, proof irrelevance and
/// backtracking (plan U6, KTD3, KTD5; docs/m5a/02), over the bundle and the attribute sidecar.
/// Every test runs with the kernel check of assignments on.
/// </summary>
public sealed class DefEqTests(AttributeSidecarFixture fixture) : IClassFixture<AttributeSidecarFixture>
{
    private MetaM NewMeta()
    {
        var m = fixture.NewMeta();
        m.DebugCheckAssignments = true;
        return m;
    }

    [Fact]
    public void AnOffsetAssignsTheMetavariable()
    {
        var m = NewMeta();
        m.WithLocalDeclD(N("x"), Nat, x =>
        {
            var mv = m.MkFreshExprMVar(Nat);
            Assert.True(m.IsDefEq(NatAdd(mv, NatLit(1)), NatAdd(x, NatLit(1))));
            Assert.Equal(x, m.InstantiateMVars(mv));
            return 0;
        });
    }

    [Fact]
    public void AMillerPatternAssignsALambda()
    {
        var m = NewMeta();
        // ?f : Nat → Nat lives outside x's scope, so ?f x =?= g x x is a pattern.
        var f = m.MkFreshExprMVar(Expr.Forall(N("a"), Nat, Nat));
        var g = C("Nat.add");
        m.WithLocalDeclD(N("x"), Nat, x =>
        {
            Assert.True(m.IsDefEq(Expr.App(f, x), Expr.App(g, x, x)));
            return 0;
        });
        Assert.Equal(Expr.Lam(N("x"), Nat, Expr.App(g, Expr.BVar(0), Expr.BVar(0))), m.InstantiateMVars(f));
    }

    [Fact]
    public void AtReducibleGtMatchesLtButInt32AddStaysFolded()
    {
        var m = NewMeta();
        m.WithLocalDeclD(N("a"), Int32T, a => m.WithLocalDeclD(N("b"), Int32T, b =>
        {
            var gt = Expr.App(C("GT.gt", Level.Zero), Int32T, C("instLTInt32"), a, b);
            var lt = Expr.App(C("LT.lt", Level.Zero), Int32T, C("instLTInt32"), b, a);
            Assert.True(m.WithReducible(() => m.IsDefEq(gt, lt)));

            // Int32.add a b =?= Int32.add b a needs unfolding; at reducible it is simply false, at
            // default both sides unfold and are still different.
            var ab = Expr.App(C("Int32.add"), a, b);
            Assert.False(m.WithReducible(() => m.IsDefEq(ab, Expr.App(C("Int32.add"), b, a))));
            // ?m + b =?= a + b is solved without unfolding Int32.add.
            var mv = m.MkFreshExprMVar(Int32T);
            Assert.True(m.WithReducible(() => m.IsDefEq(Int32Add(mv, b), Int32Add(a, b))));
            Assert.Equal(a, m.InstantiateMVars(mv));
            return 0;
        }));
    }

    [Fact]
    public void AtDefaultIncrementOf41Is42()
    {
        var m = NewMeta();
        // [Verified] static int Increment(int x) => x + 1; as M4 translates it.
        var name = N("Corpus.Increments.Increment");
        var x = N("x");
        Kernel.Kernel.Add(m.Env, new DefinitionDecl(new DefinitionInfo(
            name, [], Expr.Forall(x, Int32T, Int32T), Expr.Lam(x, Int32T, Int32Add(Expr.BVar(0), Int32Lit(1))),
            ReducibilityHints.Regular(1), DefinitionSafety.Safe, [name])));
        var lhs = Expr.App(Expr.Const(name), Int32Lit(41));
        Assert.True(m.WithDefault(() => m.IsDefEq(lhs, Int32Lit(42))));
        Assert.False(m.WithDefault(() => m.IsDefEq(lhs, Int32Lit(41))));
        // A user definition is semireducible: at reducible it does not unfold.
        Assert.False(m.WithReducible(() => m.IsDefEq(lhs, Int32Lit(42))));
    }

    [Fact]
    public void ATheoremIsNotUnfoldedToUnify()
    {
        var m = NewMeta();
        // Nat.le_refl 3 is the theorem `Nat.le.refl`; the two proofs of 3 ≤ 3 unify by proof
        // irrelevance, never by unfolding the theorem, which isDefEq does not do at any transparency.
        var thm = Expr.App(C("Nat.le_refl"), NatLit(3));
        var refl = Expr.App(C("Nat.le.refl"), NatLit(3));
        Assert.Null(m.WithTransparency(TransparencyMode.All, () => m.UnfoldDefinition(thm)));
        Assert.True(m.WithTransparency(TransparencyMode.All, () => m.IsDefEq(thm, refl)));
        m.WithConfig(c => c with { ProofIrrelevance = false, Transparency = TransparencyMode.All }, () =>
        {
            Assert.False(m.IsDefEq(thm, refl));
            return 0;
        });
    }

    [Fact]
    public void TwoProofsOfTheSamePropositionAreDefEq()
    {
        var m = NewMeta();
        Assert.True(m.WithReducible(() => m.IsDefEq(C("trivial"), C("True.intro"))));
        m.WithLocalDeclD(N("p"), Expr.Prop, p => m.WithLocalDeclD(N("h1"), p, h1 => m.WithLocalDeclD(N("h2"), p, h2 =>
        {
            Assert.True(m.IsDefEq(h1, h2));
            Assert.False(m.WithConfig(c => c with { ProofIrrelevance = false }, () => m.IsDefEq(h1, h2)));
            return 0;
        })));
    }

    [Fact]
    public void AFailedUnificationLeavesTheContextUnchanged()
    {
        var m = NewMeta();
        m.WithLocalDeclD(N("x"), Nat, x => m.WithLocalDeclD(N("y"), Nat, y =>
        {
            var mv = m.MkFreshExprMVar(Nat);
            var before = m.SaveState();
            // ?m := x is made for the first argument, then x =?= y fails and it is rolled back.
            var eq = C("Eq", Level.One);
            Assert.False(m.IsDefEq(Expr.App(eq, Nat, mv, mv), Expr.App(eq, Nat, x, y)));
            Assert.Same(before.MCtx, m.MCtx);
            Assert.Same(before.Postponed, m.Postponed);
            Assert.False(m.IsAssigned(mv.Id));
            // The same subproblem succeeds on its own, and stays assigned.
            Assert.True(m.IsDefEq(Expr.App(eq, Nat, mv, x), Expr.App(eq, Nat, x, x)));
            Assert.Equal(x, m.InstantiateMVars(mv));
            return 0;
        }));
    }

    [Fact]
    public void UniverseMetavariablesAreAssigned()
    {
        var m = NewMeta();
        var u = m.MkFreshLevelMVar();
        Assert.True(m.IsDefEq(Expr.Sort(Level.Succ(u)), Expr.Sort(Level.Succ(Level.One))));
        Assert.Equal(Level.One, m.InstantiateLevelMVars(u));
        Assert.False(m.IsDefEq(Expr.Prop, Expr.Type));
    }

    [Fact]
    public void GoalsAreNotAssignedByUnificationUnlessAllowed()
    {
        var m = NewMeta();
        var goal = m.MkFreshExprMVar(Nat, MetavarKind.SyntheticOpaque);
        Assert.False(m.IsDefEq(goal, NatLit(1)));
        Assert.True(m.WithAssignableSyntheticOpaque(() => m.IsDefEq(goal, NatLit(1))));
        Assert.Equal(NatLit(1), m.InstantiateMVars(goal));
    }

    [Fact]
    public void TheDebugFlagCatchesAnIllTypedAssignment()
    {
        var m = NewMeta();
        var mv = m.MkFreshExprMVar(Nat);
        var ex = Assert.Throws<MetaException>(() => m.Assign(mv.Id, C("Bool.true")));
        Assert.Contains("ill-typed assignment", ex.Message, StringComparison.Ordinal);
        Assert.False(m.IsAssigned(mv.Id));

        // In a local context too, and a well-typed value passes.
        m.WithLocalDeclD(N("b"), C("Bool"), b =>
        {
            var k = m.MkFreshExprMVar(Nat);
            Assert.Throws<MetaException>(() => m.Assign(k.Id, b));
            m.Assign(k.Id, NatAdd(NatLit(1), NatLit(2)));
            return 0;
        });

        // Without the flag, Assign does no checks (as Lean's MVarId.assign).
        var unchecked_ = fixture.NewMeta();
        var mv2 = unchecked_.MkFreshExprMVar(Nat);
        unchecked_.Assign(mv2.Id, C("Bool.true"));
        Assert.True(unchecked_.IsAssigned(mv2.Id));
    }

    [Fact]
    public void CheckUsesTheKernelOnGroundTerms()
    {
        var m = NewMeta();
        Assert.True(m.IsTypeCorrect(NatAdd(NatLit(1), NatLit(2))));
        Assert.False(m.IsTypeCorrect(Expr.App(C("Nat.succ"), C("Bool.true"))));
        m.WithLocalDeclD(N("x"), Nat, x =>
        {
            Assert.Equal(Nat, m.CheckWithKernel(Expr.App(C("Nat.succ"), x)));
            // With a metavariable, Meta checks it itself.
            var mv = m.MkFreshExprMVar(Nat);
            Assert.True(m.IsTypeCorrect(Expr.App(C("Nat.succ"), mv)));
            Assert.False(m.IsTypeCorrect(Expr.App(C("Nat.succ"), m.MkFreshExprMVar(C("Bool")))));
            return 0;
        });
    }
}
