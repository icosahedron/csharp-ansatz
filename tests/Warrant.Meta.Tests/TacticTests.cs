using Warrant.Cic;
using Warrant.Kernel;
using static Warrant.Meta.Tests.MetaTestSupport;

namespace Warrant.Meta.Tests;

/// <summary>
/// The basic tactics (U11, KTD6) on goals over the semantics bundle's Init constants: each builds a term, and the term the
/// goal instantiates to is checked by the kernel, so a tactic is right only when the kernel agrees.
/// </summary>
public sealed class TacticTests(SemanticsBundleFixture bundle) : IClassFixture<SemanticsBundleFixture>
{
    private static readonly Expr Int32 = Expr.Const(N("Int32"));

    private static Expr Eq(Expr type, Expr a, Expr b) => Expr.App(Expr.Const(N("Eq"), Level.One), type, a, b);

    private static Expr And(Expr a, Expr b) => Expr.App(Expr.Const(N("And")), a, b);

    private static Expr Arrow(Expr a, Expr b) => Expr.Forall(N("h"), a, b);

    private (MetaM Meta, TacticM Tactics, MVarExpr Goal) Start(Expr statement, MetaLimits? limits = null)
    {
        var m = new MetaM(bundle.Env, limits);
        var goal = m.MkFreshExprSyntheticOpaqueMVar(statement);
        return (m, new TacticM(m, [goal.Id]), goal);
    }

    private string Pp(TacticM t) => new GoalPrinter(bundle.Env).PpGoals(t.Meta.MCtx, t.GetUnsolvedGoals());

    private static void Intro(TacticM t, params string[] names) =>
        t.LiftMetaTactic1(g => t.Meta.IntroN(g, Math.Max(1, names.Length), [.. names.Select(N)]).Goal);

    private static Expr Const(TacticM t, string name) => t.Meta.MkConstWithFreshMVarLevels(N(name));

    /// <summary>Instantiates the goal and has the kernel admit <c>theorem t : statement := proof</c> into a fork of the bundle.</summary>
    private void KernelAdmits(MetaM m, MVarExpr goal, Expr statement)
    {
        var proof = m.InstantiateMVars(goal);
        Assert.False(proof.HasExprMVar || proof.HasLevelMVar || proof.HasFVar, $"proof is not ground: {proof}");
        KernelThread.Run(() => Kernel.Kernel.Add(bundle.Fork(), new TheoremDecl(new TheoremInfo(N("t"), [], statement, proof, [N("t")]))));
    }

    [Fact]
    public void IntroThenExactRflProvesReflexivity()
    {
        var statement = Expr.Forall(N("x"), Int32, Eq(Int32, Expr.BVar(0), Expr.BVar(0)));
        var (m, t, goal) = Start(statement);

        Intro(t, "x");
        Assert.Equal("x : Int32\n⊢ x = x", Pp(t));
        t.Exact(Const(t, "rfl"));

        Assert.Empty(t.GetUnsolvedGoals());
        KernelAdmits(m, goal, statement);
    }

    [Fact]
    public void IntroApplyEqSymmAndExactAHypothesisProveSymmetry()
    {
        // ∀ (a b : Int32), a = b → b = a
        var statement = Expr.Forall(N("a"), Int32, Expr.Forall(N("b"), Int32,
            Arrow(Eq(Int32, Expr.BVar(1), Expr.BVar(0)), Eq(Int32, Expr.BVar(1), Expr.BVar(2)))));
        var (m, t, goal) = Start(statement);

        t.LiftMetaTactic1(g => m.IntroN(g, 2, [N("a"), N("b")]).Goal);
        Assert.Equal("a b : Int32\n⊢ a = b → b = a", Pp(t));
        Intro(t, "h");
        t.LiftMetaTactic(g => m.ApplyConst(g, N("Eq.symm")));
        Assert.Equal("a b : Int32\nh : a = b\n⊢ a = b", Pp(t));
        t.Exact(t.WithMainContext(() => (Expr)m.GetLocalDeclFromUserName(N("h")).ToExpr()));

        Assert.Empty(t.GetUnsolvedGoals());
        KernelAdmits(m, goal, statement);
    }

    [Fact]
    public void AChainOfIntroApplyAndIntroBuildsAClosedCertificate()
    {
        // ∀ (P : Prop), ((∀ (x : Int32), x = x) → P) → P
        var reflexive = Expr.Forall(N("x"), Int32, Eq(Int32, Expr.BVar(0), Expr.BVar(0)));
        var statement = Expr.Forall(N("P"), Expr.Prop, Arrow(Arrow(reflexive, Expr.BVar(1)), Expr.BVar(1)));
        var (m, t, goal) = Start(statement);

        Intro(t, "P", "f");
        t.LiftMetaTactic(g => m.Apply(g, m.GetLocalDeclFromUserName(N("f")).ToExpr()));
        Assert.Equal("P : Prop\nf : (∀ (x : Int32), x = x) → P\n⊢ ∀ (x : Int32), x = x", Pp(t));
        Intro(t, "x");
        t.Exact(Const(t, "rfl"));

        Assert.Empty(t.GetUnsolvedGoals());
        var proof = m.InstantiateMVars(goal);
        Assert.IsType<LamExpr>(proof);
        KernelAdmits(m, goal, statement);
    }

    [Fact]
    public void ApplyLeavesOneGoalPerUnassignedArgumentInOrder()
    {
        var statement = Expr.Forall(N("a"), Int32, And(Eq(Int32, Expr.BVar(0), Expr.BVar(0)), Eq(Int32, Expr.BVar(0), Expr.BVar(0))));
        var (m, t, goal) = Start(statement);

        Intro(t, "a");
        t.LiftMetaTactic(g => m.ApplyConst(g, N("And.intro")));
        Assert.Equal("case left\na : Int32\n⊢ a = a\n\ncase right\na : Int32\n⊢ a = a", Pp(t));

        t.AllGoals(() => t.Exact(Const(t, "rfl")));
        Assert.Empty(t.GetUnsolvedGoals());
        KernelAdmits(m, goal, statement);
    }

    [Fact]
    public void ExactOfTheWrongTypeReportsATypeMismatchWithBothTypes()
    {
        var (_, t, goal) = Start(Int32);

        var ex = Assert.Throws<TacticException>(() => t.Exact(Const(t, "Nat.zero")));
        Assert.Equal("Tactic `exact` failed: type mismatch\n  Nat.zero\nhas type\n  Nat\nbut is expected to have type\n  Int32", ex.Message);
        Assert.Equal(goal.Id, ex.Goal);
    }

    [Fact]
    public void ApplyThatCannotUnifyNamesTheConclusionAndTheGoal()
    {
        var statement = Expr.Forall(N("a"), Int32, And(Eq(Int32, Expr.BVar(0), Expr.BVar(0)), Eq(Int32, Expr.BVar(0), Expr.BVar(0))));
        var (m, t, _) = Start(statement);
        Intro(t, "a");

        var ex = Assert.Throws<TacticException>(() => t.LiftMetaTactic(g => m.ApplyConst(g, N("Eq.symm"))));
        Assert.StartsWith("Tactic `apply` failed: could not unify the conclusion of 'Eq.symm'\n  ", ex.Message, StringComparison.Ordinal);
        Assert.Contains("with the goal\n  a = a ∧ a = a", ex.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ApplyFailsClearlyWhenAnInstanceArgumentStaysUnassigned()
    {
        // of_decide_eq_true : ∀ {p : Prop} [inst : Decidable p], decide p = true → p. The goal fixes p but not inst, which
        // only instance synthesis (U16) could find.
        var max = Expr.Const(N("Int32.maxValue"));
        var (m, t, _) = Start(Eq(Int32, max, max));

        var ex = Assert.Throws<TacticException>(() => t.LiftMetaTactic(g => m.ApplyConst(g, N("of_decide_eq_true"))));
        Assert.StartsWith("Tactic `apply` failed: failed to synthesize instance\n  Decidable (", ex.Message, StringComparison.Ordinal);
        Assert.EndsWith("instance synthesis is not available yet, so an instance argument must be determined by the goal", ex.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void IntroWithoutABinderFails()
    {
        var (_, t, _) = Start(Eq(Int32, Expr.Const(N("Int32.maxValue")), Expr.Const(N("Int32.maxValue"))));

        var ex = Assert.Throws<TacticException>(() => Intro(t, "x"));
        Assert.Equal("Tactic `introN` failed: There are no additional binders or `let` bindings in the goal to introduce", ex.Message);
    }

    [Fact]
    public void IntroWithoutANameKeepsTheBindersName()
    {
        var (_, t, _) = Start(Expr.Forall(N("amount"), Int32, Eq(Int32, Expr.BVar(0), Expr.BVar(0))));

        Intro(t);
        Assert.Equal("amount : Int32\n⊢ amount = amount", Pp(t));
    }

    [Fact]
    public void AssumptionAndReflCloseTheirGoals()
    {
        var statement = Expr.Forall(N("a"), Int32, Arrow(Eq(Int32, Expr.BVar(0), Expr.BVar(0)), And(Eq(Int32, Expr.BVar(1), Expr.BVar(1)), Eq(Int32, Expr.BVar(1), Expr.BVar(1)))));
        var (m, t, goal) = Start(statement);

        Intro(t, "a", "h");
        t.LiftMetaTactic(g => m.ApplyConst(g, N("And.intro")));
        t.LiftMetaFinishingTactic(m.Assumption);
        t.LiftMetaFinishingTactic(m.Refl);

        Assert.Empty(t.GetUnsolvedGoals());
        KernelAdmits(m, goal, statement);
        var (other, _, int32Goal) = Start(Int32);
        Assert.Throws<TacticException>(() => other.Assumption(int32Goal.Id));
    }

    [Fact]
    public void UnfoldReplacesADefinitionByItsBodyThroughId()
    {
        // Int32.maxValue: an Init definition with no arguments.
        var max = Expr.Const(N("Int32.maxValue"));
        var statement = Eq(Int32, max, max);
        var (m, t, goal) = Start(statement);

        t.LiftMetaTactic1(g => m.UnfoldTarget(g, N("Int32.maxValue")));
        var target = m.InstantiateMVars(m.GetMVarType(t.GetMainGoal()));
        Assert.False(target.ToString().Contains("Int32.maxValue", StringComparison.Ordinal), target.ToString());
        var assigned = m.MCtx.GetExprAssignment(goal.Id);
        Assert.Equal(N("id"), Assert.IsType<ConstExpr>(assigned!.GetAppFn()).Name);

        t.LiftMetaFinishingTactic(m.Refl);
        KernelAdmits(m, goal, statement);
    }

    [Fact]
    public void UnfoldOfAnAbsentDefinitionFails()
    {
        var (m, t, _) = Start(Eq(Int32, Expr.Const(N("Int32.maxValue")), Expr.Const(N("Int32.maxValue"))));

        var ex = Assert.Throws<TacticException>(() => t.LiftMetaTactic1(g => m.UnfoldTarget(g, N("Int32.minValue"))));
        Assert.StartsWith("Tactic `unfold` failed to unfold `Int32.minValue` in\n  ", ex.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void TryRestoresTheGoalsWhenItsTacticFails()
    {
        var (_, t, _) = Start(Int32);
        var before = t.Goals;

        Assert.False(t.Try(() => t.Exact(Const(t, "Nat.zero"))));
        Assert.Equal(before, t.Goals);
        Assert.True(t.Try(() => t.Exact(Const(t, "Int32.maxValue"))));
        Assert.Empty(t.GetUnsolvedGoals());
    }

    [Fact]
    public void TryDoesNotHideRunningOutOfFuel()
    {
        var (_, t, _) = Start(Int32, new MetaLimits(3));

        Assert.Throws<MetaResourceException>(() => t.Try(() =>
        {
            while (true)
            {
                t.Step();
            }
        }));
    }

    [Fact]
    public void AllGoalsFailsWhenItsTacticFailsOnAnyGoal()
    {
        var statement = Expr.Forall(N("a"), Int32, And(Eq(Int32, Expr.BVar(0), Expr.BVar(0)), Expr.Const(N("False"))));
        var (m, t, _) = Start(statement);
        Intro(t, "a");
        t.LiftMetaTactic(g => m.ApplyConst(g, N("And.intro")));

        Assert.Throws<TacticException>(() => t.AllGoals(() => t.Exact(Const(t, "rfl"))));
    }
}
