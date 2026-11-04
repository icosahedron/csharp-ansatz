using Warrant.Cic;
using Warrant.Kernel;
using static Warrant.Meta.Tests.MetaTestSupport;

namespace Warrant.Meta.Tests;

/// <summary>
/// <c>cases</c> and <c>induction</c> (U14, KTD6, KTD8) on goals over Init types, whose <c>casesOn</c> the bundle has. Each
/// proof the tactics build is checked by the kernel.
/// </summary>
public sealed class CasesTests(AttributeSidecarFixture attributes) : IClassFixture<AttributeSidecarFixture>
{
    private static readonly Expr Bool = Expr.Const(N("Bool"));
    private static readonly Expr Nat = Expr.Const(N("Nat"));

    private static Expr Eq(Expr type, Expr a, Expr b) => Expr.App(Expr.Const(N("Eq"), Level.One), type, a, b);

    private (MetaM Meta, TacticM Tactics, MVarExpr Goal) Start(Expr statement)
    {
        var m = attributes.NewMeta();
        var goal = m.MkFreshExprSyntheticOpaqueMVar(statement);
        return (m, new TacticM(m, [goal.Id]), goal);
    }

    private static string Pp(TacticM t) => new GoalPrinter(t.Meta.Env).PpGoals(t.Meta.MCtx, t.GetUnsolvedGoals());

    private static void Intro(TacticM t, params string[] names) =>
        t.LiftMetaTactic1(g => t.Meta.IntroN(g, names.Length, [.. names.Select(N)]).Goal);

    private static FVarId Hyp(TacticM t, string name) => t.WithMainContext(() => t.Meta.GetLocalDeclFromUserName(N(name)).FVarId);

    private static void ExactRfl(TacticM t) => t.Exact(t.Meta.MkConstWithFreshMVarLevels(N("rfl")));

    private static void KernelAdmits(MetaM m, MVarExpr goal, Expr statement)
    {
        var proof = m.InstantiateMVars(goal);
        Assert.False(proof.HasExprMVar || proof.HasLevelMVar || proof.HasFVar, $"proof is not ground: {proof}");
        KernelThread.Run(() => Kernel.Kernel.Add(m.Env, new TheoremDecl(new TheoremInfo(N("t"), [], statement, proof, [N("t")]))));
    }

    [Fact]
    public void CasesOnABoolGivesAFalseGoalAndATrueGoal()
    {
        // ∀ (b : Bool), (b && b) = b
        var statement = Expr.Forall(N("b"), Bool, Eq(Bool, Expr.App(Expr.Const(N("Bool.and")), Expr.BVar(0), Expr.BVar(0)), Expr.BVar(0)));
        var (m, t, goal) = Start(statement);
        Intro(t, "b");

        var subgoals = t.WithMainContext(() => m.Cases(t.GetMainGoal(), Hyp(t, "b")));
        t.ReplaceMainGoal(subgoals.Select(s => s.MVarId));

        Assert.Equal("case false\n⊢ Bool.and Bool.false Bool.false = Bool.false\n\ncase true\n⊢ Bool.and Bool.true Bool.true = Bool.true", Pp(t));
        Assert.Equal([N("Bool.false"), N("Bool.true")], subgoals.Select(s => s.CtorName));
        Assert.All(subgoals, s => Assert.Empty(s.Fields));
        t.AllGoals(() => ExactRfl(t));
        KernelAdmits(m, goal, statement);
        // The proof eliminates with Bool.casesOn, with the motive abstracted from the target.
        Assert.Contains("Bool.casesOn", m.InstantiateMVars(goal).ToString(), StringComparison.Ordinal);
    }

    [Fact]
    public void InductionOnANatGivesAZeroGoalAndASuccessorGoalWithItsHypothesis()
    {
        // ∀ (n : Nat), Nat.add 0 n = n, which needs the induction hypothesis.
        Expr Add0(Expr x) => Expr.App(Expr.Const(N("Nat.add")), Expr.Const(N("Nat.zero")), x);
        var statement = Expr.Forall(N("n"), Nat, Eq(Nat, Add0(Expr.BVar(0)), Expr.BVar(0)));
        var (m, t, goal) = Start(statement);
        Intro(t, "n");

        var subgoals = t.WithMainContext(() => m.Induction(t.GetMainGoal(), Hyp(t, "n"), N("Nat.rec")));
        t.ReplaceMainGoal(subgoals.Select(s => s.MVarId));

        Assert.Equal(
            "case zero\n⊢ Nat.add Nat.zero Nat.zero = Nat.zero\n\ncase succ\nn : Nat\nn_ih : Nat.add Nat.zero n = n\n⊢ Nat.add Nat.zero (Nat.succ n) = Nat.succ n",
            Pp(t));
        Assert.Empty(subgoals[0].Fields);
        Assert.Equal(2, subgoals[1].Fields.Length); // n and n_ih
        ExactRfl(t);
        // succ: congrArg Nat.succ n_ih, since Nat.add 0 (Nat.succ n) reduces to Nat.succ (Nat.add 0 n).
        var ih = t.WithMainContext(() => (Expr)m.GetLocalDeclFromUserName(N("n_ih")).ToExpr());
        var n = t.WithMainContext(() => (Expr)m.GetLocalDeclFromUserName(N("n")).ToExpr());
        t.Exact(Expr.App(Expr.Const(N("congrArg"), Level.One, Level.One), Nat, Nat, Add0(n), n, Expr.Const(N("Nat.succ")), ih));

        Assert.Empty(t.GetUnsolvedGoals());
        KernelAdmits(m, goal, statement);
    }

    [Fact]
    public void InductionRevertsAndReintroducesTheHypothesesThatDependOnTheMajorPremise()
    {
        // ∀ (n : Nat), n = n → n = n: h depends on n, so each new goal gets it back.
        var statement = Expr.Forall(N("n"), Nat, Expr.Forall(N("h"), Eq(Nat, Expr.BVar(0), Expr.BVar(0)), Eq(Nat, Expr.BVar(1), Expr.BVar(1))));
        var (m, t, goal) = Start(statement);
        Intro(t, "n", "h");

        var subgoals = t.WithMainContext(() => m.Induction(t.GetMainGoal(), Hyp(t, "n"), N("Nat.rec")));
        t.ReplaceMainGoal(subgoals.Select(s => s.MVarId));

        Assert.Equal(
            "case zero\nh : Nat.zero = Nat.zero\n⊢ Nat.zero = Nat.zero\n\ncase succ\nn : Nat\nn_ih : n = n → n = n\nh : Nat.succ n = Nat.succ n\n⊢ Nat.succ n = Nat.succ n",
            Pp(t));
        Assert.All(subgoals, s => Assert.False(s.Subst.IsEmpty));
        t.AllGoals(() => t.LiftMetaFinishingTactic(m.Assumption));
        KernelAdmits(m, goal, statement);
    }

    [Fact]
    public void CasesOnAnEquationIsNotSupportedYet()
    {
        // ∀ (a b : Nat), a = b → b = a
        var statement = Expr.Forall(N("a"), Nat, Expr.Forall(N("b"), Nat, Expr.Forall(N("h"), Eq(Nat, Expr.BVar(1), Expr.BVar(0)), Eq(Nat, Expr.BVar(1), Expr.BVar(2)))));
        var (m, t, _) = Start(statement);
        Intro(t, "a", "b", "h");

        var ex = Assert.Throws<TacticException>(() => t.WithMainContext(() => m.Cases(t.GetMainGoal(), Hyp(t, "h"))));
        Assert.Equal("Tactic `cases` failed: cases on an indexed family is not supported yet", ex.Message);
    }

    [Fact]
    public void CasesRefusesAGoalWithAnUnassignedMetavariable()
    {
        // ∀ (b : Bool), b = ?x
        var (m, t, _) = Start(Expr.Forall(N("b"), Bool, Expr.Const(N("True"))));
        Intro(t, "b");
        var hole = t.WithMainContext(() => m.MkFreshExprMVar(Bool));
        var withHole = t.WithMainContext(() => m.MkFreshExprSyntheticOpaqueMVar(Eq(Bool, m.GetLocalDeclFromUserName(N("b")).ToExpr(), hole)));
        t.Goals = [withHole.Id];

        var ex = Assert.Throws<TacticException>(() => t.WithMainContext(() => m.Cases(t.GetMainGoal(), Hyp(t, "b"))));
        Assert.Equal("Tactic `cases` failed: the goal has metavariables that are not assigned yet", ex.Message);
    }
}
