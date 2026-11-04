using Warrant.Cic;
using Warrant.Kernel;
using static Warrant.Meta.Tests.InitTerms;
using static Warrant.Meta.Tests.MetaTestSupport;

namespace Warrant.Meta.Tests;

/// <summary>
/// The simplifier over the bundle and the sidecar (plan U17, KTD11; docs/m5a/05): the structural simprocs and the goal
/// plumbing for hypotheses. Each proof is checked by the kernel. The scripts that use <c>Tactic.Simp</c> are tested
/// through the engine (Warrant.Engine.Tests, "simp").
/// </summary>
public sealed class SimpTests(AttributeSidecarFixture fixture) : IClassFixture<AttributeSidecarFixture>
{
    private static readonly Expr TrueP = C("True");

    private MetaM NewMeta()
    {
        var m = fixture.NewMeta();
        m.DebugCheckAssignments = true;
        return m;
    }

    private static SimpContext Defaults(MetaM m) => DefaultSimpSet.Context(m, SimpConfig.Default);

    private static Expr Ite(MetaM m, Expr c, Expr a, Expr b) =>
        Expr.App(C("ite", Level.One), Int32T, c, m.SynthInstanceOrThrow(Expr.App(C("Decidable"), c)), a, b);

    private static Expr Int32Le(Expr a, Expr b) => Expr.App(C("LE.le", Level.Zero), Int32T, C("instLEInt32"), a, b);

    [Theory]
    [InlineData(false, "ite_eq_left_of_eq_true")] // if True then a else b
    [InlineData(true, "ite_eq_right_of_eq_false")] // if ¬True then a else b: not_true_eq_false, then reduceIte
    public void ReduceIteRewritesAnIfWhoseConditionSimplifiesToTrueOrFalse(bool negated, string lemma)
    {
        var m = NewMeta();
        m.WithLocalDeclD(N("a"), Int32T, a => m.WithLocalDeclD(N("b"), Int32T, b =>
        {
            var c = negated ? Expr.App(C("Not"), TrueP) : TrueP;
            var e = Ite(m, c, a, b);
            var r = new Simplifier(m, Defaults(m)).Run(e);
            Assert.Equal(negated ? b : a, r.Expr);
            Assert.NotNull(r.Proof);
            Assert.Contains(lemma, r.Proof.ToString(), StringComparison.Ordinal);
            Admit(m, "ReduceIte", [a, b], m.MkEq(e, r.Expr), r.Proof);
            return 0;
        }));
    }

    [Fact]
    public void AHypothesisThatSimplifiesToFalseClosesTheGoal()
    {
        // `simp at *` with h : x ≤ 0 ∧ False: and_false turns h into False, which closes x = 5 through Eq.mp and False.elim.
        var m = NewMeta();
        m.WithLocalDeclD(N("x"), Int32T, x => m.WithLocalDeclD(N("h"), Expr.App(C("And"), Int32Le(x, Int32Lit(0)), C("False")), h =>
        {
            var target = Expr.App(C("Eq", Level.One), Int32T, x, Int32Lit(5));
            var goal = m.MkFreshExprSyntheticOpaqueMVar(target);
            Assert.Null(m.SimpAll(goal.Id, Defaults(m)));
            var proof = m.InstantiateMVars(goal);
            Assert.Contains("False.elim", proof.ToString(), StringComparison.Ordinal);
            Assert.Contains("Eq.mp", proof.ToString(), StringComparison.Ordinal);
            Admit(m, "FromFalse", [x, h], target, proof);
            return 0;
        }));
    }

    [Fact]
    public void AHypothesisThatSimplifiesIsReplacedAndTheGoalStays()
    {
        // h : x ≤ 0 ∧ True becomes h : x ≤ 0 (and_true); the target, which simp cannot change, stays.
        var m = NewMeta();
        m.WithLocalDeclD(N("x"), Int32T, x => m.WithLocalDeclD(N("h"), Expr.App(C("And"), Int32Le(x, Int32Lit(0)), TrueP), h =>
        {
            var target = Expr.App(C("Eq", Level.One), Int32T, x, Int32Lit(5));
            var goal = m.MkFreshExprSyntheticOpaqueMVar(target);
            var result = m.SimpAll(goal.Id, Defaults(m));
            Assert.NotNull(result);
            var newH = Assert.Single(result.FVarIds);
            m.WithContext(result.Goal, () =>
            {
                var decl = m.GetLocalDecl(newH);
                Assert.Equal("h", decl.UserName.ToString());
                Assert.Equal(Int32Le(x, Int32Lit(0)), decl.Type);
                Assert.Equal(target, m.GetMVarType(result.Goal));
                return 0;
            });
            return 0;
        }));
    }

    /// <summary>Admits <c>theorem name : ∀ xs, type := fun xs => proof</c> into <paramref name="m"/>'s environment.</summary>
    private static void Admit(MetaM m, string name, Expr[] xs, Expr type, Expr proof)
    {
        var closedType = m.MkForallFVars(xs, m.InstantiateMVars(type));
        var closedProof = m.MkLambdaFVars(xs, m.InstantiateMVars(proof));
        Assert.False(closedProof.HasExprMVar || closedProof.HasLevelMVar || closedProof.HasFVar, $"proof is not ground: {closedProof}");
        Kernel.Kernel.Add(m.Env, new TheoremDecl(new TheoremInfo(N(name), [], closedType, closedProof, [N(name)])));
    }
}
