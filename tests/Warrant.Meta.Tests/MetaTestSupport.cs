using Warrant.Cic;
using Warrant.Kernel;

namespace Warrant.Meta.Tests;

/// <summary>Small builders shared by the Meta tests.</summary>
internal static class MetaTestSupport
{
    public static Name N(string s) => Name.Parse(s);

    public static MetaM NewMeta(MetaLimits? limits = null) => new(new KernelEnvironment(), limits);

    /// <summary>∀ (P : Prop), P → P.</summary>
    public static Expr IdPropType { get; } =
        Expr.Forall(N("P"), Expr.Prop, Expr.Forall(N("h"), Expr.BVar(0), Expr.BVar(1)));

    /// <summary>
    /// Lean's <c>intro</c> in miniature (Lean/Meta/Tactic/Intro.lean 24-31): in the goal's context,
    /// add the binder as a hypothesis, make the body a new goal, and assign the old goal the lambda
    /// that <c>mkLambdaFVars</c> builds over it.
    /// </summary>
    public static (FVarExpr Hyp, MVarId Goal) Intro(MetaM m, MVarId goal, string name) =>
        m.WithContext(goal, () =>
        {
            var type = (ForallExpr)m.InstantiateMVars(m.GetMVarDecl(goal).Type);
            return m.WithLocalDecl(N(name), type.BinderInfo, type.BinderType, x =>
            {
                var newGoal = m.MkFreshExprMVar(ExprOps.Instantiate(type.Body, x), MetavarKind.SyntheticOpaque);
                m.Assign(goal, m.MkLambdaFVars([x], newGoal));
                return (x, newGoal.Id);
            });
        });

    /// <summary>Admits <c>theorem name : type := proof</c> into a fresh environment; throws if the kernel rejects it.</summary>
    public static void KernelAdmits(string name, Expr type, Expr proof)
    {
        Assert.False(proof.HasExprMVar || proof.HasLevelMVar || proof.HasFVar, $"proof is not ground: {proof}");
        Kernel.Kernel.Add(new KernelEnvironment(), new TheoremDecl(new TheoremInfo(N(name), [], type, proof, [N(name)])));
    }
}
