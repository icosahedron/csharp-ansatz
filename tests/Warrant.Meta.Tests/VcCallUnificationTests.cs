using Warrant.Cic;
using Warrant.Kernel;
using static Warrant.Meta.Tests.InitTerms;
using static Warrant.Meta.Tests.MetaTestSupport;

namespace Warrant.Meta.Tests;

/// <summary>
/// The VC walker's call rules (<c>lean/Warrant/Vc.lean</c>) applied with Warrant's <c>Apply</c> to a callee's contract
/// (#241). <c>Vc.call</c> states the callee's exception postcondition as <c>ClrExn.Allowed</c>, so it does not unify with
/// a contract with <c>Spec.NoThrow</c>, whose exception postcondition is <c>ClrExn.External</c>, while the program is
/// opaque; only <c>Vc.callExternal</c> takes it. When the program is a term that reduces to <c>pure v</c>, such as a
/// verified callee applied to arguments that pass its guard, the two triples are definitionally equal once
/// <c>Std.Do.Triple</c> and the program are unfolded, since the exception half is then never reached: unification finds
/// that, as Lean's lazy delta reduction would, and the kernel admits it. The walker reported this as <c>ok := True</c>
/// (the callee's result instantiated into its own <c>Ensures</c>, <c>r = r</c>); it is not a unifier bug, and the walker
/// chooses <c>Vc.callExternal</c> from the contract's type, so it never relies on this.
/// </summary>
public sealed class VcCallUnificationTests(AttributeSidecarFixture fixture) : IClassFixture<AttributeSidecarFixture>
{
    /// <summary>
    /// <c>σ, [x : ClrM σ Int32,] hx : ⦃⌜True⌝⦄ prog ⦃⇓r => ⌜0 ≤ r⌝; exceptions⦄ ⊢ ⦃⌜True⌝⦄ prog ⦃⇓r => ⌜0 ≤ r⌝; allowed⦄</c>,
    /// with the rule applied to the goal: its unassigned triple premise, <c>hx</c>, and the binders in order. The program is
    /// the opaque <c>x</c>, or with <paramref name="reducible"/> the program <c>pure 1</c>.
    /// </summary>
    private (MetaM M, MVarId Premise, FVarExpr Hx, FVarExpr[] Binders) CallSite(string rule, string exceptions, bool reducible = false)
    {
        var m = fixture.NewMeta();
        m.DebugCheckAssignments = true;
        Expr Statement(Expr sigma, Expr prog, Expr[] before)
        {
            var truth = ClrTerms.Pure(sigma, C("True"));
            var callee = ClrTerms.Triple(m, sigma, Int32T, prog, truth,
                ClrTerms.Post(m, sigma, Int32T, r => ClrTerms.Le(Int32Lit(0), r), exceptions));
            return m.WithLocalDeclD(N("hx"), callee, hx =>
                m.MkForallFVars([sigma, .. before, hx], ClrTerms.Triple(m, sigma, Int32T, prog, truth,
                    ClrTerms.Post(m, sigma, Int32T, r => ClrTerms.Le(Int32Lit(0), r)))));
        }
        var statement = m.WithLocalDeclD(N("σ"), ClrTerms.TypeT, sigma => reducible
            ? Statement(sigma, ClrTerms.PureM(m, sigma, Int32T, Int32Lit(1)), [])
            : m.WithLocalDeclD(N("x"), Expr.App(ClrTerms.M(sigma), Int32T), x => Statement(sigma, x, [x])));
        var root = m.MkFreshExprSyntheticOpaqueMVar(statement);
        var (fvars, goal) = m.IntroN(root.Id, reducible ? 2 : 3);
        var premise = m.ApplyConst(goal, N(rule))
            .First(g => !m.MCtx.IsAssigned(g) && m.InstantiateMVars(m.GetMVarType(g)).GetAppFn() is ConstExpr { Name: var n } && n == N("Std.Do.Triple"));
        var binders = fvars.Select(Expr.FVar).ToArray();
        return (m, premise, binders[^1], binders);
    }

    [Fact]
    public void VcCallDoesNotUnifyWithAContractWhoseExceptionsAreExternalOverAnOpaqueProgram()
    {
        var (m, premise, hx, _) = CallSite("Warrant.Vc.call", "Warrant.ClrExn.External");
        var saved = m.SaveState();
        IReadOnlyList<MVarId>? left = null;
        try
        {
            left = m.Apply(premise, hx, "hx");
        }
        catch (MetaException)
        {
            m.Restore(saved);
        }
        Assert.True(left is null, left is null ? "" : $"Apply succeeded: {m.InstantiateMVars(m.GetMVarType(premise))}");
        Assert.False(m.MCtx.IsAssigned(premise));
    }

    [Fact]
    public void VcCallExternalUnifiesWithAContractWhoseExceptionsAreExternal()
    {
        var (m, premise, hx, _) = CallSite("Warrant.Vc.callExternal", "Warrant.ClrExn.External");
        Assert.All(m.Apply(premise, hx, "hx"), g => Assert.True(m.MCtx.IsAssigned(g)));
    }

    [Fact]
    public void VcCallUnifiesWithAContractWhoseExceptionsAreAllowed()
    {
        var (m, premise, hx, _) = CallSite("Warrant.Vc.call", "Warrant.ClrExn.Allowed");
        Assert.All(m.Apply(premise, hx, "hx"), g => Assert.True(m.MCtx.IsAssigned(g)));
    }

    /// <summary>
    /// #241: over <c>pure 1</c>, which never raises, <c>Vc.call</c>'s premise is definitionally equal to the
    /// <c>External</c> contract once both triples unfold, so <c>Apply</c> succeeds; the kernel admits the assignment, so it
    /// is a solution, not a unifier bug.
    /// </summary>
    [Fact]
    public void VcCallUnifiesWithAnExternalContractOverAProgramThatReducesToPureAndTheKernelAdmitsIt()
    {
        var (m, premise, hx, binders) = CallSite("Warrant.Vc.call", "Warrant.ClrExn.External", reducible: true);
        var premiseExpr = Expr.MVar(premise);
        Assert.All(m.Apply(premise, hx, "hx"), g => Assert.True(m.MCtx.IsAssigned(g)));
        var (statement, proof) = m.WithContext(premise, () =>
            (m.MkForallFVars(binders, m.InstantiateMVars(m.GetMVarType(premise))), m.MkLambdaFVars(binders, m.InstantiateMVars(premiseExpr))));
        Assert.False(proof.HasExprMVar || proof.HasLevelMVar || proof.HasFVar, $"proof is not ground: {proof}");
        KernelThread.Run(() => Kernel.Kernel.Add(fixture.Bundle.Fork(), new TheoremDecl(new TheoremInfo(N("VcCallOverPure"), [], statement, proof, [N("VcCallOverPure")]))));
    }
}
