using Warrant.Cic;
using Warrant.Kernel;
using static Warrant.Meta.Tests.InitTerms;
using static Warrant.Meta.Tests.MetaTestSupport;

namespace Warrant.Meta.Tests;

/// <summary>
/// The VC walker's call rules (<c>lean/Warrant/Vc.lean</c>) applied with Warrant's <c>Apply</c> to a callee's contract
/// (#241). <c>Vc.call</c> states the callee's exception postcondition as <c>ClrExn.Allowed</c>, so it does not unify with
/// a contract with <c>Spec.NoThrow</c>, whose exception postcondition is <c>ClrExn.External</c>, while the program is
/// opaque; only <c>Vc.callExternal</c> takes it. When the program is a term that reduces to <c>pure v</c>, the two triples
/// are definitionally equal once <c>Std.Do.Triple</c> and the program are unfolded, since the exception half is then never
/// reached: unification finds that and the kernel admits it. When <c>v</c> is a variable <c>a</c> and the callee's
/// <c>Ensures</c> is <c>r = a</c>, the result postcondition <c>?ok</c> is solved as <c>fun r => r = r</c> (the pattern
/// <c>?ok a =?= (a = a)</c> abstracts every <c>a</c>), which says nothing: the weak postcondition the ticket saw. The walker
/// chooses <c>Vc.callExternal</c> from the contract's type, so it never relies on this.
/// </summary>
public sealed class VcCallUnificationTests(AttributeSidecarFixture fixture) : IClassFixture<AttributeSidecarFixture>
{
    /// <summary>What the call's program is.</summary>
    private enum Program
    {
        /// <summary>An opaque <c>x : ClrM σ Int32</c>.</summary>
        Opaque,

        /// <summary><c>pure 1</c>, with <c>Ensures(r => 0 ≤ r)</c>.</summary>
        PureLiteral,

        /// <summary><c>pure a</c> for a variable <c>a</c>, with <c>Ensures(r => r = a)</c>.</summary>
        PureVariable,
    }

    /// <summary>
    /// <c>σ, [x or a,] hx : ⦃⌜True⌝⦄ prog ⦃⇓r => ⌜ensures r⌝; exceptions⦄ ⊢ ⦃⌜True⌝⦄ prog ⦃⇓r => ⌜ensures r⌝; allowed⦄</c>,
    /// with the rule applied to the goal: its unassigned triple premise, <c>hx</c>, and the binders in order.
    /// </summary>
    private (MetaM M, MVarId Premise, FVarExpr Hx, FVarExpr[] Binders) CallSite(string rule, string exceptions, Program program = Program.Opaque)
    {
        var m = fixture.NewMeta();
        m.DebugCheckAssignments = true;
        Expr Statement(Expr sigma, Expr prog, Expr[] before, Func<Expr, Expr> ensures)
        {
            var truth = ClrTerms.Pure(sigma, C("True"));
            var callee = ClrTerms.Triple(m, sigma, Int32T, prog, truth, ClrTerms.Post(m, sigma, Int32T, ensures, exceptions));
            return m.WithLocalDeclD(N("hx"), callee, hx =>
                m.MkForallFVars([sigma, .. before, hx], ClrTerms.Triple(m, sigma, Int32T, prog, truth, ClrTerms.Post(m, sigma, Int32T, ensures))));
        }
        Expr NonNegative(Expr r) => ClrTerms.Le(Int32Lit(0), r);
        var statement = m.WithLocalDeclD(N("σ"), ClrTerms.TypeT, sigma => program switch
        {
            Program.PureLiteral => Statement(sigma, ClrTerms.PureM(m, sigma, Int32T, Int32Lit(1)), [], NonNegative),
            Program.PureVariable => m.WithLocalDeclD(N("a"), Int32T, a =>
                Statement(sigma, ClrTerms.PureM(m, sigma, Int32T, a), [a], r => ClrTerms.Eq(r, a))),
            _ => m.WithLocalDeclD(N("x"), Expr.App(ClrTerms.M(sigma), Int32T), x => Statement(sigma, x, [x], NonNegative)),
        });
        var root = m.MkFreshExprSyntheticOpaqueMVar(statement);
        var (fvars, goal) = m.IntroN(root.Id, program == Program.PureLiteral ? 2 : 3);
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
        var (m, premise, hx, binders) = CallSite("Warrant.Vc.call", "Warrant.ClrExn.External", Program.PureLiteral);
        Admit(m, premise, hx, binders, "VcCallOverPure");
    }

    /// <summary>
    /// #241's symptom: over <c>pure a</c> with <c>Ensures(r => r = a)</c>, <c>Vc.call</c> unifies with the <c>External</c>
    /// contract and solves <c>?ok</c> as <c>fun r => r = r</c>, not the callee's <c>r = a</c>; the kernel admits it.
    /// </summary>
    [Fact]
    public void VcCallOverPureOfAVariableSolvesTheResultPostconditionAsREqualsR()
    {
        var (m, premise, hx, binders) = CallSite("Warrant.Vc.call", "Warrant.ClrExn.External", Program.PureVariable);
        Admit(m, premise, hx, binders, "VcCallOverPureVariable");
        // The premise ⦃⌜?p⌝⦄ x ⦃(fun r => ⌜?ok r⌝, …)⦄ after Apply: its postcondition's first component.
        var post = m.InstantiateMVars(m.GetMVarType(premise)).GetAppArgs()[6];
        var ok = Assert.IsType<LamExpr>(post.GetAppArgs()[2]);
        var prop = ok.Body.GetAppArgs()[^1];
        Assert.True(prop.GetAppFn() is ConstExpr { Name: var eq } && eq == N("Eq"), $"ok is {ok}");
        Assert.Equal([Expr.BVar(0), Expr.BVar(0)], prop.GetAppArgs()[1..]);
    }

    /// <summary>Applies <c>hx</c> to the premise, which must close it, and has the C# kernel admit the result.</summary>
    private void Admit(MetaM m, MVarId premise, FVarExpr hx, FVarExpr[] binders, string name)
    {
        var premiseExpr = Expr.MVar(premise);
        Assert.All(m.Apply(premise, hx, "hx"), g => Assert.True(m.MCtx.IsAssigned(g)));
        var (statement, proof) = m.WithContext(premise, () =>
            (m.MkForallFVars(binders, m.InstantiateMVars(m.GetMVarType(premise))), m.MkLambdaFVars(binders, m.InstantiateMVars(premiseExpr))));
        Assert.False(proof.HasExprMVar || proof.HasLevelMVar || proof.HasFVar, $"proof is not ground: {proof}");
        KernelThread.Run(() => Kernel.Kernel.Add(fixture.Bundle.Fork(), new TheoremDecl(new TheoremInfo(N(name), [], statement, proof, [N(name)]))));
    }
}
