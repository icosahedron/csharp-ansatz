using Warrant.Cic;
using Warrant.Kernel;
using static Warrant.Meta.Tests.InitTerms;
using static Warrant.Meta.Tests.MetaTestSupport;

namespace Warrant.Meta.Tests;

/// <summary>
/// Terms of M6's effect core (plan M6 KTD4, KTD12, lean/Warrant/Effect.lean) as Lean 4.35.0 elaborates them, built over
/// fresh free variables in a <see cref="MetaM"/>: the effect monad <c>ClrM σ</c>, its post-shape, one-state assertions
/// and the KTD12 postcondition, whose exception half allows exactly <c>ClrExn.Allowed</c>.
/// </summary>
internal static class ClrTerms
{
    public static Expr TypeT { get; } = Expr.Sort(Level.One);

    public static Expr ClrExnT { get; } = C("Warrant.ClrExn");

    public static Expr M(Expr sigma) => Expr.App(C("Warrant.ClrM"), sigma);

    /// <summary><c>.arg σ .pure</c>, the world's layer.</summary>
    public static Expr ArgShape(Expr sigma) => Expr.App(C("Std.Do.PostShape.arg", Level.Zero), sigma, C("Std.Do.PostShape.pure", Level.Zero));

    /// <summary><c>.except ClrExn (.arg σ .pure)</c>, the post-shape of <c>ClrM σ</c>.</summary>
    public static Expr Shape(Expr sigma) => Expr.App(C("Std.Do.PostShape.except", Level.Zero), ClrExnT, ArgShape(sigma));

    /// <summary><c>PostShape.args shape</c>: the states of an assertion at <paramref name="shape"/>, <c>[σ]</c> here.</summary>
    public static Expr Args(Expr shape) => Expr.App(C("Std.Do.PostShape.args", Level.Zero), shape);

    /// <summary>
    /// <c>⌜p⌝ : Assertion (ClrM σ's shape)</c>, as Lean elaborates it against that type: <c>SPred.pure</c> at the states
    /// <c>PostShape.args shape</c>, which unification can match against a lemma's <c>Assertion ?ps</c>.
    /// </summary>
    public static Expr Pure(Expr sigma, Expr p) => Expr.App(C("Std.Do.SPred.pure", Level.Zero), Args(Shape(sigma)), p);

    /// <summary><c>⌜p⌝</c> at the world's layer <c>.arg σ .pure</c>, the type of an exception condition's assertion.</summary>
    public static Expr PureArg(Expr sigma, Expr p) => Expr.App(C("Std.Do.SPred.pure", Level.Zero), Args(ArgShape(sigma)), p);

    public static Expr Allowed(Expr e) => Expr.App(C("Warrant.ClrExn.Allowed"), e);

    public static Expr MonadInst(MetaM m, Expr sigma) => m.SynthInstanceOrThrow(Expr.App(C("Monad", Level.Zero, Level.Zero), M(sigma)));

    /// <summary><c>@Pure.pure (ClrM σ) _ α a</c>, through the <c>Monad</c> instance, as <c>Std.Do.Spec.pure</c> states it.</summary>
    public static Expr PureM(MetaM m, Expr sigma, Expr alpha, Expr a) =>
        Expr.App(C("Pure.pure", Level.Zero, Level.Zero), M(sigma),
            Expr.App(C("Applicative.toPure", Level.Zero, Level.Zero), M(sigma),
                Expr.App(C("Monad.toApplicative", Level.Zero, Level.Zero), M(sigma), MonadInst(m, sigma))),
            alpha, a);

    /// <summary><c>x >>= f</c> in <c>ClrM σ</c>.</summary>
    public static Expr BindM(MetaM m, Expr sigma, Expr alpha, Expr beta, Expr x, Expr f) =>
        Expr.App(C("Bind.bind", Level.Zero, Level.Zero), M(sigma),
            Expr.App(C("Monad.toBind", Level.Zero, Level.Zero), M(sigma), MonadInst(m, sigma)), alpha, beta, x, f);

    /// <summary><c>fun (x : type) => body x</c>.</summary>
    public static Expr Lam(MetaM m, string name, Expr type, Func<Expr, Expr> body) =>
        m.WithLocalDeclD(N(name), type, x => m.MkLambdaFVars([x], body(x)));

    /// <summary>
    /// KTD12's postcondition: <c>ensures r</c> on normal return, and <c>ClrExn.Allowed e</c> for an exception, so only an
    /// explicit throw or an exception propagated from a dependency is allowed.
    /// </summary>
    public static Expr Post(MetaM m, Expr sigma, Expr alpha, Func<Expr, Expr> ensures)
    {
        var shape = Shape(sigma);
        var arg = ArgShape(sigma);
        var assertion = Expr.App(C("Std.Do.Assertion", Level.Zero), shape);
        var argAssertion = Expr.App(C("Std.Do.Assertion", Level.Zero), arg);
        var conds = Expr.App(C("Std.Do.ExceptConds", Level.Zero), shape);
        var argConds = Expr.App(C("Std.Do.ExceptConds", Level.Zero), arg);
        var ok = Lam(m, "r", alpha, r => Pure(sigma, ensures(r)));
        var exc = Lam(m, "e", ClrExnT, e => PureArg(sigma, Allowed(e)));
        return Expr.App(C("Prod.mk", Level.Zero, Level.Zero), Expr.Forall(N("r"), alpha, assertion), conds, ok,
            Expr.App(C("Prod.mk", Level.Zero, Level.Zero), Expr.Forall(N("e"), ClrExnT, argAssertion), argConds, exc,
                C("PUnit.unit", Level.One)));
    }

    /// <summary><c>⦃P⦄ x ⦃Q⦄</c> for <c>x : ClrM σ α</c>, with the <c>WP</c> instance found by instance resolution.</summary>
    public static Expr Triple(MetaM m, Expr sigma, Expr alpha, Expr x, Expr pre, Expr post)
    {
        var wp = m.SynthInstanceOrThrow(Expr.App(C("Std.Do.WP", Level.Zero, Level.Zero), M(sigma), Shape(sigma)));
        return Expr.App(C("Std.Do.Triple", Level.Zero, Level.Zero), M(sigma), Shape(sigma), wp, alpha, x, pre, post);
    }

    // Int32 terms, as M4 translates them.

    public static Expr Eq(Expr a, Expr b) => Expr.App(C("Eq", Level.One), Int32T, a, b);

    public static Expr Not(Expr p) => Expr.App(C("Not"), p);

    public static Expr And(Expr p, Expr q) => Expr.App(C("And"), p, q);

    public static Expr Le(Expr a, Expr b) => Expr.App(C("LE.le", Level.Zero), Int32T, C("instLEInt32"), a, b);

    public static Expr Lt(Expr a, Expr b) => Expr.App(C("LT.lt", Level.Zero), Int32T, C("instLTInt32"), a, b);

    public static Expr Neg(Expr a) => Expr.App(C("Neg.neg", Level.Zero), Int32T, C("Int32.instNeg"), a);

    public static Expr Div(Expr a, Expr b) =>
        Expr.App(C("HDiv.hDiv", Level.Zero, Level.Zero, Level.Zero), Int32T, Int32T, Int32T,
            Expr.App(C("instHDiv", Level.Zero), Int32T, C("instDivInt32")), a, b);
}

/// <summary>
/// M6's go/no-go checkpoint for KTD13 and KTD14 (plan M6 U3 step 5, as amended by #172): three contract obligations
/// built by hand as <c>Std.Do</c> triples over <c>ClrM</c>, proved by Warrant's own <c>Apply</c> with
/// <c>Std.Do.Spec.bind</c>, <c>Spec.pure</c>, U3's <c>Warrant.ClrM.throw_spec</c>, U3's <c>Warrant.Triple.ite</c> and the
/// consequence rules, and for the third with a dependency's contract hypothesis instantiated at its call; the leftover
/// VCs are closed by Warrant's simp with KTD14's VC simp set, then <c>omega</c>; and the C# kernel admits each proof.
/// This is the walker's route (KTD13) taken by hand, before U11 builds the walker.
/// </summary>
public sealed class EffectCheckpointTests(AttributeSidecarFixture fixture) : IClassFixture<AttributeSidecarFixture>
{
    /// <summary>
    /// KTD14's VC simp set, besides Warrant's default set: the one-state assertion lemmas, the predicate transformers'
    /// equations, and the model equations of <c>ClrExn.Allowed</c>. U11's <c>VcSimpSet</c> takes this list.
    /// </summary>
    internal static readonly string[] VcSimpLemmas =
    [
        "Std.Do.SPred.entails_1", "Std.Do.SPred.apply_pure_cons", "Std.Do.SPred.down_pure_nil",
        "Std.Do.SPred.and_cons", "Std.Do.SPred.and_nil", "Std.Do.SPred.or_cons", "Std.Do.SPred.or_nil",
        "Std.Do.PredTrans.apply_Pure_pure", "Std.Do.PredTrans.apply_pure", "Std.Do.PredTrans.apply_Functor_map",
        "Std.Do.PredTrans.apply_bind", "Std.Do.PredTrans.apply_Bind_bind", "Std.Do.PredTrans.apply_Seq_seq",
        "Std.Do.PredTrans.apply_const", "Std.Do.PredTrans.apply_throw", "Std.Do.PredTrans.apply_pushArg",
        "Std.Do.PredTrans.apply_pushExcept", "Std.Do.PredTrans.apply_dite", "Std.Do.PredTrans.apply_ite",
        "Warrant.ClrExn.allowed_overflow", "Warrant.ClrExn.allowed_divideByZero", "Warrant.ClrExn.allowed_nullReference",
        "Warrant.ClrExn.allowed_invalidOperation", "Warrant.ClrExn.allowed_assertFailed", "Warrant.ClrExn.allowed_thrown",
        "Warrant.ClrExn.allowed_external",
    ];

    private static readonly Expr ArgumentException = Expr.StrLit("T:System.ArgumentException");

    private MetaM NewMeta()
    {
        var m = fixture.NewMeta();
        m.DebugCheckAssignments = true;
        return m;
    }

    [Fact]
    public void EveryConstantOfTheCheckpointIsInTheBundle()
    {
        string[] rules =
        [
            "Std.Do.Triple.entails_wp_of_pre", "Std.Do.Triple.entails_wp_of_pre_post", "Std.Do.PostCond.entails.mk",
            "Std.Do.ExceptConds.entails.refl", "Std.Do.Spec.pure", "Std.Do.Spec.bind", "Warrant.ClrM.throw_spec",
            "Warrant.Triple.ite", "Warrant.Triple.dite", "Warrant.Int32.div_spec",
        ];
        Assert.All(rules.Concat(VcSimpLemmas), n => Assert.NotNull(fixture.Env.Find(N(n))));
    }

    /// <summary>
    /// <c>Spec.pure</c>'s <c>WPMonad</c> instance appears in its conclusion only under <c>WPMonad.toWP</c>, which the goal
    /// states with <c>ExceptT.instWP</c>. Unification assigns it through its pending-instance step, and <c>Apply</c>
    /// synthesizes it again and checks that the two agree, as Lean's <c>synthAppInstances</c> does (M6 U3 step 3).
    /// </summary>
    [Fact]
    public void ApplySynthesizesTheWPMonadInstanceOfAStructuralRule()
    {
        var m = NewMeta();
        var statement = m.WithLocalDeclD(N("σ"), ClrTerms.TypeT, sigma => m.WithLocalDeclD(N("a"), Int32T, a =>
        {
            // ⦃Q.1 a⦄ pure a ⦃Q⦄, Spec.pure's own shape.
            var post = ClrTerms.Post(m, sigma, Int32T, r => ClrTerms.Le(Int32Lit(0), r));
            var pre = Expr.App(C("Prod.fst", Level.Zero, Level.Zero), Expr.Forall(N("r"), Int32T, Expr.App(C("Std.Do.Assertion", Level.Zero), ClrTerms.Shape(sigma))),
                Expr.App(C("Std.Do.ExceptConds", Level.Zero), ClrTerms.Shape(sigma)), post, a);
            return m.MkForallFVars([sigma, a], ClrTerms.Triple(m, sigma, Int32T, ClrTerms.PureM(m, sigma, Int32T, a), pre, post));
        }));
        var (root, goal, _) = Start(m, statement, 2);
        Assert.Empty(m.ApplyConst(goal, N("Std.Do.Spec.pure")));
        var proof = m.InstantiateMVars(root);
        Assert.NotNull(ExprOps.Find(proof, (e, _) => e is ConstExpr c && c.Name == N("Std.Do.ExceptT.instWPMonad")));
        Admit(m, "PureSpec", statement, root);
    }

    /// <summary>
    /// U11's <c>Ratio</c>: <c>Spec.Requires(b != 0 &amp;&amp; b != -1); return a / b;</c>, whose obligation is
    /// <c>∀ σ a b, ⦃⌜b ≠ 0 ∧ b ≠ -1⌝⦄ Warrant.Int32.div a b ⦃⇓_ => True, allowed⦄</c>. The division's <c>@[spec]</c>
    /// lemma leaves one VC, that neither <c>divideByZero</c> nor <c>overflow</c> is raised under the precondition.
    /// </summary>
    [Fact]
    public void RatioIsProved()
    {
        var m = NewMeta();
        var statement = Ratio(m, excludeMinusOne: true);
        var (root, goal, _) = Start(m, statement, 3);
        var (h, hpre) = Conseq(m, goal);
        Assert.Empty(m.ApplyConst(h, N("Warrant.Int32.div_spec")));
        CloseVc(m, hpre);
        Admit(m, "Ratio", statement, root);
    }

    /// <summary>
    /// With only <c>Spec.Requires(b != 0)</c>, <c>int.MinValue / -1</c> raises <c>overflow</c>, which the obligation
    /// does not allow: the same route leaves a VC that omega refutes.
    /// </summary>
    [Fact]
    public void RatioWithoutTheMinusOneGuardFailsAtOmega()
    {
        var m = NewMeta();
        var (_, goal, _) = Start(m, Ratio(m, excludeMinusOne: false), 3);
        var (h, hpre) = Conseq(m, goal);
        Assert.Empty(m.ApplyConst(h, N("Warrant.Int32.div_spec")));
        var ex = Assert.Throws<TacticException>(() => CloseVc(m, hpre));
        Assert.Equal("omega", ex.Tactic);
    }

    /// <summary><c>∀ σ a b, ⦃⌜b ≠ 0 ∧ b ≠ -1⌝⦄ Warrant.Int32.div a b ⦃⇓_ => True, allowed⦄</c>, or with <c>⌜b ≠ 0⌝</c>.</summary>
    private static Expr Ratio(MetaM m, bool excludeMinusOne) =>
        m.WithLocalDeclD(N("σ"), ClrTerms.TypeT, sigma =>
            m.WithLocalDeclD(N("a"), Int32T, a => m.WithLocalDeclD(N("b"), Int32T, b =>
            {
                var nonZero = ClrTerms.Not(ClrTerms.Eq(b, Int32Lit(0)));
                var pre = ClrTerms.Pure(sigma, excludeMinusOne
                    ? ClrTerms.And(nonZero, ClrTerms.Not(ClrTerms.Eq(b, ClrTerms.Neg(Int32Lit(1)))))
                    : nonZero);
                var post = ClrTerms.Post(m, sigma, Int32T, _ => C("True"));
                var program = Expr.App(C("Warrant.Int32.div"), sigma, a, b);
                return m.MkForallFVars([sigma, a, b], ClrTerms.Triple(m, sigma, Int32T, program, pre, post));
            })));

    /// <summary>
    /// A guard, <c>if b == 0 then throw (thrown k) else pure (a / b)</c>, with <c>Requires(b &gt;= 0)</c> and
    /// <c>Ensures(r =&gt; b &gt; 0 &amp;&amp; r == a / b)</c>: the ite rule gives one goal per branch, the throw is allowed
    /// (an explicit throw), and the normal return needs the branch's <c>¬(b = 0)</c> and omega for <c>0 &lt; b</c>.
    /// </summary>
    [Fact]
    public void TheGuardIsProved()
    {
        var m = NewMeta();
        var statement = m.WithLocalDeclD(N("σ"), ClrTerms.TypeT, sigma =>
            m.WithLocalDeclD(N("a"), Int32T, a => m.WithLocalDeclD(N("b"), Int32T, b =>
            {
                var zero = Int32Lit(0);
                var pre = ClrTerms.Pure(sigma, ClrTerms.Le(zero, b));
                var post = ClrTerms.Post(m, sigma, Int32T, r => ClrTerms.And(ClrTerms.Lt(zero, b), ClrTerms.Eq(r, ClrTerms.Div(a, b))));
                var condition = ClrTerms.Eq(b, zero);
                var program = Expr.App(C("ite", Level.One), Expr.App(ClrTerms.M(sigma), Int32T), condition,
                    Expr.App(C("instDecidableEqInt32"), b, zero),
                    Expr.App(C("Warrant.ClrM.throw"), sigma, Int32T, Expr.App(C("Warrant.ClrExn.thrown"), ArgumentException)),
                    ClrTerms.PureM(m, sigma, Int32T, ClrTerms.Div(a, b)));
                return m.MkForallFVars([sigma, a, b], ClrTerms.Triple(m, sigma, Int32T, program, pre, post));
            })));

        var (root, goal, _) = Start(m, statement, 3);
        var branches = m.ApplyConst(goal, N("Warrant.Triple.ite"));
        Assert.Equal(2, branches.Count);

        var (_, thenGoal) = m.Intro1(branches[0], N("hb"));
        var (hThrow, preThrow) = Conseq(m, thenGoal);
        Assert.Empty(m.ApplyConst(hThrow, N("Warrant.ClrM.throw_spec")));
        CloseVc(m, preThrow);

        var (_, elseGoal) = m.Intro1(branches[1], N("hb"));
        var (hPure, prePure) = Conseq(m, elseGoal);
        Assert.Empty(m.ApplyConst(hPure, N("Std.Do.Spec.pure")));
        Assert.True(CloseVc(m, prePure), "the normal return's VC needs omega");

        Admit(m, "Guard", statement, root);
    }

    /// <summary>
    /// The D9 shape (design §5.2's <c>GetPayment</c>, U20): <c>var p = store.Get(id); return p;</c> with
    /// <c>Ensures(p =&gt; p is null || p.Id == id)</c>, for every world type <c>σ</c> and every operation <c>get</c> that keeps
    /// its contract <c>∀ x, ⦃⌜True⌝⦄ get x ⦃⇓r => r is null || r.Id == x, allowed⦄</c>. The record is a stand-in pair
    /// <c>Int32 × Int32</c> whose first component is <c>Id</c>, and <c>p is null || p.Id == id</c> is
    /// <c>∀ q, p = some q → q.1 = id</c>. The external hypothesis is instantiated at the call through <c>Apply</c> with
    /// the consequence rule <c>Triple.entails_wp_of_pre_post</c>, which is the step simp alone cannot take.
    /// </summary>
    [Fact]
    public void ADependencyCallIsProvedFromItsContract()
    {
        var m = NewMeta();
        var record = Expr.App(C("Prod", Level.Zero, Level.Zero), Int32T, Int32T);
        var result = Expr.App(C("Option", Level.Zero), record);
        Expr NullOrId(Expr r, Expr id) =>
            m.WithLocalDeclD(N("q"), record, q => m.WithLocalDeclD(N("h"),
                Expr.App(C("Eq", Level.One), result, r, Expr.App(C("Option.some", Level.Zero), record, q)),
                h => m.MkForallFVars([q, h], ClrTerms.Eq(Expr.App(C("Prod.fst", Level.Zero, Level.Zero), Int32T, Int32T, q), id))));

        var statement = m.WithLocalDeclD(N("σ"), ClrTerms.TypeT, sigma =>
        {
            var getType = Expr.Forall(N("x"), Int32T, Expr.App(ClrTerms.M(sigma), result));
            return m.WithLocalDeclD(N("get"), getType, get => m.WithLocalDeclD(N("id"), Int32T, id =>
            {
                var truth = ClrTerms.Pure(sigma, C("True"));
                var contract = m.WithLocalDeclD(N("x"), Int32T, x => m.MkForallFVars([x],
                    ClrTerms.Triple(m, sigma, result, Expr.App(get, x), truth, ClrTerms.Post(m, sigma, result, r => NullOrId(r, x)))));
                return m.WithLocalDeclD(N("hget"), contract, hget =>
                {
                    var program = ClrTerms.BindM(m, sigma, result, result, Expr.App(get, id),
                        ClrTerms.Lam(m, "p", result, p => ClrTerms.PureM(m, sigma, result, p)));
                    var obligation = ClrTerms.Triple(m, sigma, result, program, truth, ClrTerms.Post(m, sigma, result, r => NullOrId(r, id)));
                    return m.MkForallFVars([sigma, get, id, hget], obligation);
                });
            }));
        });

        var (root, goal, fvars) = Start(m, statement, 4);
        var hget = Expr.FVar(fvars[3]);
        var (hBind, preBind) = Conseq(m, goal);
        Assert.Empty(m.ApplyConst(hBind, N("Std.Do.Spec.bind")));

        // ⌜True⌝ ⊢ₛ wp⟦get id⟧ (fun a => wp⟦pure a⟧ Q, Q.2): the contract at the call, then its pre- and postcondition.
        var call = m.ApplyConst(preBind, N("Std.Do.Triple.entails_wp_of_pre_post"));
        var hCall = Single(m, call, "Std.Do.Triple");
        Assert.Empty(m.Apply(hCall, hget, "hget"));
        CloseVc(m, Single(m, call, "Std.Do.SPred.entails"));

        var conds = m.ApplyConst(Single(m, call, "Std.Do.PostCond.entails"), N("Std.Do.PostCond.entails.mk"));
        Assert.Empty(m.ApplyConst(Single(m, conds, "Std.Do.ExceptConds.entails"), N("Std.Do.ExceptConds.entails.refl")));
        var (_, normal) = m.Intro1(conds.Single(g => !m.MCtx.IsAssigned(g) && Head(m, g) is null), N("p"));
        // PostCond.entails.mk leaves (fun a => wp⟦pure a⟧ Q, Q.2).1 p, which neither Lean's apply nor Warrant's unifies with
        // the consequence rule's wp⟦?x⟧ ?Q; simp with no lemmas reduces the projection and the β-redex (Lean's dsimp only).
        var (hReturn, preReturn) = Conseq(m, Reduce(m, normal));
        Assert.Empty(m.ApplyConst(hReturn, N("Std.Do.Spec.pure")));
        CloseVc(m, preReturn);

        Admit(m, "GetPayment", statement, root);
    }

    // ------------------------------------------------------------------ the route

    /// <summary>A goal for <paramref name="statement"/>, with its first <paramref name="binders"/> binders introduced.</summary>
    private static (MVarExpr Root, MVarId Goal, FVarId[] FVars) Start(MetaM m, Expr statement, int binders)
    {
        var root = m.MkFreshExprSyntheticOpaqueMVar(statement);
        var (fvars, goal) = m.IntroN(root.Id, binders);
        return (root, goal, fvars);
    }

    /// <summary>
    /// The consequence rule <c>Triple.entails_wp_of_pre</c> on a triple goal: a triple for the same program with a
    /// precondition left for the program's rule to determine, and the entailment from the goal's precondition to it.
    /// </summary>
    private static (MVarId Triple, MVarId Pre) Conseq(MetaM m, MVarId goal)
    {
        var goals = m.ApplyConst(goal, N("Std.Do.Triple.entails_wp_of_pre"));
        return (Single(m, goals, "Std.Do.Triple"), Single(m, goals, "Std.Do.SPred.entails"));
    }

    /// <summary>Warrant's simp with no lemmas: β, projections of constructors and the other definitional steps only.</summary>
    private static MVarId Reduce(MetaM m, MVarId goal) =>
        m.SimpTarget(goal, new SimpContext(SimpConfig.Default, [], SimpContext.CongrTheoremsOf(m.Attributes)))
            ?? throw new InvalidOperationException("the goal closed");

    /// <summary>
    /// Closes a leftover VC with Warrant's simp over KTD14's VC simp set, then <c>omega</c> if simp leaves a goal.
    /// </summary>
    /// <returns>Whether omega was needed.</returns>
    private static bool CloseVc(MetaM m, MVarId goal)
    {
        var extra = new SimpTheorems();
        foreach (var name in VcSimpLemmas)
        {
            extra.AddRange(m.MkSimpTheoremsFromConst(N(name)));
        }
        var context = DefaultSimpSet.Context(m, SimpConfig.Default, extra);
        if (m.SimpTarget(goal, context) is not { } rest)
        {
            return false;
        }
        m.OmegaTactic(rest);
        return true;
    }

    /// <summary>The unassigned goal among <paramref name="goals"/> whose type is headed by <paramref name="head"/>.</summary>
    private static MVarId Single(MetaM m, IReadOnlyList<MVarId> goals, string head) =>
        Assert.Single(goals, g => !m.MCtx.IsAssigned(g) && Head(m, g) == head);

    private static string? Head(MetaM m, MVarId goal) =>
        (m.InstantiateMVars(m.GetMVarType(goal)).GetAppFn() as ConstExpr)?.Name.ToString();

    /// <summary>Has the C# kernel admit <c>theorem name : statement := proof</c> into a fork of the bundle.</summary>
    private void Admit(MetaM m, string name, Expr statement, MVarExpr root)
    {
        var proof = m.InstantiateMVars(root);
        Assert.False(proof.HasExprMVar || proof.HasLevelMVar || proof.HasFVar, $"proof is not ground: {proof}");
        KernelThread.Run(() => Kernel.Kernel.Add(fixture.Bundle.Fork(), new TheoremDecl(new TheoremInfo(N(name), [], statement, proof, [N(name)]))));
    }
}
