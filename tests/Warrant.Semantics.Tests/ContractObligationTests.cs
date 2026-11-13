using Warrant.Cic;
using Warrant.Kernel;
using Warrant.Vir;

namespace Warrant.Semantics.Tests;

/// <summary>
/// Contract obligations (plan M6 U10, KTD12, KTD25, KTD26): what Semantics states for each verified method that has a
/// contract, can raise, or calls a method with <c>Spec.Requires</c>. The statements are checked by the kernel to be
/// propositions over the admitted definitions; whether they are proved is the engine's (and, for the default procedure,
/// M6 U11's) concern.
/// </summary>
public sealed class ContractObligationTests(SemanticsBundleFixture bundle) : IClassFixture<SemanticsBundleFixture>
{
    private static readonly Expr Int32T = C("Int32");

    private static Name N(string dotted) => Name.Parse(dotted);

    private static Expr C(string dotted, params Level[] levels) => Expr.Const(N(dotted), levels);

    private static Expr I(int n) => Literals.Int32(n);

    private (Translation Translation, KernelEnvironment Env) Translate(string source)
    {
        var translation = TranslationCorpus.Translate(TranslationCorpus.Inline("using System;\n" + source), bundle.Env);
        return (translation, TranslationCorpus.Admit(bundle, translation));
    }

    private static ContractObligation Contract(Translation translation, string key) =>
        translation.Find(key)!.Contract ?? throw new InvalidOperationException($"{key} has no contract obligation");

    /// <summary>The kernel infers <c>Prop</c> for <paramref name="statement"/> in <paramref name="env"/>.</summary>
    private static void AssertProposition(KernelEnvironment env, Expr statement) =>
        KernelThread.Run(() =>
        {
            var tc = new TypeChecker(env);
            Assert.Equal(Expr.Sort(Level.Zero), tc.Whnf(tc.Check(statement)));
        });

    /// <summary>Every statement of an obligation, each a proposition the kernel accepts.</summary>
    private static void AssertPropositions(KernelEnvironment env, ContractObligation contract)
    {
        AssertProposition(env, contract.Theorem.Type);
        if (contract.Spec is { } spec)
        {
            AssertProposition(env, spec.Type);
        }
        foreach (var obligation in contract.WellDefinedness.Concat(contract.Vacuity))
        {
            AssertProposition(env, obligation.Theorem.Type);
        }
    }

    /// <summary>The body under <paramref name="count"/> <c>∀</c> binders, which must be there.</summary>
    private static Expr Under(Expr statement, int count)
    {
        for (int i = 0; i < count; i++)
        {
            statement = Assert.IsType<ForallExpr>(statement).Body;
        }
        return statement;
    }

    /// <summary>A triple's parts: <c>@Std.Do.Triple m shape inst α x pre post</c>.</summary>
    private static (Expr Program, Expr Pre, Expr Ok, Expr Exceptions) Triple(Expr triple)
    {
        Assert.Equal(C("Std.Do.Triple", Level.Zero, Level.Zero), triple.GetAppFn());
        var args = triple.GetAppArgs();
        Assert.Equal(7, args.Length);
        var post = args[6].GetAppArgs();
        Assert.Equal(C("Prod.mk", Level.Zero, Level.Zero), args[6].GetAppFn());
        return (args[4], args[5], post[2], post[3]);
    }

    /// <summary>The proposition of a one-state assertion <c>⌜p⌝ = @SPred.pure (PostShape.args shape) p</c>.</summary>
    private static Expr Assertion(Expr assertion)
    {
        Assert.Equal(C("Std.Do.SPred.pure", Level.Zero), assertion.GetAppFn());
        return assertion.GetAppArgs()[1];
    }

    /// <summary>The proposition of the normal postcondition <c>fun r =&gt; ⌜p⌝</c>, with <c>r</c> as <c>#0</c>.</summary>
    private static Expr Ensures(Expr ok) => Assertion(Assert.IsType<LamExpr>(ok).Body);

    /// <summary>KTD12's exception postcondition: <c>(fun e =&gt; ⌜ClrExn.Allowed e⌝, PUnit.unit)</c>.</summary>
    private static void AssertOnlyExplicitAndExternalExceptionsAllowed(Expr exceptions)
    {
        var parts = exceptions.GetAppArgs();
        Assert.Equal(C("Prod.mk", Level.Zero, Level.Zero), exceptions.GetAppFn());
        Assert.Equal(Expr.App(C("Warrant.ClrExn.Allowed"), Expr.BVar(0)), Assertion(Assert.IsType<LamExpr>(parts[2]).Body));
        Assert.Equal(C("PUnit.unit", Level.One), parts[3]);
    }

    private static Expr Ge(Expr a, Expr b) => Expr.App(C("GE.ge", Level.Zero), Int32T, C("instLEInt32"), a, b);

    private static Expr Gt(Expr a, Expr b) => Expr.App(C("GT.gt", Level.Zero), Int32T, C("instLTInt32"), a, b);

    private static Expr Lt(Expr a, Expr b) => Expr.App(C("LT.lt", Level.Zero), Int32T, C("instLTInt32"), a, b);

    private static Expr NotEq(Expr a, Expr b) => Expr.App(C("Not"), Expr.App(C("Eq", Level.One), Int32T, a, b));

    // ---- The triple (KTD12) ----

    [Fact]
    public void RequiresWithoutEnsuresStatesTruePostconditionAndTheExceptionPostcondition()
    {
        var (translation, env) = Translate("""
            public static class S
            {
                [Verified]
                public static int Halve(int x)
                {
                    Spec.Requires(x >= 0);
                    return x / 2;
                }
            }
            """);
        const string key = "M:S.Halve(System.Int32)";
        var contract = Contract(translation, key);
        Assert.Equal("Cs.S.«Halve(System.Int32)».$contract", contract.Theorem.Name.ToString());
        Assert.False(contract.Raising);
        Assert.Equal(2, contract.Binders);
        // ∀ (σ : Type) (x : Int32), ⦃⌜x ≥ 0⌝⦄ pure (Halve x) ⦃⇓_ => ⌜True⌝, allowed⦄
        var σ = Assert.IsType<ForallExpr>(contract.Theorem.Type);
        Assert.Equal(Expr.Sort(Level.One), σ.BinderType);
        var (program, pre, ok, exceptions) = Triple(Under(contract.Theorem.Type, 2));
        Assert.Equal(C("Pure.pure", Level.Zero, Level.Zero), program.GetAppFn());
        Assert.Equal(Expr.App(Expr.Const(translation.Find(key)!.Name), Expr.BVar(0)), program.GetAppArgs()[3]);
        Assert.Equal(Ge(Expr.BVar(0), I(0)), Assertion(pre));
        Assert.Equal(C("True"), Ensures(ok));
        AssertOnlyExplicitAndExternalExceptionsAllowed(exceptions);
        // No Ensures, so no spec lemma; the definition is M4's.
        Assert.Null(contract.Spec);
        AssertPropositions(env, contract);
    }

    // ---- Spec.NoThrow (#182) ----

    /// <summary><paramref name="e"/> with every <c>ClrExn.External</c> replaced by <c>ClrExn.Allowed</c>.</summary>
    private static Expr AllowedFor(Expr e) =>
        ExprOps.Replace(e, (x, _) => x is ConstExpr { Name: var n } && n == N("Warrant.ClrExn.External") ? C("Warrant.ClrExn.Allowed") : null);

    [Fact]
    public void NoThrowStatesTheExternalExceptionPostconditionAndChangesNothingElse()
    {
        var (translation, env) = Translate("""
            public static class S
            {
                [Verified]
                public static int Guard(int a, int b)
                {
                    Spec.Requires(b != 0);
                    Spec.NoThrow();
                    Spec.Ensures<int>(r => r == a);
                    if (b == 0)
                    {
                        throw new ArgumentException("b");
                    }
                    return a;
                }

                [Verified]
                public static int Plain(int a, int b)
                {
                    Spec.Requires(b != 0);
                    Spec.Ensures<int>(r => r == a);
                    if (b == 0)
                    {
                        throw new ArgumentException("b");
                    }
                    return a;
                }
            }
            """);
        var guard = Contract(translation, "M:S.Guard(System.Int32,System.Int32)");
        var plain = Contract(translation, "M:S.Plain(System.Int32,System.Int32)");
        Assert.True(guard.Raising);
        var (_, _, _, exceptions) = Triple(Under(guard.Theorem.Type, guard.Binders));
        var parts = exceptions.GetAppArgs();
        Assert.Equal(Expr.App(C("Warrant.ClrExn.External"), Expr.BVar(0)), Assertion(Assert.IsType<LamExpr>(parts[2]).Body));
        AssertOnlyExplicitAndExternalExceptionsAllowed(Triple(Under(plain.Theorem.Type, plain.Binders)).Exceptions);
        // Only the exception postcondition differs: with Allowed in place of External, the two statements are the same
        // up to the function's name.
        var guardName = translation.Find("M:S.Guard(System.Int32,System.Int32)")!.Name;
        var plainName = translation.Find("M:S.Plain(System.Int32,System.Int32)")!.Name;
        var renamed = ExprOps.Replace(AllowedFor(guard.Theorem.Type), (x, _) => x is ConstExpr c && c.Name == guardName ? Expr.Const(plainName) : null);
        Assert.Equal(plain.Theorem.Type, renamed);
        Assert.Equal(guard.Binders, plain.Binders);
        AssertPropositions(env, guard);
    }

    [Fact]
    public void NoThrowOnAPureMethodChangesNothing()
    {
        // A pure method raises nothing, so NoThrow holds of it already and its obligation is the one without (#182).
        var (translation, env) = Translate("""
            public static class S
            {
                [Verified]
                public static int Half(int x)
                {
                    Spec.Requires(x >= 0);
                    Spec.NoThrow();
                    return x / 2;
                }

                [Verified]
                public static int Same(int x)
                {
                    Spec.NoThrow();
                    return x;
                }
            }
            """);
        var half = Contract(translation, "M:S.Half(System.Int32)");
        Assert.False(half.Raising);
        AssertOnlyExplicitAndExternalExceptionsAllowed(Triple(Under(half.Theorem.Type, half.Binders)).Exceptions);
        Assert.Null(translation.Find("M:S.Same(System.Int32)")!.Contract);
        AssertPropositions(env, half);
    }

    [Fact]
    public void AContractFreeMethodThatDividesHasATrueTrueObligationOverItsProgram()
    {
        var (translation, env) = Translate("public static class S { [Verified] public static int Ratio(int a, int b) => a / b; }");
        const string key = "M:S.Ratio(System.Int32,System.Int32)";
        var contract = Contract(translation, key);
        Assert.True(contract.Raising);
        Assert.Equal(3, contract.Binders);
        var (program, pre, ok, exceptions) = Triple(Under(contract.Theorem.Type, 3));
        // @Ratio σ a b
        Assert.Equal(Expr.App(Expr.Const(translation.Find(key)!.Name), Expr.BVar(2), Expr.BVar(1), Expr.BVar(0)), program);
        Assert.Equal(C("True"), Assertion(pre));
        Assert.Equal(C("True"), Ensures(ok));
        AssertOnlyExplicitAndExternalExceptionsAllowed(exceptions);
        Assert.Empty(contract.WellDefinedness);
        Assert.Empty(contract.Vacuity);
        AssertPropositions(env, contract);
    }

    [Fact]
    public void ACallerOfAMethodWithRequiresHasAnObligationWithTheCallAsACalleeNode()
    {
        var (translation, env) = Translate("""
            public static class S
            {
                [Verified]
                public static int Positive(int x)
                {
                    Spec.Requires(x > 0);
                    return x;
                }

                [Verified] public static int Caller(int y) => Positive(unchecked(y + 1));
            }
            """);
        // unchecked: default-context y + 1 would be a site of its own before the call (#244).
        const string caller = "M:S.Caller(System.Int32)";
        var contract = Contract(translation, caller);
        Assert.True(contract.Raising);
        var (program, pre, ok, _) = Triple(Under(contract.Theorem.Type, 2));
        Assert.Equal(Expr.App(Expr.Const(translation.Find(caller)!.Name), Expr.BVar(1), Expr.BVar(0)), program);
        Assert.Equal(C("True"), Assertion(pre));
        Assert.Equal(C("True"), Ensures(ok));
        // The caller's program is pure (Positive (y + 1)), the callee node the walker proves the precondition at (M6 U9: a
        // call to a method with Spec.Requires is its pure value lifted into ClrM, bound unless it is the whole program).
        var body = ((LamExpr)((LamExpr)Assert.IsType<DefinitionDecl>(Assert.Single(translation.Find(caller)!.Declarations)).Value.Value).Body).Body;
        Assert.Equal(C("Pure.pure", Level.Zero, Level.Zero), body.GetAppFn());
        Assert.Equal(Expr.Const(translation.Find("M:S.Positive(System.Int32)")!.Name), body.GetAppArgs()[3].GetAppFn());
        AssertPropositions(env, contract);
        AssertPropositions(env, Contract(translation, "M:S.Positive(System.Int32)"));
    }

    [Fact]
    public void APureMethodWithEnsuresHasATripleOverPureAndASpecLemma()
    {
        var (translation, env) = Translate("""
            public static class S
            {
                [Verified]
                public static int AtMost(int x, int limit)
                {
                    Spec.Requires(x >= 0);
                    Spec.Requires(limit >= 0);
                    Spec.Ensures<int>(r => r >= 0 && r <= limit);
                    return x > limit ? limit : x;
                }
            }
            """);
        const string key = "M:S.AtMost(System.Int32,System.Int32)";
        var name = Expr.Const(translation.Find(key)!.Name);
        var contract = Contract(translation, key);
        var (program, pre, ok, _) = Triple(Under(contract.Theorem.Type, 3));
        Assert.Equal(C("Pure.pure", Level.Zero, Level.Zero), program.GetAppFn());
        // Two Requires are one conjunction; the result is bound by the postcondition's lambda, under x and limit.
        Assert.Equal(Expr.App(C("And"), Ge(Expr.BVar(1), I(0)), Ge(Expr.BVar(0), I(0))), Assertion(pre));
        Assert.Equal(
            Expr.App(C("And"), Ge(Expr.BVar(0), I(0)), Expr.App(C("LE.le", Level.Zero), Int32T, C("instLEInt32"), Expr.BVar(0), Expr.BVar(1))),
            Ensures(ok));

        // f.$contract_spec : ∀ x limit, (x ≥ 0 ∧ limit ≥ 0) → AtMost x limit ≥ 0 ∧ AtMost x limit ≤ limit
        var spec = Assert.IsType<TheoremShell>(contract.Spec);
        Assert.Equal("Cs.S.«AtMost(System.Int32,System.Int32)».$contract_spec", spec.Name.ToString());
        Assert.Equal(3, contract.SpecBinders);
        var result = Expr.App(name, Expr.BVar(2), Expr.BVar(1));
        Assert.Equal(
            Expr.App(C("And"), Ge(result, I(0)), Expr.App(C("LE.le", Level.Zero), Int32T, C("instLEInt32"), result, Expr.BVar(1))),
            Under(spec.Type, 3));
        AssertPropositions(env, contract);
    }

    [Fact]
    public void ARaisingMethodsEnsuresIsOverItsResultAndItsProofForScriptComesWithIt()
    {
        var (translation, env) = Translate("""
            public static class S
            {
                [Verified]
                public static int Share(int total, int people)
                {
                    Spec.Requires(people > 0);
                    Spec.Ensures<int>(each => each <= total || total < 0);
                    return total / people;
                }

                [ProofFor(nameof(Share))]
                static Proof ShareProof() => Prove.Contract().By(Tactic.VcGen(), Tactic.Omega());
            }
            """);
        var contract = Contract(translation, "M:S.Share(System.Int32,System.Int32)");
        Assert.True(contract.Raising);
        Assert.Null(contract.Spec);
        Assert.Equal(["vcgen", "omega"], contract.Script!.Select(t => t.Name));
        var (_, pre, ok, _) = Triple(Under(contract.Theorem.Type, 3));
        Assert.Equal(Gt(Expr.BVar(0), I(0)), Assertion(pre));
        Assert.Equal(N("each"), Assert.IsType<LamExpr>(ok).BinderName);
        Assert.Equal(
            Expr.App(C("Or"), Expr.App(C("LE.le", Level.Zero), Int32T, C("instLEInt32"), Expr.BVar(0), Expr.BVar(2)), Lt(Expr.BVar(2), I(0))),
            Ensures(ok));
        AssertPropositions(env, contract);
    }

    [Fact]
    public void APureMethodWithoutAContractHasNoObligationAndItsTranslationIsUnchanged()
    {
        // Nor implicit arithmetic, which must not overflow (#244): unchecked wraps on purpose.
        var (translation, _) = Translate("public static class S { [Verified] public static int Inc(int x) => unchecked(x + 1); }");
        Assert.Null(translation.Find("M:S.Inc(System.Int32)")!.Contract);
    }

    // ---- Well-definedness of Spec expressions (KTD26) ----

    [Fact]
    public void ADivisionInRequiresHasAWellDefinednessObligationUnderItsGuards()
    {
        var (translation, env) = Translate("""
            public static class S
            {
                [Verified]
                public static int Unguarded(int a, int b)
                {
                    Spec.Requires(a / b > 0);
                    return a;
                }

                [Verified]
                public static int Guarded(int a, int b)
                {
                    Spec.Requires(b != 0 && a / b > 0);
                    return a;
                }
            }
            """);
        var div = C("Warrant.Int32.div");

        var unguarded = Contract(translation, "M:S.Unguarded(System.Int32,System.Int32)");
        var wd = Assert.Single(unguarded.WellDefinedness);
        Assert.Equal(SpecObligationKind.WellDefinedOperation, wd.Kind);
        Assert.Equal("Cs.S.«Unguarded(System.Int32,System.Int32)».$wd_1", wd.Theorem.Name.ToString());
        Assert.Equal(3, wd.Binders);
        // ∀ σ a b, ⦃⌜True⌝⦄ Warrant.Int32.div σ a b ⦃⇓_ => ⌜True⌝, allowed⦄
        var (program, pre, ok, exceptions) = Triple(Under(wd.Theorem.Type, 3));
        Assert.Equal(Expr.App(div, Expr.BVar(2), Expr.BVar(1), Expr.BVar(0)), program);
        Assert.Equal(C("True"), Assertion(pre));
        Assert.Equal(C("True"), Ensures(ok));
        AssertOnlyExplicitAndExternalExceptionsAllowed(exceptions);
        Assert.IsType<BinaryExpr>(wd.Node);
        // The Requires itself reads the total division, which agrees with C#'s wherever the obligation holds.
        Assert.NotNull(ExprOps.Find(unguarded.Theorem.Type, (e, _) => e is ConstExpr { Name: var n } && n == N("HDiv.hDiv")));

        var guarded = Contract(translation, "M:S.Guarded(System.Int32,System.Int32)");
        wd = Assert.Single(guarded.WellDefinedness);
        // ∀ σ a b, ¬(b = 0) → ⦃⌜True⌝⦄ Warrant.Int32.div σ a b ⦃…⦄
        Assert.Equal(4, wd.Binders);
        var guard = Under(wd.Theorem.Type, 3);
        Assert.Equal(NotEq(Expr.BVar(0), I(0)), Assert.IsType<ForallExpr>(guard).BinderType);
        (program, _, _, _) = Triple(Under(wd.Theorem.Type, 4));
        Assert.Equal(Expr.App(div, Expr.BVar(3), Expr.BVar(2), Expr.BVar(1)), program);
        AssertPropositions(env, unguarded);
        AssertPropositions(env, guarded);
    }

    [Fact]
    public void ACheckedNarrowingInRequiresHasAWellDefinednessObligation()
    {
        // Review #230: the obligation's program is built over its own world, not the translator's (which a contract has none of).
        var (translation, env) = Translate("""
            public static class S
            {
                [Verified]
                public static long Narrow(long l)
                {
                    Spec.Requires(checked((int)l) > 0);
                    return l;
                }
            }
            """);
        var contract = Contract(translation, "M:S.Narrow(System.Int64)");
        var wd = Assert.Single(contract.WellDefinedness);
        Assert.Equal(SpecObligationKind.WellDefinedOperation, wd.Kind);
        Assert.IsType<ConvertExpr>(wd.Node);
        Assert.Equal(2, wd.Binders);
        // ∀ σ l, ⦃⌜True⌝⦄ Warrant.Int64.toInt32Checked σ l ⦃⇓_ => ⌜True⌝, allowed⦄
        var (program, pre, ok, exceptions) = Triple(Under(wd.Theorem.Type, 2));
        Assert.Equal(Expr.App(C("Warrant.Int64.toInt32Checked"), Expr.BVar(1), Expr.BVar(0)), program);
        Assert.Equal(C("True"), Assertion(pre));
        Assert.Equal(C("True"), Ensures(ok));
        AssertOnlyExplicitAndExternalExceptionsAllowed(exceptions);
        AssertPropositions(env, contract);
    }

    [Fact]
    public void WrappingArithmeticInEnsuresHasAnOverflowObligation()
    {
        // #183: + - * and unary - on int and long in a Spec expression must not overflow, even where C# would wrap.
        var (translation, env) = Translate("""
            public static class S
            {
                [Verified]
                public static int Add(int a, int b)
                {
                    Spec.Ensures<int>(r => r == a + b);
                    return unchecked(a + b);
                }

                [Verified]
                public static long Negate(long a)
                {
                    Spec.Requires(a > 0 || -a > 0);
                    return a;
                }
            }
            """);
        var add = Contract(translation, "M:S.Add(System.Int32,System.Int32)");
        var wd = Assert.Single(add.WellDefinedness);
        Assert.Equal(SpecObligationKind.WellDefinedOperation, wd.Kind);
        Assert.Equal("Cs.S.«Add(System.Int32,System.Int32)».$wd_1", wd.Theorem.Name.ToString());
        Assert.IsType<BinaryExpr>(wd.Node);
        // ∀ σ a b r, ⦃⌜True⌝⦄ Warrant.Int32.addChecked σ a b ⦃⇓_ => ⌜True⌝, allowed⦄
        Assert.Equal(4, wd.Binders);
        var (program, pre, ok, exceptions) = Triple(Under(wd.Theorem.Type, 4));
        Assert.Equal(Expr.App(C("Warrant.Int32.addChecked"), Expr.BVar(3), Expr.BVar(2), Expr.BVar(1)), program);
        Assert.Equal(C("True"), Assertion(pre));
        Assert.Equal(C("True"), Ensures(ok));
        AssertOnlyExplicitAndExternalExceptionsAllowed(exceptions);
        AssertPropositions(env, add);

        // The negation is under the guard ¬(a > 0) of the || that encloses it.
        var negate = Contract(translation, "M:S.Negate(System.Int64)");
        wd = Assert.Single(negate.WellDefinedness);
        Assert.IsType<UnaryExpr>(wd.Node);
        Assert.Equal(3, wd.Binders);
        (program, _, _, _) = Triple(Under(wd.Theorem.Type, 3));
        Assert.Equal(Expr.App(C("Warrant.Int64.negChecked"), Expr.BVar(2), Expr.BVar(1)), program);
        AssertPropositions(env, negate);
    }

    /// <summary>
    /// #213: <c>Spec.Implies(p, q)</c> in a contract evaluates <c>q</c> only under <c>p</c>, so the well-definedness and
    /// overflow obligations of <c>q</c>'s operations (KTD26, #183) are under the guard <c>p</c>; a <c>Spec.Requires</c>
    /// using it has its vacuity obligation over the implication.
    /// </summary>
    [Fact]
    public void ImpliesInAContractGuardsItsConclusionsObligationsWithItsPremise()
    {
        var (translation, env) = Translate("""
            public static class S
            {
                [Verified]
                public static int Inc(int x)
                {
                    Spec.Requires(Spec.Implies(x < 100, x + 1 > x));
                    return x;
                }

                [Verified]
                public static int Quot(int a, int b)
                {
                    Spec.Ensures<int>(r => Spec.Implies(b > 0, r == a / b));
                    return 0;
                }
            }
            """);
        var inc = Contract(translation, "M:S.Inc(System.Int32)");
        var wd = Assert.Single(inc.WellDefinedness);
        Assert.Equal(SpecObligationKind.WellDefinedOperation, wd.Kind);
        Assert.IsType<BinaryExpr>(wd.Node);
        // ∀ σ x, x < 100 → ⦃⌜True⌝⦄ Warrant.Int32.addChecked σ x 1 ⦃⇓_ => ⌜True⌝, allowed⦄
        Assert.Equal(3, wd.Binders);
        Assert.Equal(Lt(Expr.BVar(0), I(100)), Assert.IsType<ForallExpr>(Under(wd.Theorem.Type, 2)).BinderType);
        var (program, _, _, _) = Triple(Under(wd.Theorem.Type, 3));
        Assert.Equal(Expr.App(C("Warrant.Int32.addChecked"), Expr.BVar(2), Expr.BVar(1), I(1)), program);
        // ∀ x, (x < 100 → x + 1 > x) → False
        var vacuity = Assert.Single(inc.Vacuity);
        Assert.Equal(2, vacuity.Binders);
        var implication = Assert.IsType<ForallExpr>(Assert.IsType<ForallExpr>(Under(vacuity.Theorem.Type, 1)).BinderType);
        Assert.Equal(Lt(Expr.BVar(0), I(100)), implication.BinderType);
        Assert.Equal(C("False"), Under(vacuity.Theorem.Type, 2));
        AssertPropositions(env, inc);

        var quot = Contract(translation, "M:S.Quot(System.Int32,System.Int32)");
        wd = Assert.Single(quot.WellDefinedness);
        // ∀ σ a b r, b > 0 → ⦃⌜True⌝⦄ Warrant.Int32.div σ a b ⦃…⦄
        Assert.Equal(5, wd.Binders);
        Assert.Equal(Gt(Expr.BVar(1), I(0)), Assert.IsType<ForallExpr>(Under(wd.Theorem.Type, 4)).BinderType);
        (program, _, _, _) = Triple(Under(wd.Theorem.Type, 5));
        Assert.Equal(Expr.App(C("Warrant.Int32.div"), Expr.BVar(4), Expr.BVar(3), Expr.BVar(2)), program);
        AssertPropositions(env, quot);
    }

    /// <summary>#213: <c>Spec.Implies</c> as a <c>bool</c> value in a contract is <c>!p || q</c>, with <c>q</c> under <c>p</c>.</summary>
    [Fact]
    public void ImpliesAsAValueInAContractGuardsItsConclusionWithItsPremise()
    {
        var (translation, env) = Translate("""
            public static class S
            {
                [Verified]
                public static bool Same(int x, bool b)
                {
                    Spec.Ensures<bool>(r => r == Spec.Implies(x > 0, 10 / x > 0));
                    return b;
                }
            }
            """);
        var contract = Contract(translation, "M:S.Same(System.Int32,System.Boolean)");
        var wd = Assert.Single(contract.WellDefinedness);
        // ∀ σ x b r, decide (x > 0) = true → ⦃⌜True⌝⦄ Warrant.Int32.div σ 10 x ⦃…⦄
        Assert.Equal(5, wd.Binders);
        var (program, _, _, _) = Triple(Under(wd.Theorem.Type, 5));
        Assert.Equal(Expr.App(C("Warrant.Int32.div"), Expr.BVar(4), I(10), Expr.BVar(3)), program);
        AssertPropositions(env, contract);
    }

    [Fact]
    public void AnUncheckedCastInASpecExpressionHasNoObligation()
    {
        // #183 leaves an explicit unchecked narrowing as written: it is a deliberate C# truncation.
        var (translation, _) = Translate("""
            public static class S
            {
                [Verified]
                public static long Narrow(long l)
                {
                    Spec.Requires(unchecked((int)l) > 0);
                    return l;
                }
            }
            """);
        Assert.Empty(Contract(translation, "M:S.Narrow(System.Int64)").WellDefinedness);
    }

    [Fact]
    public void ExplicitUncheckedArithmeticInASpecExpressionWrapsWithNoObligation()
    {
        // #236: unchecked(...) wraps on purpose, so it has no obligation; its value is the wrapped one, as the default's.
        var (translation, env) = Translate("""
            public static class S
            {
                [Verified]
                public static int Add(int a, int b)
                {
                    Spec.Ensures<int>(r => r == unchecked(a + b));
                    return unchecked(a + b);
                }

                [Verified]
                public static int Plain(int a, int b)
                {
                    Spec.Ensures<int>(r => r == a + b);
                    return a + b;
                }
            }
            """);
        var add = Contract(translation, "M:S.Add(System.Int32,System.Int32)");
        Assert.Empty(add.WellDefinedness);
        AssertPropositions(env, add);
        var plain = Contract(translation, "M:S.Plain(System.Int32,System.Int32)");
        // The Spec.Ensures's a + b, then the body's (#244).
        Assert.Equal([SpecObligationKind.WellDefinedOperation, SpecObligationKind.NoOverflow], plain.WellDefinedness.Select(w => w.Kind));
        // The same program: only the obligation differs.
        static Expr Value(TranslatedUnit u) => Assert.IsType<DefinitionDecl>(Assert.Single(u.Declarations)).Value.Value;
        Assert.Equal(Value(translation.Find("M:S.Plain(System.Int32,System.Int32)")!), Value(translation.Find("M:S.Add(System.Int32,System.Int32)")!));
    }

    [Fact]
    public void ASpecAssertsArithmeticHasAnOverflowObligationUnderWhatIsKnownThereAndTheProgramIsUnchanged()
    {
        // #235: the obligation is f.$wd_k after the contract's own, over σ, the parameters, the facts known at the
        // Spec.Assert (the Spec.Requires, the branch) and a local's value unfolded; the definition keeps wrapping.
        var source = """
            public static class S
            {
                [Verified]
                public static int F(int a, int b)
                {
                    Spec.Requires(a < 1000);
                    Spec.Ensures<int>(r => r == a - 1);
                    var c = b;
                    if (a > 0)
                    {
                        Spec.Assert(a * c >= unchecked(a * c));
                    }
                    return a;
                }
            }
            """;
        var (translation, env) = Translate(source);
        var f = Contract(translation, "M:S.F(System.Int32,System.Int32)");
        Assert.Equal(2, f.WellDefinedness.Length);
        var wd = f.WellDefinedness[1];
        Assert.Equal(2, wd.Index);
        Assert.Equal("Cs.S.«F(System.Int32,System.Int32)».$wd_2", wd.Theorem.Name.ToString());
        Assert.Equal(SpecObligationKind.WellDefinedOperation, wd.Kind);
        Assert.Equal(VirOverflow.Wrap, Assert.IsType<BinaryExpr>(wd.Node).Overflow);
        // ∀ σ a b (h : a < 1000) (h : 0 < a), ⦃⌜True⌝⦄ Warrant.Int32.mulChecked σ a b ⦃⇓_ => ⌜True⌝, allowed⦄
        Assert.Equal(5, wd.Binders);
        var (program, _, _, _) = Triple(Under(wd.Theorem.Type, 5));
        Assert.Equal(Expr.App(C("Warrant.Int32.mulChecked"), Expr.BVar(4), Expr.BVar(3), Expr.BVar(2)), program);
        AssertPropositions(env, f);

        // The same unit with the Spec.Assert's arithmetic unchecked has the same definition.
        var (wrapped, _) = Translate(source.Replace("a * c >= unchecked(a * c)", "unchecked(a * c >= a * c)", StringComparison.Ordinal));
        static Expr Value(TranslatedUnit u) => Assert.IsType<DefinitionDecl>(Assert.Single(u.Declarations)).Value.Value;
        Assert.Equal(Value(translation.Find("M:S.F(System.Int32,System.Int32)")!), Value(wrapped.Find("M:S.F(System.Int32,System.Int32)")!));
        Assert.Single(Contract(wrapped, "M:S.F(System.Int32,System.Int32)").WellDefinedness);
    }

    [Fact]
    public void APureBodysArithmeticHasAnOverflowObligationUnderThePathToItAndTheDefinitionIsUnchanged()
    {
        // #244: a pure method's implicit arithmetic is f.$wd_k of kind NoOverflow, after the contract's own, over σ, the
        // parameters, the Spec.Requires, the branch taken and a guard inside the expression, a local's value unfolded; the
        // definition keeps wrapping, so it is the same as with the arithmetic unchecked.
        var source = """
            public static class S
            {
                [Verified]
                public static int F(int a, int b)
                {
                    Spec.Requires(a < 1000);
                    var c = b;
                    if (a > 0)
                    {
                        return b > 0 ? a * c : 0;
                    }
                    return 0;
                }

                [Verified]
                public static int G(int a) => unchecked(a + 1);
            }
            """;
        var (translation, env) = Translate(source);
        var f = Contract(translation, "M:S.F(System.Int32,System.Int32)");
        var wd = Assert.Single(f.WellDefinedness);
        Assert.Equal(1, wd.Index);
        Assert.Equal("Cs.S.«F(System.Int32,System.Int32)».$wd_1", wd.Theorem.Name.ToString());
        Assert.Equal(SpecObligationKind.NoOverflow, wd.Kind);
        Assert.Equal(VirOverflow.Wrap, Assert.IsType<BinaryExpr>(wd.Node).Overflow);
        // ∀ σ a b (h : a < 1000) (h : 0 < a) (h : 0 < b), ⦃⌜True⌝⦄ Warrant.Int32.mulChecked σ a b ⦃⇓_ => ⌜True⌝, allowed⦄
        Assert.Equal(6, wd.Binders);
        var (program, _, _, _) = Triple(Under(wd.Theorem.Type, 6));
        Assert.Equal(Expr.App(C("Warrant.Int32.mulChecked"), Expr.BVar(5), Expr.BVar(4), Expr.BVar(3)), program);
        AssertPropositions(env, f);

        // A method with no contract and no implicit arithmetic still has no obligation.
        Assert.Null(translation.Find("M:S.G(System.Int32)")!.Contract);

        // The same unit with the arithmetic unchecked has the same definition and no body obligation.
        var (wrapped, _) = Translate(source.Replace("a * c", "unchecked(a * c)", StringComparison.Ordinal));
        static Expr Value(TranslatedUnit u) => Assert.IsType<DefinitionDecl>(Assert.Single(u.Declarations)).Value.Value;
        Assert.Equal(Value(translation.Find("M:S.F(System.Int32,System.Int32)")!), Value(wrapped.Find("M:S.F(System.Int32,System.Int32)")!));
        Assert.Empty(Contract(wrapped, "M:S.F(System.Int32,System.Int32)").WellDefinedness);
    }

    [Fact]
    public void ATheoremStatementsArithmeticHasAnOverflowObligationUnderItsGuardsAndBinders()
    {
        // #236: a theorem's statement is translated as a Spec expression is: T.$wd_k over σ, the parameters, the
        // variables of Spec.ForAll and the guards; the statement itself is the same term as without them.
        var (translation, env) = Translate("""
            public static class S
            {
                [Verified]
                public static int Half(int x)
                {
                    Spec.Requires(x >= 0);
                    return x / 2;
                }

                [Theorem]
                static Proof Guarded(int a) => Prove.That(Spec.Implies(a < 10, Spec.ForAll<int>(y => y * a == a * y)));

                [Theorem]
                static Proof Calls(int a) => Prove.That(a < 0 || Half(a) <= a);

                [Theorem]
                static Proof Wraps(int a) => Prove.That(unchecked(a + 1) != a);
            }
            """);
        var guarded = translation.Find("M:S.Guarded(System.Int32)")!;
        Assert.Equal(2, guarded.WellDefinedness.Length);
        var wd = guarded.WellDefinedness[0];
        Assert.Equal(SpecObligationKind.WellDefinedOperation, wd.Kind);
        Assert.Equal("Cs.S.«Guarded(System.Int32)».$wd_1", wd.Theorem.Name.ToString());
        Assert.Equal(BinaryOp.Mul, Assert.IsType<BinaryExpr>(wd.Node).Op);
        // ∀ σ a (h : a < 10) y, ⦃⌜True⌝⦄ Warrant.Int32.mulChecked σ y a ⦃⇓_ => ⌜True⌝, allowed⦄
        Assert.Equal(4, wd.Binders);
        var (program, _, _, _) = Triple(Under(wd.Theorem.Type, 4));
        Assert.Equal(Expr.App(C("Warrant.Int32.mulChecked"), Expr.BVar(3), Expr.BVar(0), Expr.BVar(2)), program);
        // The second is also under the first's exact value, (y * a).toInt = y.toInt * a.toInt (#244).
        Assert.Equal(5, guarded.WellDefinedness[1].Binders);
        Assert.Equal(Under(guarded.WellDefinedness[1].Theorem.Type, 5).GetAppArgs()[4].GetAppFn(), C("Warrant.Int32.mulChecked"));
        foreach (var obligation in guarded.WellDefinedness)
        {
            AssertProposition(env, obligation.Theorem.Type);
        }
        AssertProposition(env, guarded.Theorem!.Type);

        // The call to Half is under ¬(a < 0), the guard of the || that encloses it.
        var calls = translation.Find("M:S.Calls(System.Int32)")!;
        var call = Assert.Single(calls.WellDefinedness);
        Assert.Equal(SpecObligationKind.CalleePrecondition, call.Kind);
        Assert.IsType<CallExpr>(call.Node);
        Assert.Equal(2, call.Binders);
        AssertProposition(env, call.Theorem.Type);

        Assert.Empty(translation.Find("M:S.Wraps(System.Int32)")!.WellDefinedness);
    }

    [Fact]
    public void ACallToAPureMethodWithRequiresInASpecExpressionHasItsPreconditionAsAnObligation()
    {
        var (translation, env) = Translate("""
            public static class S
            {
                [Verified]
                public static int Positive(int x)
                {
                    Spec.Requires(x > 0);
                    return x;
                }

                [Verified]
                public static int Uses(int x)
                {
                    Spec.Requires(x > 5);
                    Spec.Ensures<int>(r => r == Positive(x));
                    return x;
                }
            }
            """);
        var contract = Contract(translation, "M:S.Uses(System.Int32)");
        var wd = Assert.Single(contract.WellDefinedness);
        Assert.Equal(SpecObligationKind.CalleePrecondition, wd.Kind);
        Assert.IsType<CallExpr>(wd.Node);
        // ∀ x r, x > 5 → x > 0: the callee's precondition at the argument, under the caller's own Requires.
        Assert.Equal(3, wd.Binders);
        Assert.Equal(Gt(Expr.BVar(1), I(5)), Assert.IsType<ForallExpr>(Under(wd.Theorem.Type, 2)).BinderType);
        Assert.Equal(Gt(Expr.BVar(2), I(0)), Under(wd.Theorem.Type, 3));
        // Uses itself stays pure: a call in a Spec expression is a claim, never run.
        Assert.False(contract.Raising);
        AssertPropositions(env, contract);
    }

    /// <summary>
    /// A callee's <c>Spec.Requires</c> binds its own variables in the caller's context (M6 U19): with a name generator of
    /// its own, the second variable a nested <c>Spec.ForAll</c> binds would get the id of the caller's first parameter (the
    /// world is the first), and the argument <c>x</c> would be captured by <c>j</c>. Extraction rejects <c>Spec.ForAll</c>
    /// outside a theorem statement (WRT0004), so the VIR is built here: translation must not rely on that.
    /// </summary>
    [Fact]
    public void ACalleesForAllInItsRequiresDoesNotCaptureTheCallersArguments()
    {
        var extraction = TranslationCorpus.Inline("""
            public static class S
            {
                [Verified]
                public static int Positive(int x)
                {
                    Spec.Requires(x > 0);
                    return x;
                }

                [Verified]
                public static int Uses(int x)
                {
                    Spec.Requires(x > 5);
                    Spec.Ensures<int>(r => r == Positive(x));
                    return x;
                }
            }
            """);
        // Positive's Spec.Requires(x > 0) becomes Spec.Requires(Spec.ForAll<int>(i => Spec.ForAll<int>(j => x > 0))).
        var units = extraction.Units.Select(u =>
        {
            if (u.Key != "M:S.Positive(System.Int32)")
            {
                return u.Unit;
            }
            var body = Assert.IsType<BlockStmt>(u.Unit.Body);
            var stmts = body.Stmts.Select(s => s is RequiresStmt req
                ? new RequiresStmt(new ForAllExpr(1000, "i", VirType.Int32, new ForAllExpr(1001, "j", VirType.Int32, req.Condition)))
                : s);
            return u.Unit with { Body = new BlockStmt(new VirList<VirStmt>(stmts)) };
        });
        var translation = Translator.Translate(units, bundle.Env, extraction.Units.ToDictionary(u => u.Key, u => u.DisplayName, StringComparer.Ordinal));
        var env = TranslationCorpus.Admit(bundle, translation);
        var contract = Contract(translation, "M:S.Uses(System.Int32)");
        var wd = Assert.Single(contract.WellDefinedness);
        Assert.Equal(SpecObligationKind.CalleePrecondition, wd.Kind);
        // ∀ x r, x > 5 → ∀ i j, x > 0: the argument is the caller's x, four binders out, never j.
        Assert.Equal(3, wd.Binders);
        Assert.Equal(Gt(Expr.BVar(4), I(0)), Under(wd.Theorem.Type, 5));
        AssertPropositions(env, contract);
    }

    // ---- Vacuity (KTD25) ----

    [Fact]
    public void EachRequiresHasAVacuityObligationUnderTheOnesBeforeIt()
    {
        var (translation, env) = Translate("""
            public static class S
            {
                [Verified]
                public static int Never(int x)
                {
                    Spec.Requires(x > 0);
                    Spec.Requires(x < 0);
                    return x;
                }
            }
            """);
        var contract = Contract(translation, "M:S.Never(System.Int32)");
        Assert.Equal(2, contract.Vacuity.Length);
        Assert.All(contract.Vacuity, v => Assert.Equal(SpecObligationKind.Vacuity, v.Kind));
        Assert.All(contract.Vacuity, v => Assert.IsType<RequiresStmt>(v.Node));
        Assert.Equal("Cs.S.«Never(System.Int32)».$vacuous_2", contract.Vacuity[1].Theorem.Name.ToString());
        // ∀ x, x > 0 → False, and ∀ x, x > 0 → x < 0 → False
        Assert.Equal(2, contract.Vacuity[0].Binders);
        Assert.Equal(Gt(Expr.BVar(0), I(0)), Assert.IsType<ForallExpr>(Under(contract.Vacuity[0].Theorem.Type, 1)).BinderType);
        Assert.Equal(C("False"), Under(contract.Vacuity[0].Theorem.Type, 2));
        Assert.Equal(3, contract.Vacuity[1].Binders);
        Assert.Equal(Lt(Expr.BVar(1), I(0)), Assert.IsType<ForallExpr>(Under(contract.Vacuity[1].Theorem.Type, 2)).BinderType);
        Assert.Equal(C("False"), Under(contract.Vacuity[1].Theorem.Type, 3));
        AssertPropositions(env, contract);
    }

    // ---- The M6 corpus ----

    /// <summary>The M6 corpus's contracts without dependencies: each method has an obligation the kernel takes as a proposition.</summary>
    [Theory]
    [InlineData("M:Corpus.M6.Contracts.NonNegative(System.Int32)", false, false)]
    [InlineData("M:Corpus.M6.Contracts.AtMost(System.Int32,System.Int32)", false, false)]
    [InlineData("M:Corpus.M6.Contracts.Capped(System.Int32)", true, false)]
    [InlineData("M:Corpus.M6.Contracts.Average(System.Int32,System.Int32)", true, false)]
    [InlineData("M:Corpus.M6.Contracts.Same(System.Int32)", false, true)]
    public void M6CorpusContractsHaveObligations(string key, bool raising, bool script)
    {
        var result = Extraction.Extractor.Extract(CorpusSet.M6.Compile("accepted"));
        var byKey = result.Units.ToDictionary(u => u.Key, u => u.Unit, StringComparer.Ordinal);
        var closure = new Dictionary<string, VirUnit>(StringComparer.Ordinal);
        void Add(string k)
        {
            if (closure.TryAdd(k, byKey[k]))
            {
                foreach (var dep in byKey[k].Deps)
                {
                    Add(dep);
                }
            }
        }
        Add(key);
        var translation = Translator.Translate(closure.Values, bundle.Env);
        var env = TranslationCorpus.Admit(bundle, translation);
        var contract = Contract(translation, key);
        Assert.Equal(raising, contract.Raising);
        Assert.Equal(script, contract.Script is not null);
        AssertPropositions(env, contract);
    }

    // ---- Rejections ----

    [Fact]
    public void AContractOnARecursiveMethodIsATranslationError()
    {
        var units = new[]
        {
            VirUnit.Function(
                "M:S.F(System.Int32)",
                VirList.Of(new VirParam("n", VirType.Int32)),
                VirType.Int32,
                new BlockStmt(VirList.Of<VirStmt>(
                    new DecreasesStmt(new ParamExpr(VirType.Int32, 0)),
                    new EnsuresStmt(null, null, LitExpr.Bool(true)),
                    new ReturnStmt(new ParamExpr(VirType.Int32, 0)))),
                VirList<VirAssumption>.Empty,
                new VirFacts(VirOverflow.Wrap, "14", "test", "test"),
                VirList<string>.Empty),
        };
        var ex = Assert.Throws<TranslationException>(() => Translator.Translate(units, bundle.Env));
        Assert.Contains("contract on a recursive method", ex.Message, StringComparison.Ordinal);
    }
}
