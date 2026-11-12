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

                [Verified] public static int Caller(int y) => Positive(y + 1);
            }
            """);
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
        var (translation, _) = Translate("public static class S { [Verified] public static int Inc(int x) => x + 1; }");
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
