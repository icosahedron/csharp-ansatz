using Warrant.Cic;
using Warrant.Kernel;
using Warrant.Lean4Export;
using Warrant.Vir;

namespace Warrant.Semantics.Tests;

/// <summary>Translation from VIR to CIC (docs/m4/05, the statement half of docs/m4/06; plan U7).</summary>
public sealed class TranslationTests(SemanticsBundleFixture bundle) : IClassFixture<SemanticsBundleFixture>
{
    private const string PayoutKey = "M:Payouts.PayoutRules.Payout(System.Int32,System.Int32,System.Int32)";

    public static TheoryData<string> Compilations => new("accepted", "refuted");

    private static Name N(string dotted) => Name.Parse(dotted);

    private static Expr C(string dotted, params Level[] levels) => Expr.Const(N(dotted), levels);

    private static Expr App(Expr f, params Expr[] args) => Expr.App(f, args);

    private static Expr Int32Lit(int n) =>
        App(C("OfNat.ofNat", Level.Zero), C("Int32"), Expr.NatLit(n), App(C("Int32.instOfNat"), Expr.NatLit(n)));

    // ---- The corpus ----

    [Theory]
    [MemberData(nameof(Compilations))]
    public void EveryUnitIsAdmitted(string compilation)
    {
        var result = TranslationCorpus.Extract(compilation);
        var translation = TranslationCorpus.Translate(result, bundle.Env);
        Assert.Equal(result.Units.Select(u => u.Key).Order(StringComparer.Ordinal), translation.Units.Select(u => u.Key).Order(StringComparer.Ordinal));
        var env = TranslationCorpus.Admit(bundle, translation);
        foreach (var unit in translation.Units.Where(u => u.Kind != VirUnitKind.Theorem))
        {
            Assert.All(unit.Declarations, d => Assert.NotNull(env.Find(Names(d)[0])));
        }
    }

    [Theory]
    [MemberData(nameof(Compilations))]
    public void EveryTheoremStatementIsAWellTypedProposition(string compilation)
    {
        var translation = TranslationCorpus.Translate(TranslationCorpus.Extract(compilation), bundle.Env);
        var env = TranslationCorpus.Admit(bundle, translation);
        var theorems = translation.Units.Where(u => u.Kind == VirUnitKind.Theorem).ToList();
        Assert.NotEmpty(theorems);
        KernelThread.Run(() =>
        {
            foreach (var unit in theorems)
            {
                var shell = unit.Theorem!;
                Assert.Equal(unit.Name, shell.Name);
                var checker = new TypeChecker(env);
                checker.Check(shell.Type);
                Assert.True(checker.IsProp(shell.Type), $"{unit.Key}: not a proposition");
                // D is a Decidable instance for exactly P.
                var decidable = Expr.App(C("Decidable"), shell.Statement.Prop);
                Assert.True(checker.IsDefEq(checker.Check(shell.Statement.Instance), decidable), $"{unit.Key}: instance type");
            }
        });
    }

    /// <summary>
    /// The statements say what the C# says: each accepted theorem is admitted with the proof expected.json names (the
    /// engine's two proof terms, docs/m4/06), and each refuted one decides to false.
    /// </summary>
    [Fact]
    public void TheoremStatementsHaveTheExpectedTruthValues()
    {
        var accepted = TranslationCorpus.Translate(TranslationCorpus.Extract("accepted"), bundle.Env);
        var env = TranslationCorpus.Admit(bundle, accepted);
        var proofs = TranslationCorpus.ExpectedProofs("accepted");
        var theorems = accepted.Units.Where(u => u.Theorem is not null).ToList();
        Assert.Equal(proofs.Keys.Order(StringComparer.Ordinal), theorems.Select(u => u.Key).Order(StringComparer.Ordinal));
        KernelThread.Run(() =>
        {
            foreach (var unit in theorems)
            {
                var shell = unit.Theorem!;
                // rfl is used only when P is an equation; decide always works for these statements.
                var proof = proofs[unit.Key] == "rfl" && shell.Type.GetAppFn() is ConstExpr { Name: var head } && head == N("Eq")
                    ? App(C("Eq.refl", Level.One), shell.Type.GetAppArgs()[0], shell.Type.GetAppArgs()[1])
                    : Decide(shell);
                Kernel.Kernel.Add(env, shell.WithProof(proof), KernelLimits.Corpus);
            }
        });

        var refuted = TranslationCorpus.Translate(TranslationCorpus.Extract("refuted"), bundle.Env);
        var renv = TranslationCorpus.Admit(bundle, refuted);
        KernelThread.Run(() =>
        {
            foreach (var shell in refuted.Units.Select(u => u.Theorem).OfType<TheoremShell>())
            {
                var decided = new TypeChecker(renv).Whnf(Operators.Decide(shell.Statement));
                Assert.Equal(C("Bool.false"), decided);
            }
        });
    }

    [Fact]
    public void TranslationIsDeterministic()
    {
        string first = Export(TranslationCorpus.Translate(TranslationCorpus.ExtractFresh("accepted"), bundle.Env));
        string second = Export(TranslationCorpus.Translate(TranslationCorpus.ExtractFresh("accepted"), bundle.Env));
        Assert.Equal(first, second);
    }

    [Fact]
    public void EveryEmittedConstantIsABundleRootOrGenerated()
    {
        var roots = BundleTests.Roots().Select(Name.Parse).ToHashSet();
        var cs = Name.From("Cs");
        var missing = new SortedSet<string>(StringComparer.Ordinal);
        foreach (var compilation in new[] { "accepted", "refuted" })
        {
            var translation = TranslationCorpus.Translate(TranslationCorpus.Extract(compilation), bundle.Env);
            foreach (var term in translation.Units.SelectMany(Terms))
            {
                ExprOps.ForEach(term, (e, _) =>
                {
                    if (e is ConstExpr c && !c.Name.StartsWith(cs) && !roots.Contains(c.Name))
                    {
                        missing.Add(c.Name.ToString());
                    }
                    return true;
                });
            }
        }
        Assert.Empty(missing);
    }

    /// <summary>Every constant in the table translation emits from, not only those the corpus happens to use, is a root.</summary>
    [Fact]
    public void EveryInitConstantTranslationCanEmitIsABundleRoot()
    {
        var roots = BundleTests.Roots().Select(Name.Parse).ToHashSet();
        var table = typeof(Init).GetFields(System.Reflection.BindingFlags.Static | System.Reflection.BindingFlags.Public)
            .Select(f => f.GetValue(null))
            .OfType<ConstExpr>()
            .Select(c => c.Name)
            .ToList();
        Assert.True(table.Count > 50, $"only {table.Count} constants found");
        Assert.All(table, n => Assert.Contains(n, roots));
    }

    [Theory]
    [InlineData("Spec.Implies(Inc(1) > 5, Inc(1) > 100)", true)]
    [InlineData("Spec.Implies(Inc(1) > 1, Inc(1) == 2)", true)]
    [InlineData("Spec.Implies(Inc(1) > 1, Inc(1) == 3)", false)]
    public void ImplicationIsAForallWithItsDecidableInstance(string claim, bool holds)
    {
        var result = TranslationCorpus.Inline($$"""
            public static class S
            {
                [Verified] public static int Inc(int x) => x + 1;
                [Theorem] static Proof Claim() => Prove.That({{claim}});
            }
            """);
        var translation = TranslationCorpus.Translate(result, bundle.Env);
        var env = TranslationCorpus.Admit(bundle, translation);
        var shell = translation.Find("M:S.Claim")!.Theorem!;
        Assert.IsType<ForallExpr>(shell.Type);
        KernelThread.Run(() =>
        {
            var checker = new TypeChecker(env);
            checker.Check(shell.Type);
            Assert.True(checker.IsProp(shell.Type));
            Assert.Equal(Literals.Bool(holds), checker.Whnf(Operators.Decide(shell.Statement)));
        });
    }

    // ---- Shapes ----

    [Fact]
    public void PayoutHasTheShapeOfDocsChapter5()
    {
        var translation = TranslationCorpus.Translate(TranslationCorpus.Extract("accepted"), bundle.Env);
        var payout = Definition(translation, PayoutKey);
        Assert.Equal(N("Cs.Payouts.PayoutRules").Append("Payout(System.Int32,System.Int32,System.Int32)"), payout.Name);

        var int32 = C("Int32");
        var lctx = new LocalContext();
        var ngen = new NameGenerator(N("expected"));
        var loss = lctx.MkLocalDecl(ngen, N("loss"), int32);
        var deductible = lctx.MkLocalDecl(ngen, N("deductible"), int32);
        var limit = lctx.MkLocalDecl(ngen, N("limit"), int32);
        var sub = App(C("HSub.hSub", Level.Zero, Level.Zero, Level.Zero), int32, int32, int32,
            App(C("instHSub", Level.Zero), int32, C("instSubInt32")), loss, deductible);
        var covered = lctx.MkLetDecl(ngen, N("covered"), int32, sub);
        var capped = App(C("ite", Level.One), int32,
            App(C("LT.lt", Level.Zero), int32, C("instLTInt32"), limit, covered), App(C("Int32.decLt"), limit, covered),
            limit, covered);
        var body = App(C("ite", Level.One), int32,
            App(C("LE.le", Level.Zero), int32, C("instLEInt32"), loss, deductible), App(C("Int32.decLe"), loss, deductible),
            Int32Lit(0), lctx.MkLambda([covered], capped));
        var expected = lctx.MkLambda([loss, deductible, limit], body);

        Assert.True(expected.AlphaEquals(payout.Value), $"expected\n{expected}\nactual\n{payout.Value}");
        Assert.True(lctx.MkPi([loss, deductible, limit], int32).AlphaEquals(payout.Type));
        // Lean's rule: one more than the largest height among the definitions the body mentions (Int32.decLt is 16).
        Assert.Equal(ReducibilityHints.Regular(17), payout.Hints);
    }

    [Fact]
    public void ShippingHasOneJoinPoint()
    {
        var translation = TranslationCorpus.Translate(TranslationCorpus.Extract("accepted"), bundle.Env);
        var shipping = Definition(translation, "M:Corpus.Locals.Shipping(System.Int32,System.Boolean,System.Boolean)");
        var joinPoints = Lets(shipping.Value).Where(l => l.Value is LamExpr).ToList();
        var jp = Assert.Single(joinPoints);
        Assert.IsType<LamExpr>(((LamExpr)jp.Value).Body); // fun (cost bonus : Int32) => …
        Assert.IsType<ForallExpr>(jp.BinderType);
    }

    [Fact]
    public void OneChangedLocalGivesALetOfAnIte()
    {
        var result = TranslationCorpus.Inline("""
            public static class S
            {
                [Verified]
                public static int Shipping(int weight, bool express, bool member)
                {
                    var cost = weight * 2;
                    var bonus = 0;
                    if (express) { cost = cost + 15; }
                    if (member) return cost - 5;
                    return cost + bonus;
                }
            }
            """);
        var translation = TranslationCorpus.Translate(result, bundle.Env);
        var shipping = Definition(translation, "M:S.Shipping(System.Int32,System.Boolean,System.Boolean)");
        var lets = Lets(shipping.Value).ToList();
        Assert.DoesNotContain(lets, l => l.Value is LamExpr);
        var cost = Assert.Single(lets, l => l.Value.GetAppFn() is ConstExpr { Name: var n } && n == N("ite"));
        Assert.Equal(N("cost"), cost.BinderName);
        TranslationCorpus.Admit(bundle, translation);
    }

    [Fact]
    public void NestedReturnIsKept()
    {
        var translation = TranslationCorpus.Translate(TranslationCorpus.Extract("accepted"), bundle.Env);
        var env = TranslationCorpus.Admit(bundle, translation);
        var f = Definition(translation, "M:Corpus.Locals.NestedReturn(System.Boolean,System.Boolean)");
        var call = App(Expr.Const(f.Name), C("Bool.true"), C("Bool.true"));
        var claim = App(C("Eq", Level.One), C("Int32"), call, Int32Lit(1));
        var proof = App(C("Eq.refl", Level.One), C("Int32"), call);
        KernelThread.Run(() => Kernel.Kernel.Add(env, new TheoremDecl(new TheoremInfo(N("Test.nestedReturn"), [], claim, proof, [N("Test.nestedReturn")]))));
    }

    [Fact]
    public void SequentialIfsGrowLinearly()
    {
        long Size(int n)
        {
            var body = string.Concat(Enumerable.Range(1, n).Select(i => $"if (c) {{ a = a + {i}; b = b + 1; }}\n"));
            var result = TranslationCorpus.Inline($$"""
                public static class Chain
                {
                    [Verified]
                    public static int F(bool c)
                    {
                        var a = 0;
                        var b = 0;
                        {{body}}
                        return a + b;
                    }
                }
                """);
            var translation = TranslationCorpus.Translate(result, bundle.Env);
            TranslationCorpus.Admit(bundle, translation);
            return Count(Definition(translation, "M:Chain.F(System.Boolean)").Value);
        }

        long s0 = Size(0), s10 = Size(10), s20 = Size(20);
        Assert.Equal(s10 - s0, s20 - s10);
    }

    [Fact]
    public void IntMinValueIsDefinitionallyInt32MinValue()
    {
        var literal = Literals.Int32(int.MinValue);
        Assert.Equal(App(C("Neg.neg", Level.Zero), C("Int32"), C("Int32.instNeg"), NatOfNat("Int32", 2147483648)), literal);
        var literal64 = Literals.Int64(long.MinValue);
        KernelThread.Run(() =>
        {
            var checker = new TypeChecker(bundle.Env);
            Assert.True(checker.IsDefEq(literal, C("Int32.minValue")));
            Assert.True(checker.IsDefEq(literal64, C("Int64.minValue")));
            Assert.False(checker.IsDefEq(literal, C("Int32.maxValue")));
        });
        Assert.Throws<TranslationException>(() => Literals.Of(VirPrimitive.Int32, 2147483648L));
        Assert.Throws<TranslationException>(() => Literals.Of(VirPrimitive.Bool, 2));
    }

    [Fact]
    public void OverloadsAndSameNamedParameterTypesGetDistinctStableNames()
    {
        const string types = """
            namespace A { public enum Status { X } }
            namespace B { public enum Status { Y } }
            """;
        const string rates = """
            public static class Rates
            {
                [Verified] public static int Fee(int x) => x;
                [Verified] public static int Fee(A.Status s) => 1;
                [Verified] public static int Fee(B.Status s) => 2;
            """;
        var without = TranslationCorpus.Translate(TranslationCorpus.Inline(types + rates + "}"), bundle.Env);
        var with = TranslationCorpus.Translate(
            TranslationCorpus.Inline(types + rates + "[Verified] public static int Fee(int x, bool y) => x; }"), bundle.Env);

        var names = with.Units.Where(u => u.Kind == VirUnitKind.Function).Select(u => u.Name).ToList();
        Assert.Equal(4, names.Distinct().Count());
        Assert.Contains(N("Cs.Rates").Append("Fee(System.Int32)"), names);
        Assert.Contains(N("Cs.Rates").Append("Fee(System.Int32,System.Boolean)"), names);
        Assert.Contains(N("Cs.Rates").Append("Fee(A.Status)"), names);
        Assert.Contains(N("Cs.Rates").Append("Fee(B.Status)"), names);
        foreach (var unit in without.Units)
        {
            Assert.Equal(unit.Name, with.Find(unit.Key)!.Name);
        }
        Assert.Equal("Rates.Fee(int, bool)", with.Display(N("Cs.Rates").Append("Fee(System.Int32,System.Boolean)")));
    }

    [Fact]
    public void ACollisionIsAnError()
    {
        var facts = new VirFacts(VirOverflow.Wrap, "14", "test", "test");
        var closed = VirUnit.TypeUnit("T:N.E", new ClosedDefinition(VirList.Of(new VirClosedMember("X", 0))), VirList<VirAssumption>.Empty, facts, VirList<string>.Empty);
        var record = VirUnit.TypeUnit("T:N.E.X", new RecordDefinition(VirList<VirField>.Empty), VirList<VirAssumption>.Empty, facts, VirList<string>.Empty);
        var ex = Assert.Throws<TranslationException>(() => Translator.Translate([closed, record], bundle.Env));
        Assert.Contains("Cs.N.E.X", ex.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ClosedSwitchIsTheRecursorWithOneArgumentPerConstructor()
    {
        var translation = TranslationCorpus.Translate(TranslationCorpus.Extract("accepted"), bundle.Env);
        var priority = Definition(translation, "M:Claims.ClaimStatuses.Priority(Claims.ClaimStatus)");
        var body = ((LamExpr)priority.Value).Body;
        Assert.Equal(C("Cs.Claims.ClaimStatus.rec", Level.One), body.GetAppFn());
        var args = body.GetAppArgs();
        // motive, then Open, Paid, Denied, Withdrawn (declaration order), then the scrutinee.
        Assert.Equal(6, args.Length);
        Assert.Equal(Expr.Lam(N("x"), C("Cs.Claims.ClaimStatus"), C("Int32")), args[0]);
        Assert.Equal([Int32Lit(2), Int32Lit(0), Int32Lit(1), Int32Lit(0)], args[1..5]);
        Assert.Equal(Expr.BVar(0), args[5]);
    }

    /// <summary>Switch statements the corpus does not reach compute what C# computes.</summary>
    [Theory]
    [InlineData("Closed(E.A)", 10)]
    [InlineData("Closed(E.B)", 20)]
    [InlineData("Closed(E.C)", 20)]
    [InlineData("Closed(E.D)", 7)]
    [InlineData("Ints(1)", 11)]
    [InlineData("Ints(2)", 11)]
    [InlineData("Ints(3)", 30)]
    [InlineData("Ints(4)", 99)]
    [InlineData("Ints(5)", 51)]
    [InlineData("Open(O.Y)", 2)]
    [InlineData("Open((O)9)", 0)]
    public void SwitchStatementsComputeWhatCSharpComputes(string call, int expected)
    {
        var result = TranslationCorpus.Inline($$"""
            [Closed] public enum E { A, B, C, D }
            public enum O { X, Y }
            public static class S
            {
                [Verified]
                public static int Closed(E e)
                {
                    var r = 0;
                    switch (e)
                    {
                        case E.A:
                            return 10;
                        case E.B or E.C:
                            r = 20;
                            break;
                        default:
                            r = 7;
                            break;
                    }
                    return r;
                }

                [Verified]
                public static int Ints(int x)
                {
                    var r = 0;
                    var s = 0;
                    switch (x)
                    {
                        case 1:
                        case 2:
                            r = 10;
                            s = 1;
                            break;
                        default:
                            return 99;
                        case 3:
                            return 30;
                        case > 4:
                            r = 50;
                            s = 1;
                            break;
                    }
                    return r + s;
                }

                [Verified]
                public static int Open(O o) => o switch { O.X => 1, O.Y => 2, _ => 0 };

                [Theorem]
                static Proof Claim() => Prove.That({{call}} == {{expected}});
            }
            """);
        var translation = TranslationCorpus.Translate(result, bundle.Env);
        var env = TranslationCorpus.Admit(bundle, translation);
        var shell = translation.Find("M:S.Claim")!.Theorem!;
        KernelThread.Run(() =>
            Kernel.Kernel.Add(env, shell.WithProof(App(C("Eq.refl", Level.One), C("Int32"), shell.Type.GetAppArgs()[1])), KernelLimits.Corpus));
    }

    [Fact]
    public void RecordEqualityComparesFields()
    {
        var translation = TranslationCorpus.Translate(TranslationCorpus.Extract("accepted"), bundle.Env);
        var env = TranslationCorpus.Admit(bundle, translation);
        Expr Payment(int id, int amount, string status) =>
            App(Expr.Const(N("Cs.Claims.Payment").Append("$mk")), Int32Lit(id), Int32Lit(amount), Expr.Const(N("Cs.Claims.PaymentStatus").Append(status)));
        var eq = Expr.Const(N("Cs.Claims.Payment").Append("$eq"));
        KernelThread.Run(() =>
        {
            var checker = new TypeChecker(env);
            Assert.Equal(C("Bool.true"), checker.Whnf(App(eq, Payment(1, 2, "Pending"), Payment(1, 2, "Pending"))));
            Assert.Equal(C("Bool.false"), checker.Whnf(App(eq, Payment(1, 2, "Pending"), Payment(1, 3, "Pending"))));
            Assert.Equal(C("Bool.false"), checker.Whnf(App(eq, Payment(1, 2, "Pending"), Payment(1, 2, "Failed"))));
        });
    }

    [Fact]
    public void ATheoremShellFixesItsNameAndType()
    {
        var translation = TranslationCorpus.Translate(TranslationCorpus.Extract("accepted"), bundle.Env);
        var unit = translation.Find("M:Payouts.PayoutTheorems.CappedAtTheLimit")!;
        var shell = unit.Theorem!;
        Assert.Empty(unit.Declarations);
        var payout = Expr.Const(N("Cs.Payouts.PayoutRules").Append("Payout(System.Int32,System.Int32,System.Int32)"));
        var call = App(payout, Int32Lit(1000), Int32Lit(250), Int32Lit(500));
        Assert.Equal(App(C("Eq", Level.One), C("Int32"), call, Int32Lit(500)), shell.Type);
        Assert.Equal(App(C("instDecidableEqInt32"), call, Int32Lit(500)), shell.Statement.Instance);
        var decl = shell.WithProof(C("Bool.true"));
        Assert.Equal(shell.Name, decl.Value.Name);
        Assert.Equal(shell.Type, decl.Value.Type);
        Assert.Empty(decl.Value.LevelParams);
    }

    // ---- Helpers ----

    private static Expr NatOfNat(string type, long n) =>
        App(C("OfNat.ofNat", Level.Zero), C(type), Expr.NatLit(n), App(C(type + ".instOfNat"), Expr.NatLit(n)));

    private static Expr Decide(TheoremShell shell) =>
        App(C("of_decide_eq_true"), shell.Statement.Prop, shell.Statement.Instance, App(C("Eq.refl", Level.One), C("Bool"), C("Bool.true")));

    private static DefinitionInfo Definition(Translation translation, string key)
    {
        var unit = translation.Find(key) ?? throw new InvalidOperationException($"no unit {key}");
        return Assert.IsType<DefinitionDecl>(Assert.Single(unit.Declarations)).Value;
    }

    private static List<Name> Names(KernelDeclaration declaration) => declaration switch
    {
        DefinitionDecl d => [d.Value.Name],
        InductiveDecl i => [.. i.Types.Select(t => t.Name), .. i.Types.SelectMany(t => t.Constructors).Select(c => c.Name)],
        _ => throw new InvalidOperationException(declaration.GetType().Name),
    };

    private static IEnumerable<Expr> Terms(TranslatedUnit unit)
    {
        foreach (var declaration in unit.Declarations)
        {
            switch (declaration)
            {
                case DefinitionDecl d:
                    yield return d.Value.Type;
                    yield return d.Value.DefinitionValue;
                    break;
                case InductiveDecl i:
                    foreach (var t in i.Types)
                    {
                        yield return t.Type;
                        foreach (var c in t.Constructors)
                        {
                            yield return c.Type;
                        }
                    }
                    break;
            }
        }
        if (unit.Theorem is { } shell)
        {
            yield return shell.Statement.Prop;
            yield return shell.Statement.Instance;
        }
    }

    private static IEnumerable<LetExpr> Lets(Expr e)
    {
        var lets = new List<LetExpr>();
        ExprOps.ForEach(e, (x, _) =>
        {
            if (x is LetExpr l)
            {
                lets.Add(l);
            }
            return true;
        });
        return lets;
    }

    /// <summary>The term's size as a tree: shared subterms count once per occurrence, so copying shows.</summary>
    private static long Count(Expr e) => e switch
    {
        AppExpr a => 1 + Count(a.Fn) + Count(a.Arg),
        BindingExpr b => 1 + Count(b.BinderType) + Count(b.Body),
        LetExpr l => 1 + Count(l.BinderType) + Count(l.Value) + Count(l.Body),
        ProjExpr p => 1 + Count(p.Struct),
        _ => 1,
    };

    /// <summary>The admitted declarations as NDJSON, as the engine will export them.</summary>
    private string Export(Translation translation)
    {
        var env = TranslationCorpus.Admit(bundle, translation);
        using var stream = new MemoryStream();
        using (var writer = new Lean4ExportWriter(stream, leaveOpen: true))
        {
            foreach (var declaration in translation.Units.SelectMany(u => u.Declarations))
            {
                writer.Write(AdmittedDeclarations.Of(env, declaration));
            }
            foreach (var shell in translation.Units.Select(u => u.Theorem).OfType<TheoremShell>())
            {
                writer.Write(new ConstantDeclaration(new AxiomInfo(shell.Name, [], shell.Type, false)));
                writer.Write(new ConstantDeclaration(new AxiomInfo(shell.Name.Append("$instance"), [], shell.Statement.Instance, false)));
            }
        }
        return System.Text.Encoding.UTF8.GetString(stream.ToArray());
    }
}
