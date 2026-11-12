using Warrant.Cic;
using Warrant.Kernel;
using Warrant.Vir;

namespace Warrant.Semantics.Tests;

/// <summary>
/// The decimal translation (plan M6 U21, KTD7, KTD11): each <c>decimal</c> VIR node is its <c>lean/Warrant/Decimal.lean</c>
/// or <c>Math.lean</c> model operation, and the kernel evaluates every translated method on concrete values. <c>+</c> and
/// <c>-</c> raise in any context, so a method that uses them is a <c>ClrM</c> program; comparisons, equality, unary minus,
/// literals and <c>Math.Min</c>, <c>Max</c> and <c>Abs</c> cannot raise and stay pure.
/// </summary>
public sealed class DecimalTranslationTests(SemanticsBundleFixture bundle) : IClassFixture<SemanticsBundleFixture>
{
    private static readonly Expr TypeT = Expr.Sort(Level.One);
    private static readonly Expr ClrExnT = C("Warrant.ClrExn");
    private static readonly Expr DecimalT = C("Warrant.Decimal");
    private static readonly Expr True = C("Bool.true");
    private static readonly Expr False = C("Bool.false");

    private static Name N(string dotted) => Name.Parse(dotted);

    private static Expr C(string dotted, params Level[] levels) => Expr.Const(N(dotted), levels);

    private static Expr D(decimal value) => Literals.Decimal(DecimalLitExpr.Of(value));

    private (Translation Translation, KernelEnvironment Env) Translate(string source)
    {
        var translation = TranslationCorpus.Translate(TranslationCorpus.Inline("using System;\n" + source), bundle.Env);
        return (translation, TranslationCorpus.Admit(bundle, translation));
    }

    private static DefinitionInfo Definition(Translation translation, string key) =>
        Assert.IsType<DefinitionDecl>(Assert.Single(translation.Find(key)!.Declarations)).Value;

    /// <summary>Whether the pure unit <paramref name="key"/> applied to <paramref name="args"/> reduces to <paramref name="expected"/>.</summary>
    private static bool Evaluates(KernelEnvironment env, Translation translation, string key, Expr expected, params Expr[] args) =>
        KernelThread.Run(() => new TypeChecker(env).IsDefEq(Expr.App(Expr.Const(translation.Find(key)!.Name), args), expected));

    /// <summary>
    /// Whether the raising unit <paramref name="key"/> applied to <paramref name="args"/>, run from every world, gives
    /// <paramref name="expected"/>'s <c>Except</c>, as in <see cref="MonadicTranslationTests"/>.
    /// </summary>
    private static bool Runs(KernelEnvironment env, Translation translation, string key, Expr expected, params Expr[] args)
    {
        var f = Expr.Const(translation.Find(key)!.Name);
        var sigma = Expr.BVar(1);
        var except = Expr.App(C("Except", Level.Zero, Level.Zero), ClrExnT, DecimalT);
        var stateM = Expr.App(C("StateM", Level.Zero), sigma);
        var run = Expr.App(C("StateT.run", Level.Zero, Level.Zero), sigma, C("Id", Level.Zero), except,
            Expr.App(C("ExceptT.run", Level.Zero, Level.Zero), ClrExnT, stateM, DecimalT, Expr.App(f, [sigma, .. args])),
            Expr.BVar(0));
        var program = Expr.Lam(N("σ"), TypeT, Expr.Lam(N("s"), Expr.BVar(0),
            Expr.App(C("Prod.fst", Level.Zero, Level.Zero), except, sigma, run)));
        var outcome = Expr.Lam(N("σ"), TypeT, Expr.Lam(N("s"), Expr.BVar(0), expected));
        return KernelThread.Run(() =>
        {
            var tc = new TypeChecker(env);
            tc.Check(program);
            return tc.IsDefEq(program, outcome);
        });
    }

    private static Expr Ok(Expr value) => Expr.App(C("Except.ok", Level.Zero, Level.Zero), ClrExnT, DecimalT, value);

    private static Expr Overflow => Expr.App(C("Except.error", Level.Zero, Level.Zero), ClrExnT, DecimalT, C("Warrant.ClrExn.overflow"));

    private static Expr Body(DefinitionInfo definition, int binders)
    {
        Expr body = definition.Value;
        for (int i = 0; i < binders; i++)
        {
            body = Assert.IsType<LamExpr>(body).Body;
        }
        return body;
    }

    // ---- + and - raise in any context ----

    [Fact]
    public void AMethodWhoseOnlyOperationIsDecimalAdditionIsAClrMProgram()
    {
        var (translation, env) = Translate("""
            public static class S
            {
                [Verified] public static decimal Add(decimal a, decimal b) => a + b;
                [Verified] public static decimal Sub(decimal a, decimal b) => unchecked(a - b);
            }
            """);
        const string add = "M:S.Add(System.Decimal,System.Decimal)";
        var definition = Definition(translation, add);
        // ∀ {σ : Type}, Decimal → Decimal → ClrM σ Decimal
        Assert.Equal(
            Expr.Forall(N("σ"), TypeT, Expr.Forall(N("a"), DecimalT, Expr.Forall(N("b"), DecimalT,
                Expr.App(C("Warrant.ClrM"), Expr.BVar(2), DecimalT))), BinderInfo.Implicit),
            definition.Type);
        Assert.Equal(Expr.App(C("Warrant.Decimal.add"), Expr.BVar(2), Expr.BVar(1), Expr.BVar(0)), Body(definition, 3));

        Assert.True(Runs(env, translation, add, Overflow, D(decimal.MaxValue), D(1m)));
        Assert.True(Runs(env, translation, add, Ok(D(3.75m)), D(1.5m), D(2.25m)));
        Assert.False(Runs(env, translation, add, Ok(D(decimal.MaxValue)), D(decimal.MaxValue), D(1m)), "MaxValue + 1m does not fit");

        // unchecked does not change decimal subtraction: it still raises (KTD11).
        const string sub = "M:S.Sub(System.Decimal,System.Decimal)";
        Assert.Equal(Expr.App(C("Warrant.Decimal.sub"), Expr.BVar(2), Expr.BVar(1), Expr.BVar(0)), Body(Definition(translation, sub), 3));
        Assert.True(Runs(env, translation, sub, Overflow, D(decimal.MinValue), D(1m)));
        Assert.True(Runs(env, translation, sub, Ok(D(-0.75m)), D(1.5m), D(2.25m)));
    }

    // ---- Literals, unary minus and Math stay pure ----

    [Fact]
    public void LiteralsUnaryMinusAndMathArePure()
    {
        var (translation, env) = Translate("""
            public static class S
            {
                [Verified] public static decimal Price() => 1.50m;
                [Verified] public static decimal Negate(decimal a) => -a;
                [Verified] public static decimal Same(decimal a) => +a;
                [Verified] public static decimal Smaller(decimal a, decimal b) => Math.Min(a, b);
                [Verified] public static decimal Larger(decimal a, decimal b) => Math.Max(a, b);
                [Verified] public static decimal Magnitude(decimal a) => Math.Abs(a);
            }
            """);
        var price = Definition(translation, "M:S.Price");
        Assert.Equal(DecimalT, price.Type);
        Assert.Equal(D(1.50m), price.Value);
        Assert.Equal(Expr.Forall(N("a"), DecimalT, DecimalT), Definition(translation, "M:S.Negate(System.Decimal)").Type);
        Assert.Equal(Expr.App(C("Warrant.Decimal.neg"), Expr.BVar(0)), Body(Definition(translation, "M:S.Negate(System.Decimal)"), 1));

        Assert.True(Evaluates(env, translation, "M:S.Negate(System.Decimal)", D(-2.5m), D(2.5m)));
        // Negating zero gives negative zero, as on the CLR.
        Assert.True(Evaluates(env, translation, "M:S.Negate(System.Decimal)", Literals.Decimal(new DecimalLitExpr(true, 0, 0)), D(0m)));
        Assert.False(Evaluates(env, translation, "M:S.Negate(System.Decimal)", D(0m), D(0m)), "-0m is not 0m's representation");
        Assert.True(Evaluates(env, translation, "M:S.Same(System.Decimal)", D(2.50m), D(2.50m)));
        // Min and Max return an operand, keeping its scale: Math.Min(1.0m, 1.00m) is 1.00m, Math.Max(1.0m, 1.00m) is 1.0m.
        Assert.True(Evaluates(env, translation, "M:S.Smaller(System.Decimal,System.Decimal)", D(Math.Min(1.0m, 1.00m)), D(1.0m), D(1.00m)));
        Assert.True(Evaluates(env, translation, "M:S.Larger(System.Decimal,System.Decimal)", D(Math.Max(1.0m, 1.00m)), D(1.0m), D(1.00m)));
        Assert.True(Evaluates(env, translation, "M:S.Larger(System.Decimal,System.Decimal)", D(3m), D(-2m), D(3m)));
        Assert.True(Evaluates(env, translation, "M:S.Magnitude(System.Decimal)", D(2.5m), D(-2.5m)));
        Assert.True(Evaluates(env, translation, "M:S.Magnitude(System.Decimal)", D(decimal.MaxValue), D(decimal.MinValue)));
    }

    // ---- Comparisons and equality by value ----

    [Fact]
    public void ComparisonsAndEqualityCompareValues()
    {
        var (translation, env) = Translate("""
            public static class S
            {
                [Verified] public static bool Eq(decimal a, decimal b) => a == b;
                [Verified] public static bool Ne(decimal a, decimal b) => a != b;
                [Verified] public static bool Lt(decimal a, decimal b) => a < b;
                [Verified] public static bool Le(decimal a, decimal b) => a <= b;
                [Verified] public static bool Gt(decimal a, decimal b) => a > b;
                [Verified] public static bool Ge(decimal a, decimal b) => a >= b;
                [Verified] public static int Sign(decimal a) => a < 0m ? -1 : a == 0m ? 0 : 1;
            }
            """);
        bool Is(string name, bool expected, decimal a, decimal b) =>
            Evaluates(env, translation, $"M:S.{name}(System.Decimal,System.Decimal)", expected ? True : False, D(a), D(b));

        foreach (var (a, b) in new[] { (1.0m, 1.00m), (1m, 2m), (2m, 1m), (-0m, 0m), (-1.5m, 1.5m), (decimal.MinValue, decimal.MaxValue), (0.0000000000000000000000000001m, 0m) })
        {
            Assert.True(Is("Eq", a == b, a, b), $"{a} == {b}");
            Assert.True(Is("Ne", a != b, a, b), $"{a} != {b}");
            Assert.True(Is("Lt", a < b, a, b), $"{a} < {b}");
            Assert.True(Is("Le", a <= b, a, b), $"{a} <= {b}");
            Assert.True(Is("Gt", a > b, a, b), $"{a} > {b}");
            Assert.True(Is("Ge", a >= b, a, b), $"{a} >= {b}");
        }
        Assert.True(Is("Eq", true, 1.0m, 1.00m), "1.0m == 1.00m");

        var eq = Body(Definition(translation, "M:S.Eq(System.Decimal,System.Decimal)"), 2);
        // decide (Warrant.Decimal.eq a b) with Warrant.Decimal.decEq a b
        var prop = Expr.App(C("Warrant.Decimal.eq"), Expr.BVar(1), Expr.BVar(0));
        Assert.Equal(Expr.App(C("Decidable.decide"), prop, Expr.App(C("Warrant.Decimal.decEq"), Expr.BVar(1), Expr.BVar(0))), eq);

        Assert.True(Evaluates(env, translation, "M:S.Sign(System.Decimal)", Literals.Int32(-1), D(-0.01m)));
        Assert.True(Evaluates(env, translation, "M:S.Sign(System.Decimal)", Literals.Int32(0), D(-0.000m)));
        Assert.True(Evaluates(env, translation, "M:S.Sign(System.Decimal)", Literals.Int32(1), D(0.01m)));
    }

    [Fact]
    public void AQuantifiedStatementUsesGtAndGeOnDecimal()
    {
        var (translation, _) = Translate("""
            public static class S
            {
                [Verified] public static decimal Larger(decimal a, decimal b) => Math.Max(a, b);
                [Theorem] static Proof LargerIsAtLeastA(decimal a, decimal b) => Prove.That(Larger(a, b) >= a);
                [Theorem] static Proof LargerIsAboveSmaller(decimal a, decimal b) => Prove.That(Spec.Implies(a < b, Larger(a, b) > a));
            }
            """);
        var largerFn = Expr.Const(translation.Find("M:S.Larger(System.Decimal,System.Decimal)")!.Name);
        var larger = Expr.App(largerFn, Expr.BVar(1), Expr.BVar(0));
        // ∀ a b, GE.ge Decimal Decimal.instLE (Larger a b) a
        Assert.Equal(
            Expr.Forall(N("a"), DecimalT, Expr.Forall(N("b"), DecimalT,
                Expr.App(C("GE.ge", Level.Zero), DecimalT, C("Warrant.Decimal.instLE"), larger, Expr.BVar(1)))),
            translation.Find("M:S.LargerIsAtLeastA(System.Decimal,System.Decimal)")!.Theorem!.Type);
        // ∀ a b, a < b → GT.gt Decimal Decimal.instLT (Larger a b) a
        Assert.Equal(
            Expr.Forall(N("a"), DecimalT, Expr.Forall(N("b"), DecimalT, Expr.Forall(N("x"),
                Expr.App(C("LT.lt", Level.Zero), DecimalT, C("Warrant.Decimal.instLT"), Expr.BVar(1), Expr.BVar(0)),
                Expr.App(C("GT.gt", Level.Zero), DecimalT, C("Warrant.Decimal.instLT"), Expr.App(largerFn, Expr.BVar(2), Expr.BVar(1)), Expr.BVar(2))))),
            translation.Find("M:S.LargerIsAboveSmaller(System.Decimal,System.Decimal)")!.Theorem!.Type);
    }

    // ---- Records compare a decimal field by value ----

    [Fact]
    public void ARecordsEqualityComparesADecimalFieldByValue()
    {
        var (translation, env) = Translate("""
            public sealed record P(decimal Amount);
            public sealed record Line(P Price, int Count, decimal Discount);
            public static class S
            {
                [Verified] public static bool Same() => new P(1.0m) == new P(1.00m);
                [Verified] public static bool Different() => new P(1.0m) == new P(1.01m);
                [Verified] public static bool SameLine(decimal a, decimal b) => new Line(new P(a), 1, 0.10m) == new Line(new P(b), 1, 0.1m);
                [Verified] public static decimal Amount(P p) => p.Amount;
                [Verified] public static decimal OrZero(decimal? d) => d ?? 0m;
            }
            """);
        Assert.True(Evaluates(env, translation, "M:S.Same", True));
        Assert.True(Evaluates(env, translation, "M:S.Different", False));
        Assert.True(Evaluates(env, translation, "M:S.SameLine(System.Decimal,System.Decimal)", True, D(2.50m), D(2.5m)));
        Assert.True(Evaluates(env, translation, "M:S.SameLine(System.Decimal,System.Decimal)", False, D(2.50m), D(2.51m)));
        Assert.True(Evaluates(env, translation, "M:S.OrZero(System.Nullable{System.Decimal})", D(0m),
            Expr.App(C("Option.none", Level.Zero), DecimalT)));
        Assert.True(Evaluates(env, translation, "M:S.OrZero(System.Nullable{System.Decimal})", D(4.2m),
            Expr.App(C("Option.some", Level.Zero), DecimalT, D(4.2m))));
    }

    // ---- What stays an error ----

    [Fact]
    public void AComparisonWhoseKindDoesNotMatchItsOperandsIsAnError()
    {
        var facts = new VirFacts(VirOverflow.Wrap, "14", "test", "test");
        var x = new ParamExpr(VirType.Int32, 0);
        VirUnit Fn(VirExpr condition) => VirUnit.Function("M:C.F(System.Int32)", VirList.Of(new VirParam("x", VirType.Int32)), VirType.Int32,
            new CondExpr(VirType.Int32, condition, x, x), VirList<VirAssumption>.Empty, facts, VirList<string>.Empty);
        Assert.Throws<TranslationException>(() => Translator.Translate([Fn(new CompareExpr(CompareOp.Eq, CompareKind.Decimal, x, x))], bundle.Env));
        Assert.Throws<TranslationException>(() => Translator.Translate(
            [Fn(new CompareExpr(CompareOp.Lt, CompareKind.Int, DecimalLitExpr.Of(1m), DecimalLitExpr.Of(2m)))], bundle.Env));
    }
}
