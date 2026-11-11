using Warrant.Cic;
using Warrant.Kernel;
using Warrant.Vir;

namespace Warrant.Semantics.Tests;

/// <summary>
/// The monadic translation (plan M6 U9, KTD4, KTD11): a unit that can raise is a <c>ClrM</c> program, and every other unit
/// keeps its pure translation. Programs are evaluated by the kernel from an arbitrary world, comparing the <c>Except</c>
/// component of the result (#110), as U3's CLR-agreement rows do.
/// </summary>
public sealed class MonadicTranslationTests(SemanticsBundleFixture bundle) : IClassFixture<SemanticsBundleFixture>
{
    private static readonly Expr TypeT = Expr.Sort(Level.One);
    private static readonly Expr ClrExnT = C("Warrant.ClrExn");
    private static readonly Expr Int32T = C("Int32");
    private static readonly Expr BoolT = C("Bool");

    private static Name N(string dotted) => Name.Parse(dotted);

    private static Expr C(string dotted, params Level[] levels) => Expr.Const(N(dotted), levels);

    private static Expr I(int n) => Literals.Int32(n);

    private static Expr Exn(string ctor) => C("Warrant.ClrExn." + ctor);

    private static Expr Thrown(string key) => Expr.App(C("Warrant.ClrExn.thrown"), Expr.StrLit(key));

    private const string ArgumentException = "T:System.ArgumentException";

    private (Translation Translation, KernelEnvironment Env) Translate(string source)
    {
        var translation = TranslationCorpus.Translate(TranslationCorpus.Inline("using System;\n" + source), bundle.Env);
        return (translation, TranslationCorpus.Admit(bundle, translation));
    }

    private static DefinitionInfo Definition(Translation translation, string key) =>
        Assert.IsType<DefinitionDecl>(Assert.Single(translation.Find(key)!.Declarations)).Value;

    /// <summary>
    /// Whether the raising unit <paramref name="key"/> applied to <paramref name="args"/>, run from every world, gives
    /// <paramref name="expected"/>'s <c>Except</c>: <c>fun σ s => ((f σ args) s).1</c> against <c>fun σ s => expected</c>.
    /// </summary>
    private static bool Runs(KernelEnvironment env, Translation translation, string key, Expr result, Expr expected, params Expr[] args)
    {
        var f = Expr.Const(translation.Find(key)!.Name);
        var sigma = Expr.BVar(1);
        var except = Expr.App(C("Except", Level.Zero, Level.Zero), ClrExnT, result);
        var stateM = Expr.App(C("StateM", Level.Zero), sigma);
        var run = Expr.App(C("StateT.run", Level.Zero, Level.Zero), sigma, C("Id", Level.Zero), except,
            Expr.App(C("ExceptT.run", Level.Zero, Level.Zero), ClrExnT, stateM, result, Expr.App(f, [sigma, .. args])),
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

    private static Expr Ok(Expr type, Expr value) => Expr.App(C("Except.ok", Level.Zero, Level.Zero), ClrExnT, type, value);

    private static Expr Error(Expr type, Expr exn) => Expr.App(C("Except.error", Level.Zero, Level.Zero), ClrExnT, type, exn);

    /// <summary>Whether the pure unit <paramref name="key"/> applied to <paramref name="args"/> reduces to <paramref name="expected"/>.</summary>
    private static bool Evaluates(KernelEnvironment env, Translation translation, string key, Expr expected, params Expr[] args) =>
        KernelThread.Run(() => new TypeChecker(env).IsDefEq(Expr.App(Expr.Const(translation.Find(key)!.Name), args), expected));

    /// <summary><c>∀ {σ : Type}, params → ClrM σ R</c>, the type of a unit that can raise.</summary>
    private static void AssertRaisingType(DefinitionInfo definition, Expr returns, params Expr[] parameters)
    {
        var type = Assert.IsType<ForallExpr>(definition.Type);
        Assert.Equal(BinderInfo.Implicit, type.BinderInfo);
        Assert.Equal(TypeT, type.BinderType);
        Expr body = type.Body;
        foreach (var p in parameters)
        {
            var binder = Assert.IsType<ForallExpr>(body);
            Assert.Equal(p, binder.BinderType);
            body = binder.Body;
        }
        Assert.Equal(Expr.App(C("Warrant.ClrM"), Expr.BVar(parameters.Length), returns), body);
    }

    // ---- Pure units keep their translation ----

    [Fact]
    public void AMethodWithOnlyIntArithmeticTranslatesAsItDidAlone()
    {
        const string pure = "[Verified] public static int Add(int a, int b) => a * 2 + b;";
        var (alone, _) = Translate($"public static class S {{ {pure} }}");
        var (mixed, _) = Translate($$"""
            public static class S
            {
                {{pure}}
                [Verified] public static int Ratio(int a, int b) => a / b;
            }
            """);
        var before = Definition(alone, "M:S.Add(System.Int32,System.Int32)");
        var after = Definition(mixed, "M:S.Add(System.Int32,System.Int32)");
        Assert.Equal(before.Type, after.Type);
        Assert.Equal(before.Value, after.Value);
        Assert.Equal(Expr.Forall(N("a"), Int32T, Expr.Forall(N("b"), Int32T, Int32T)), after.Type);
    }

    [Fact]
    public void YearModFourStaysPure()
    {
        var (translation, env) = Translate("""
            public static class S
            {
                [Verified] public static bool IsLeap(int year) => year % 4 == 0;
                [Verified] public static int Half(long x) => (int)(x / 2);
            }
            """);
        var leap = Definition(translation, "M:S.IsLeap(System.Int32)");
        Assert.Equal(Expr.Forall(N("year"), Int32T, BoolT), leap.Type);
        Assert.NotNull(ExprOps.Find(leap.Value, (e, _) => e is ConstExpr { Name: var n } && n == N("HMod.hMod")));
        Assert.Null(ExprOps.Find(leap.Value, (e, _) => e is ConstExpr { Name: var n } && n == N("Warrant.ClrM")));
        Assert.True(Evaluates(env, translation, "M:S.IsLeap(System.Int32)", C("Bool.true"), I(2024)));
        Assert.True(Evaluates(env, translation, "M:S.IsLeap(System.Int32)", C("Bool.false"), I(2023)));
        // C# truncates toward zero, as Lean's Int32 % does: -5 % 4 is -1, so -2024 % 4 is 0 and -2023 % 4 is -3.
        Assert.True(Evaluates(env, translation, "M:S.IsLeap(System.Int32)", C("Bool.true"), I(-2024)));
        Assert.True(Evaluates(env, translation, "M:S.Half(System.Int64)", I(-3), Literals.Int64(-7)));
    }

    // ---- Division and the order of operands ----

    [Fact]
    public void DivisionIsTheRaisingModelInClrM()
    {
        var (translation, env) = Translate("public static class S { [Verified] public static int Ratio(int a, int b) => a / b; }");
        const string key = "M:S.Ratio(System.Int32,System.Int32)";
        var ratio = Definition(translation, key);
        AssertRaisingType(ratio, Int32T, Int32T, Int32T);
        // fun {σ} a b => Warrant.Int32.div σ a b
        var body = ((LamExpr)((LamExpr)((LamExpr)ratio.Value).Body).Body).Body;
        Assert.Equal(Expr.App(C("Warrant.Int32.div"), Expr.BVar(2), Expr.BVar(1), Expr.BVar(0)), body);

        Assert.True(Runs(env, translation, key, Int32T, Error(Int32T, Exn("divideByZero")), I(7), I(0)));
        Assert.True(Runs(env, translation, key, Int32T, Error(Int32T, Exn("overflow")), I(int.MinValue), I(-1)));
        Assert.True(Runs(env, translation, key, Int32T, Ok(Int32T, I(-3)), I(-7), I(2)));
        Assert.False(Runs(env, translation, key, Int32T, Ok(Int32T, I(0)), I(7), I(0)), "7 / 0 is not 0");
    }

    [Fact]
    public void TheLeftOperandsExceptionWinsAndTheOperatorsCheckComesLast()
    {
        var (translation, env) = Translate("""
            public static class S
            {
                [Verified] public static int Fail(int x) => throw new ArgumentException();
                [Verified] public static int BothRaise(int a, int b) => Fail(a) / (1 / b);
                [Verified] public static int RightRaises(int a, int b) => a / (1 / b);
                [Verified] public static int LeftThenZero(int a) => Fail(a) / 0;
                [Verified] public static int Pair(int a, int b) => Math.Max(Fail(a), 1 / b);
            }
            """);
        Assert.True(Runs(env, translation, "M:S.BothRaise(System.Int32,System.Int32)", Int32T, Error(Int32T, Thrown(ArgumentException)), I(1), I(0)));
        Assert.True(Runs(env, translation, "M:S.RightRaises(System.Int32,System.Int32)", Int32T, Error(Int32T, Exn("divideByZero")), I(1), I(0)));
        Assert.True(Runs(env, translation, "M:S.LeftThenZero(System.Int32)", Int32T, Error(Int32T, Thrown(ArgumentException)), I(1)));
        Assert.True(Runs(env, translation, "M:S.Pair(System.Int32,System.Int32)", Int32T, Error(Int32T, Thrown(ArgumentException)), I(1), I(0)));
    }

    // ---- Logical operators ----

    [Fact]
    public void ShortCircuitBindsOnlyTheEvaluatedSideAndEagerBindsBoth()
    {
        var (translation, env) = Translate("""
            public static class S
            {
                [Verified] public static bool F(int y) => y > 0 ? true : throw new ArgumentException();
                [Verified] public static bool Lazy(bool x, int y) => x && F(y);
                [Verified] public static bool Eager(bool x, int y) => x & F(y);
                [Verified] public static bool LazyOr(bool x, int y) => x || F(y);
                [Verified] public static bool EagerOr(bool x, int y) => x | F(y);
            }
            """);
        var thrown = Error(BoolT, Thrown(ArgumentException));
        var @false = C("Bool.false");
        var @true = C("Bool.true");
        Assert.True(Runs(env, translation, "M:S.Lazy(System.Boolean,System.Int32)", BoolT, Ok(BoolT, @false), @false, I(0)));
        Assert.True(Runs(env, translation, "M:S.Eager(System.Boolean,System.Int32)", BoolT, thrown, @false, I(0)));
        Assert.True(Runs(env, translation, "M:S.Lazy(System.Boolean,System.Int32)", BoolT, thrown, @true, I(0)));
        Assert.True(Runs(env, translation, "M:S.Lazy(System.Boolean,System.Int32)", BoolT, Ok(BoolT, @true), @true, I(1)));
        Assert.True(Runs(env, translation, "M:S.LazyOr(System.Boolean,System.Int32)", BoolT, Ok(BoolT, @true), @true, I(0)));
        Assert.True(Runs(env, translation, "M:S.EagerOr(System.Boolean,System.Int32)", BoolT, thrown, @true, I(0)));
    }

    // ---- Calls ----

    [Fact]
    public void APureMethodCallingARaisingOneBecomesRaising()
    {
        var (translation, env) = Translate("""
            public static class S
            {
                [Verified] public static int Ratio(int a, int b) => a / b;
                [Verified] public static int Twice(int a, int b) => Ratio(a, b) * 2;
            }
            """);
        const string key = "M:S.Twice(System.Int32,System.Int32)";
        AssertRaisingType(Definition(translation, key), Int32T, Int32T, Int32T);
        Assert.True(Runs(env, translation, key, Int32T, Error(Int32T, Exn("divideByZero")), I(1), I(0)));
        Assert.True(Runs(env, translation, key, Int32T, Ok(Int32T, I(6)), I(7), I(2)));
    }

    [Fact]
    public void AThrowStatementRaisesTheThrownTypesKey()
    {
        var (translation, env) = Translate("""
            public static class S
            {
                [Verified]
                public static int Guard(int amount)
                {
                    if (amount < 0)
                    {
                        throw new ArgumentException();
                    }
                    return amount;
                }

                [Verified] public static int Always() => throw new ArgumentException();
            }
            """);
        Assert.True(Runs(env, translation, "M:S.Guard(System.Int32)", Int32T, Error(Int32T, Thrown(ArgumentException)), I(-1)));
        Assert.True(Runs(env, translation, "M:S.Guard(System.Int32)", Int32T, Ok(Int32T, I(5)), I(5)));
        Assert.True(Runs(env, translation, "M:S.Always", Int32T, Error(Int32T, Thrown(ArgumentException))));
    }

    // ---- Nullable values ----

    private const string Payments = """
        public sealed record Payment(int Id);
        public static class S
        {
            [Verified] public static int Use(Payment payment) => payment.Id;
        #pragma warning disable CS8602, CS8604
            [Verified] public static int Unchecked(Payment? payment) => Use(payment);
            [Verified] public static int IdOf(Payment? payment) => payment.Id;
        #pragma warning restore CS8602, CS8604
            [Verified]
            public static int Guarded(Payment? payment)
            {
                if (payment is null)
                {
                    return 0;
                }
                return Use(payment);
            }

            [Verified] public static int Read(int? x) => x.Value;
            [Verified] public static int OrThrow(int? x) => x ?? throw new ArgumentException();
            [Verified] public static int OrZero(int? x) => x ?? 0;
            [Verified] public static int? Wrap(int a) => a;
            [Verified] public static bool IsMissing(Payment? payment) => payment is null;
        }
        """;

    private static Expr Payment(Translation translation, int id) => Expr.App(Expr.Const(translation.Find("T:Payment")!.Name.Append("$mk")), I(id));

    private static Expr Some(Expr type, Expr value) => Expr.App(C("Option.some", Level.Zero), type, value);

    private static Expr None(Expr type) => Expr.App(C("Option.none", Level.Zero), type);

    [Fact]
    public void ANullablePassedWhereANonNullableIsRequiredRaisesNullReference()
    {
        var (translation, env) = Translate(Payments);
        var payment = Expr.Const(translation.Find("T:Payment")!.Name);
        const string key = "M:S.Unchecked(Payment)";
        AssertRaisingType(Definition(translation, key), Int32T, Expr.App(C("Option", Level.Zero), payment));
        Assert.True(Runs(env, translation, key, Int32T, Error(Int32T, Exn("nullReference")), None(payment)));
        Assert.True(Runs(env, translation, key, Int32T, Ok(Int32T, I(42)), Some(payment, Payment(translation, 42))));
        Assert.True(Runs(env, translation, "M:S.IdOf(Payment)", Int32T, Error(Int32T, Exn("nullReference")), None(payment)));
        Assert.True(Runs(env, translation, "M:S.IdOf(Payment)", Int32T, Ok(Int32T, I(7)), Some(payment, Payment(translation, 7))));
    }

    /// <summary>#163: after <c>if (p is null) return</c>, the unwrap at the argument is <c>Warrant.Nullable.nonNull</c>, whose null case the path rules out.</summary>
    [Fact]
    public void AGuardedUnwrapIsTheNonNullMatchUnderTheNullTest()
    {
        var (translation, env) = Translate(Payments);
        var payment = Expr.Const(translation.Find("T:Payment")!.Name);
        const string key = "M:S.Guarded(Payment)";
        var guarded = Definition(translation, key);
        Assert.NotNull(ExprOps.Find(guarded.Value, (e, _) => e is ConstExpr { Name: var n } && n == N("Option.isNone")));
        Assert.NotNull(ExprOps.Find(guarded.Value, (e, _) => e is ConstExpr { Name: var n } && n == N("Warrant.Nullable.nonNull")));
        Assert.True(Runs(env, translation, key, Int32T, Ok(Int32T, I(0)), None(payment)));
        Assert.True(Runs(env, translation, key, Int32T, Ok(Int32T, I(9)), Some(payment, Payment(translation, 9))));
    }

    [Fact]
    public void NullableReadsCoalesceAndWrapAgreeWithTheClr()
    {
        var (translation, env) = Translate(Payments);
        var payment = Expr.Const(translation.Find("T:Payment")!.Name);
        Assert.True(Runs(env, translation, "M:S.Read(System.Nullable{System.Int32})", Int32T, Error(Int32T, Exn("invalidOperation")), None(Int32T)));
        Assert.True(Runs(env, translation, "M:S.Read(System.Nullable{System.Int32})", Int32T, Ok(Int32T, I(3)), Some(Int32T, I(3))));
        Assert.True(Runs(env, translation, "M:S.OrThrow(System.Nullable{System.Int32})", Int32T, Error(Int32T, Thrown(ArgumentException)), None(Int32T)));
        Assert.True(Runs(env, translation, "M:S.OrThrow(System.Nullable{System.Int32})", Int32T, Ok(Int32T, I(4)), Some(Int32T, I(4))));

        // These cannot raise, so they stay pure.
        Assert.True(Evaluates(env, translation, "M:S.OrZero(System.Nullable{System.Int32})", I(0), None(Int32T)));
        Assert.True(Evaluates(env, translation, "M:S.OrZero(System.Nullable{System.Int32})", I(5), Some(Int32T, I(5))));
        Assert.True(Evaluates(env, translation, "M:S.Wrap(System.Int32)", Some(Int32T, I(5)), I(5)));
        Assert.True(Evaluates(env, translation, "M:S.IsMissing(Payment)", C("Bool.true"), None(payment)));
        Assert.True(Evaluates(env, translation, "M:S.IsMissing(Payment)", C("Bool.false"), Some(payment, Payment(translation, 1))));
    }

    // ---- Checked arithmetic, Math and Spec.Assert ----

    [Fact]
    public void CheckedArithmeticAndMathAbsRaiseOverflow()
    {
        var (translation, env) = Translate("""
            public static class S
            {
                [Verified] public static int Add(int a, int b) => checked(a + b);
                [Verified] public static int Negate(int a) => checked(-a);
                [Verified] public static int Narrow(long a) => checked((int)a);
                [Verified] public static int Size(int a) => Math.Abs(a);
                [Verified] public static int Largest(int a, int b) => Math.Max(a, b);
            }
            """);
        Assert.True(Runs(env, translation, "M:S.Add(System.Int32,System.Int32)", Int32T, Error(Int32T, Exn("overflow")), I(int.MaxValue), I(1)));
        Assert.True(Runs(env, translation, "M:S.Add(System.Int32,System.Int32)", Int32T, Ok(Int32T, I(3)), I(1), I(2)));
        Assert.True(Runs(env, translation, "M:S.Negate(System.Int32)", Int32T, Error(Int32T, Exn("overflow")), I(int.MinValue)));
        Assert.True(Runs(env, translation, "M:S.Narrow(System.Int64)", Int32T, Error(Int32T, Exn("overflow")), Literals.Int64(1L << 40)));
        Assert.True(Runs(env, translation, "M:S.Narrow(System.Int64)", Int32T, Ok(Int32T, I(-5)), Literals.Int64(-5)));
        Assert.True(Runs(env, translation, "M:S.Size(System.Int32)", Int32T, Error(Int32T, Exn("overflow")), I(int.MinValue)));
        Assert.True(Runs(env, translation, "M:S.Size(System.Int32)", Int32T, Ok(Int32T, I(5)), I(-5)));
        // Math.Max cannot raise, so it stays pure.
        Assert.Equal(Expr.Forall(N("a"), Int32T, Expr.Forall(N("b"), Int32T, Int32T)), Definition(translation, "M:S.Largest(System.Int32,System.Int32)").Type);
        Assert.True(Evaluates(env, translation, "M:S.Largest(System.Int32,System.Int32)", I(3), I(-4), I(3)));
    }

    /// <summary>KTD16: <c>Spec.Assert(c)</c> is <c>(if c then pure () else throw assertFailed) &gt;&gt;= fun _ =&gt; rest</c>.</summary>
    [Fact]
    public void SpecAssertIsACheckNode()
    {
        var (translation, env) = Translate("""
            public static class S
            {
                [Verified]
                public static int Positive(int x)
                {
                    Spec.Assert(x > 0);
                    return x;
                }
            }
            """);
        const string key = "M:S.Positive(System.Int32)";
        var body = ((LamExpr)((LamExpr)Definition(translation, key).Value).Body).Body;
        Assert.Equal(C("Bind.bind", Level.Zero, Level.Zero), body.GetAppFn());
        var check = body.GetAppArgs()[4];
        Assert.Equal(C("ite", Level.One), check.GetAppFn());
        Assert.Equal(Expr.App(C("Warrant.ClrM.throw"), Expr.BVar(1), C("Unit"), Exn("assertFailed")), check.GetAppArgs()[4]);
        Assert.True(Runs(env, translation, key, Int32T, Error(Int32T, Exn("assertFailed")), I(0)));
        Assert.True(Runs(env, translation, key, Int32T, Ok(Int32T, I(2)), I(2)));
    }

    // ---- Statements ----

    [Fact]
    public void ANonVariableDiscriminantIsLetBoundAndBranchesKeepTheirJoinPoint()
    {
        var (translation, env) = Translate("""
            public static class S
            {
                [Verified]
                public static int Pick(int x, int y)
                {
                    var r = 0;
                    switch (x + 1)
                    {
                        case 1:
                            r = 10 / y;
                            break;
                        default:
                            r = 20;
                            break;
                    }
                    return r + 1;
                }

                [Verified]
                public static int Steps(int x, int y)
                {
                    var r = 1;
                    if (x > 0)
                    {
                        r = 100 / y;
                    }
                    return r;
                }
            }
            """);
        const string pick = "M:S.Pick(System.Int32,System.Int32)";
        var body = ((LamExpr)((LamExpr)((LamExpr)Definition(translation, pick).Value).Body).Body).Body;
        // let r := 0; let x := x + 1; let jp := fun r => pure (r + 1); ite (x = 1) (bind (div σ 10 y) (fun r => jp r)) (jp 20)
        var r = Assert.IsType<LetExpr>(body);
        var discriminant = Assert.IsType<LetExpr>(r.Body);
        Assert.Equal(N("x"), discriminant.BinderName);
        var jp = Assert.IsType<LetExpr>(discriminant.Body);
        Assert.Equal(N("jp"), jp.BinderName);
        Assert.True(Runs(env, translation, pick, Int32T, Error(Int32T, Exn("divideByZero")), I(0), I(0)));
        Assert.True(Runs(env, translation, pick, Int32T, Ok(Int32T, I(6)), I(0), I(2)));
        Assert.True(Runs(env, translation, pick, Int32T, Ok(Int32T, I(21)), I(5), I(0)));

        // One changed local and a branch that can raise: a join point, not M4's let of an ite (docs/m4/05, rule 3).
        const string steps = "M:S.Steps(System.Int32,System.Int32)";
        Assert.NotNull(ExprOps.Find(Definition(translation, steps).Value, (e, _) => e is LetExpr { BinderName: var n } && n == N("jp")));
        Assert.True(Runs(env, translation, steps, Int32T, Ok(Int32T, I(1)), I(0), I(0)));
        Assert.True(Runs(env, translation, steps, Int32T, Error(Int32T, Exn("divideByZero")), I(1), I(0)));
        Assert.True(Runs(env, translation, steps, Int32T, Ok(Int32T, I(25)), I(1), I(4)));
    }

    [Fact]
    public void ARaisingInitializerIsBoundToTheLocal()
    {
        var (translation, env) = Translate("""
            public static class S
            {
                [Verified]
                public static int Share(int total, int people)
                {
                    var each = total / people;
                    return each * 2;
                }
            }
            """);
        const string key = "M:S.Share(System.Int32,System.Int32)";
        var body = ((LamExpr)((LamExpr)((LamExpr)Definition(translation, key).Value).Body).Body).Body;
        Assert.Equal(C("Bind.bind", Level.Zero, Level.Zero), body.GetAppFn());
        Assert.Equal(N("each"), Assert.IsType<LamExpr>(body.GetAppArgs()[5]).BinderName);
        Assert.True(Runs(env, translation, key, Int32T, Ok(Int32T, I(6)), I(7), I(2)));
    }

    // ---- The M6 corpus ----

    /// <summary>
    /// The M6 corpus members U9 can translate (no decimal, contract or dependency): each is admitted, and is a <c>ClrM</c>
    /// program exactly when effect inference says it can raise.
    /// </summary>
    [Theory]
    [InlineData("accepted", "M:Corpus.Rejected.Arithmetic.Halve(System.Int32)", false)]
    [InlineData("accepted", "M:Corpus.Rejected.Arithmetic.Remainder(System.Int32)", false)]
    [InlineData("accepted", "M:Corpus.M6.Effects.Biggest(System.Int32,System.Int32)", false)]
    [InlineData("accepted", "M:Corpus.M6.Effects.Smallest(System.Int64,System.Int64)", false)]
    [InlineData("accepted", "M:Corpus.M6.Effects.Guard(System.Int32)", true)]
    [InlineData("accepted", "M:Corpus.Rejected.Statements.Throws(System.Int32)", true)]
    [InlineData("accepted", "M:Corpus.Rejected.Types.NullableParameter(Corpus.Rejected.Point)", false)]
    [InlineData("accepted", "M:Corpus.Rejected.Types.ReturnsNull", false)]
    [InlineData("accepted", "M:Corpus.M6.Nullables.OrZero(System.Nullable{System.Int32})", false)]
    [InlineData("accepted", "M:Corpus.M6.Nullables.ValueWhenKnown(System.Nullable{System.Int32})", true)]
    [InlineData("refuted", "M:Corpus.Rejected.Arithmetic.CheckedAdd(System.Int32,System.Int32)", true)]
    [InlineData("refuted", "M:Corpus.M6.Refuted.Effects.Ratio(System.Int32,System.Int32)", true)]
    [InlineData("refuted", "M:Corpus.M6.Refuted.Effects.Magnitude(System.Int64)", true)]
    [InlineData("refuted", "M:Corpus.M6.Refuted.Nullables.Unchecked(Corpus.M6.Refuted.Payment)", true)]
    [InlineData("refuted", "M:Corpus.M6.Refuted.Nullables.Cast(System.Nullable{System.Int64})", true)]
    [InlineData("refuted", "M:Corpus.Rejected.Statements.CallsUnverified(System.Int32)", true)]
    public void M6CorpusMembersTranslate(string compilation, string key, bool raising)
    {
        var result = Extraction.Extractor.Extract(CorpusSet.M6.Compile(compilation));
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
        TranslationCorpus.Admit(bundle, translation);
        var definition = Definition(translation, key);
        Assert.Equal(raising, ExprOps.Find(definition.Type, (e, _) => e is ConstExpr { Name: var n } && n == N("Warrant.ClrM")) is not null);
    }
}
