using Warrant.Cic;
using Warrant.Kernel;
using static Warrant.Meta.Tests.MetaTestSupport;

namespace Warrant.Meta.Tests;

/// <summary>
/// Golden-text tests of the goal printer (U8, KTD7): Lean's <c>PPGoal.lean</c> layout and the
/// notation table of docs/m5a/04, on terms built from the semantics bundle's real Init constants so
/// that implicit and instance arguments are hidden from the constants' actual binder infos.
/// </summary>
public sealed class GoalPrinterTests(SemanticsBundleFixture bundle) : IClassFixture<SemanticsBundleFixture>
{
    private static readonly Expr Int32 = C("Int32");
    private static readonly Expr Int64 = C("Int64");

    // Translated constants, as the translator names them (LeanNames) and displays them (Translation.Display).
    private static readonly Name Increment = N("Cs.Corpus.Refuted.Increments.Increment");
    private static readonly Name Validate = N("Cs.Claims.Payments.Validate");
    private static readonly Name Payment = N("Cs.Claims.Payment");
    private static readonly Name PaymentStatus = N("Cs.Claims.PaymentStatus");
    private static readonly Name PaymentResult = N("Cs.Claims.PaymentResult");

    private static readonly Dictionary<Name, string> Displays = new()
    {
        [Increment] = "Increment",
        [Validate] = "Validate",
        [Payment] = "Payment",
        [PaymentStatus] = "PaymentStatus",
        [PaymentResult] = "PaymentResult",
        [PaymentStatus.Append("Pending")] = "PaymentStatus.Pending",
        [PaymentResult.Append("Valid")] = "PaymentResult.Valid",
        [PaymentResult.Append("InvalidAmount")] = "PaymentResult.InvalidAmount",
        [PaymentResult.Append("InvalidStatus")] = "PaymentResult.InvalidStatus",
    };

    private static readonly string[] PaymentFields = ["Id", "Amount", "Status"];

    private static readonly NotationNames Names = new(
        n => Displays.GetValueOrDefault(n),
        (type, i) => type == Payment && i < PaymentFields.Length ? PaymentFields[i] : null);

    private GoalPrinter Printer(NotationNames? names = null) => new(bundle.Env, names ?? Names);

    private MetaM NewBundleMeta() => new(bundle.Env);

    // ------------------------------------------------------------------ term builders

    private static ConstExpr C(string name, params Level[] levels) => Expr.Const(N(name), levels);

    private static Expr Lit(int n) =>
        Expr.App(C("OfNat.ofNat", Level.Zero), Int32, Expr.NatLit(n), Expr.App(C("Int32.instOfNat"), Expr.NatLit(n)));

    private static Expr Add(Expr a, Expr b) =>
        Expr.App(C("HAdd.hAdd", Level.Zero, Level.Zero, Level.Zero), Int32, Int32, Int32, Expr.App(C("instHAdd", Level.Zero), Int32, C("instAddInt32")), a, b);

    private static Expr Sub(Expr a, Expr b) =>
        Expr.App(C("HSub.hSub", Level.Zero, Level.Zero, Level.Zero), Int32, Int32, Int32, Expr.App(C("instHSub", Level.Zero), Int32, C("instSubInt32")), a, b);

    private static Expr Mul(Expr a, Expr b) =>
        Expr.App(C("HMul.hMul", Level.Zero, Level.Zero, Level.Zero), Int32, Int32, Int32, Expr.App(C("instHMul", Level.Zero), Int32, C("instMulInt32")), a, b);

    private static Expr Neg(Expr a) => Expr.App(C("Neg.neg", Level.Zero), Int32, C("Int32.instNeg"), a);

    private static Expr Gt(Expr a, Expr b) => Expr.App(C("GT.gt", Level.Zero), Int32, C("instLTInt32"), a, b);

    private static Expr Ge(Expr a, Expr b) => Expr.App(C("GE.ge", Level.Zero), Int32, C("instLEInt32"), a, b);

    private static Expr Lt(Expr a, Expr b) => Expr.App(C("LT.lt", Level.Zero), Int32, C("instLTInt32"), a, b);

    private static Expr Le(Expr a, Expr b) => Expr.App(C("LE.le", Level.Zero), Int32, C("instLEInt32"), a, b);

    private static Expr Eq(Expr type, Expr a, Expr b) => Expr.App(C("Eq", Level.One), type, a, b);

    private static Expr Ne(Expr type, Expr a, Expr b) => Expr.App(C("Ne", Level.One), type, a, b);

    private static Expr Arrow(Expr a, Expr b) => Expr.Forall(N("h"), a, b);

    private static Expr Ite(Expr type, Expr c, Expr inst, Expr t, Expr e) => Expr.App(C("ite", Level.One), type, c, inst, t, e);

    /// <summary>Makes the goal <paramref name="type"/> in the context of the hypotheses <paramref name="hyps"/>.</summary>
    private static MVarId Goal(MetaM m, (string Name, Expr Type)[] hyps, Func<Expr[], Expr> type, string? tag = null)
    {
        Expr[] xs = new Expr[hyps.Length];
        MVarId Go(int i)
        {
            if (i == hyps.Length)
            {
                return m.MkFreshExprMVar(type(xs), MetavarKind.SyntheticOpaque, tag is null ? null : N(tag)).Id;
            }
            return m.WithLocalDeclD(N(hyps[i].Name), hyps[i].Type, x =>
            {
                xs[i] = x;
                return Go(i + 1);
            });
        }
        return Go(0);
    }

    // ------------------------------------------------------------------ layout

    [Fact]
    public void TheReadmeFailureGoalPrintsAfterIntro()
    {
        var m = NewBundleMeta();
        var statement = Expr.Forall(N("x"), Int32, Gt(Add(Expr.BVar(0), Lit(1)), Expr.BVar(0)));
        var goal = m.MkFreshExprMVar(statement, MetavarKind.SyntheticOpaque).Id;

        Assert.Equal("⊢ ∀ (x : Int32), x + 1 > x", Printer().PpGoal(m.MCtx, goal));

        var (_, after) = Intro(m, goal, "x");
        Assert.Equal("x : Int32\n⊢ x + 1 > x", Printer().PpGoal(m.MCtx, after));
    }

    [Fact]
    public void TranslatedConstantsPrintByTheirDisplayNames()
    {
        var m = NewBundleMeta();
        var statement = Expr.Forall(N("x"), Int32, Gt(Expr.App(Expr.Const(Increment), Expr.BVar(0)), Expr.BVar(0)));
        var (_, goal) = Intro(m, m.MkFreshExprMVar(statement, MetavarKind.SyntheticOpaque).Id, "x");

        Assert.Equal("x : Int32\n⊢ Increment x > x", Printer().PpGoal(m.MCtx, goal));
        Assert.Equal("x : Int32\n⊢ Cs.Corpus.Refuted.Increments.Increment x > x", Printer(new NotationNames()).PpGoal(m.MCtx, goal));
    }

    [Fact]
    public void ConsecutiveHypothesesOfEqualTypeShareALine()
    {
        var m = NewBundleMeta();
        var goal = Goal(m, [("a", Int32), ("b", Int32), ("c", Int64), ("d", Int32)], xs => Le(xs[0], xs[3]));

        Assert.Equal("a b : Int32\nc : Int64\nd : Int32\n⊢ a ≤ d", Printer().PpGoal(m.MCtx, goal));
    }

    [Fact]
    public void ACaseTagLetValueAndSeveralGoalsFollowLeansLayout()
    {
        var m = NewBundleMeta();
        var (x, y, tagged) = m.WithLocalDeclD(N("x"), Int32, x =>
            m.WithLetDecl(N("y"), Int32, Add(x, Lit(1)), y =>
                (x, y, m.MkFreshExprMVar(Gt(y, x), MetavarKind.SyntheticOpaque, N("succ")).Id)));
        var plain = Goal(m, [("x", Int32)], xs => Ge(xs[0], xs[0]));

        Assert.Equal("case succ\nx : Int32\ny : Int32 := x + 1\n⊢ y > x", Printer().PpGoal(m.MCtx, tagged));
        Assert.Equal(
            "case succ\nx : Int32\ny : Int32 := x + 1\n⊢ y > x\n\nx : Int32\n⊢ x ≥ x",
            Printer().PpGoals(m.MCtx, [tagged, plain]));
        _ = (x, y);
    }

    // ------------------------------------------------------------------ notation

    [Fact]
    public void ProjectionsOfTranslatedRecordsPrintByFieldName()
    {
        var m = NewBundleMeta();
        var goal = Goal(m, [("p", Expr.Const(Payment))], xs => Gt(Expr.Proj(Payment, 1, xs[0]), Lit(0)));

        Assert.Equal("p : Payment\n⊢ p.Amount > 0", Printer().PpGoal(m.MCtx, goal));
        Assert.Equal("p : Cs.Claims.Payment\n⊢ p.2 > 0", Printer(new NotationNames()).PpGoal(m.MCtx, goal));
    }

    [Fact]
    public void IteOverTranslatedMembersPrintsAsIfThenElse()
    {
        var m = NewBundleMeta();
        var result = Expr.Const(PaymentResult);
        var goal = Goal(m, [("p", Expr.Const(Payment))], xs =>
        {
            var amount = Expr.Proj(Payment, 1, xs[0]);
            var status = Expr.Proj(Payment, 2, xs[0]);
            var pending = Expr.Const(PaymentStatus.Append("Pending"));
            var statusCheck = Ite(
                result,
                Ne(Expr.Const(PaymentStatus), status, pending),
                Expr.App(C("instDecidableNot"), Eq(Expr.Const(PaymentStatus), status, pending), Expr.Const(PaymentStatus.Append("decEq"))),
                Expr.Const(PaymentResult.Append("InvalidStatus")),
                Expr.Const(PaymentResult.Append("Valid")));
            var body = Ite(
                result,
                Le(amount, Lit(0)),
                Expr.App(C("Int32.decLe"), amount, Lit(0)),
                Expr.Const(PaymentResult.Append("InvalidAmount")),
                statusCheck);
            return Eq(result, Expr.App(Expr.Const(Validate), xs[0]), body);
        });

        Assert.Equal(
            "p : Payment\n⊢ Validate p = if p.Amount ≤ 0 then PaymentResult.InvalidAmount "
                + "else if p.Status ≠ PaymentStatus.Pending then PaymentResult.InvalidStatus else PaymentResult.Valid",
            Printer().PpGoal(m.MCtx, goal));
    }

    [Theory]
    [InlineData("(a + b) * c + a * (b + c) = a + b + c")]
    [InlineData("a - (b - c) = a - b - c")]
    [InlineData("-(a + b) = -a * b")]
    [InlineData("(a ≤ b → a < b + 1) ∧ ¬a = b ∨ a ≥ b")]
    public void ParenthesesFollowLeansPrecedences(string expected)
    {
        var m = NewBundleMeta();
        var goal = Goal(m, [("a", Int32), ("b", Int32), ("c", Int32)], xs =>
        {
            var (a, b, c) = (xs[0], xs[1], xs[2]);
            return expected switch
            {
                "(a + b) * c + a * (b + c) = a + b + c" => Eq(Int32, Add(Mul(Add(a, b), c), Mul(a, Add(b, c))), Add(Add(a, b), c)),
                "a - (b - c) = a - b - c" => Eq(Int32, Sub(a, Sub(b, c)), Sub(Sub(a, b), c)),
                "-(a + b) = -a * b" => Eq(Int32, Neg(Add(a, b)), Mul(Neg(a), b)),
                _ => Expr.App(
                    C("Or"),
                    Expr.App(C("And"), Arrow(Le(a, b), Lt(a, Add(b, Lit(1)))), Expr.App(C("Not"), Eq(Int32, a, b))),
                    Ge(a, b)),
            };
        });

        Assert.Equal("a b c : Int32\n⊢ " + expected, Printer().PpGoal(m.MCtx, goal));
    }

    [Fact]
    public void ImplicitAndInstanceArgumentsAreHiddenFromTheConstantsBinderInfos()
    {
        var m = NewBundleMeta();
        // Decidable.decide : (p : Prop) → [h : Decidable p] → Bool; Eq.refl : {α : Sort u} → (a : α) → a = a.
        var goal = Goal(m, [("x", Int32)], xs =>
        {
            var p = Gt(xs[0], Lit(0));
            var decide = Expr.App(C("Decidable.decide"), p, Expr.App(C("Int32.decLt"), Lit(0), xs[0]));
            return Eq(Eq(C("Bool"), decide, C("Bool.true")), Expr.App(C("Eq.refl", Level.One), C("Bool"), decide), Expr.App(C("Eq.refl", Level.One), C("Bool"), decide));
        });

        Assert.Equal(
            "x : Int32\n⊢ Eq.refl (Decidable.decide (x > 0)) = Eq.refl (Decidable.decide (x > 0))",
            Printer().PpGoal(m.MCtx, goal));
    }

    [Fact]
    public void BindersGroupAndExistsHidesItsType()
    {
        var m = NewBundleMeta();
        var forall = Expr.Forall(N("a"), Int32, Expr.Forall(N("b"), Int32, Arrow(Le(Expr.BVar(1), Expr.BVar(0)), Ge(Expr.BVar(1), Expr.BVar(2)))));
        var exists = Expr.App(C("Exists", Level.One), Int32, Expr.Lam(N("y"), Int32, Gt(Expr.BVar(0), Lit(0))));
        var goal = Goal(m, [], _ => Expr.App(C("And"), forall, exists));

        Assert.Equal("⊢ (∀ (a b : Int32), a ≤ b → b ≥ a) ∧ ∃ y, y > 0", Printer().PpGoal(m.MCtx, goal));
    }

    [Fact]
    public void ABoundNameThatWouldCaptureAHypothesisIsRenamed()
    {
        var m = NewBundleMeta();
        var goal = Goal(m, [("x", Int32)], xs => Expr.Forall(N("x"), Int32, Gt(Expr.BVar(0), xs[0])));

        Assert.Equal("x : Int32\n⊢ ∀ (x_1 : Int32), x_1 > x", Printer().PpGoal(m.MCtx, goal));
    }

    [Fact]
    public void UnassignedMetavariablesPrintByIndexOrUserName()
    {
        var m = NewBundleMeta();
        for (int i = 0; i < 3; i++)
        {
            m.MkFreshExprMVar(Int32);
        }
        var hole = m.MkFreshExprMVar(Int32);
        var named = m.MkFreshExprMVar(Int32, MetavarKind.Natural, N("n"));
        var goal = m.MkFreshExprMVar(Gt(hole, named), MetavarKind.SyntheticOpaque).Id;

        Assert.Equal(3, m.GetMVarDecl(hole.Id).Index);
        Assert.Equal("⊢ ?m.3 > ?n", Printer().PpGoal(m.MCtx, goal));

        m.Assign(hole.Id, Lit(7));
        Assert.Equal("⊢ 7 > ?n", Printer().PpGoal(m.MCtx, goal));
    }
}
