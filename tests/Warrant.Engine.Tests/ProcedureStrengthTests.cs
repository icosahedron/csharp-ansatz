using Warrant.Engine.Contracts;

namespace Warrant.Engine.Tests;

/// <summary>
/// What the default procedure and <c>Tactic.Omega()</c> used to leave unproved (#216, #217, #227, #237, #245, #257): a
/// case split on a <c>bool</c> or nullable, a <c>decimal</c> <c>if</c> and literal read by omega, and products bounded
/// under their bounds. docs/proving/proofs-that-work.md runs these examples.
/// </summary>
public sealed class ProcedureStrengthTests(EngineFixture engine) : IClassFixture<EngineFixture>
{
    private EngineResult Run(string source) =>
        Pipeline.Run(EngineCorpus.Inputs(EngineCorpus.Inline(source)), engine.Bundle, engine.Options);

    private static string Wrap(string members) => $"public static class S\n{{\n{members}\n}}\n";

    private static string Describe(UnitOutcome? outcome) =>
        outcome is NotProvedOutcome n ? string.Join("\n----\n", n.Vcs.Select(v => $"{v.Kind}: {v.Message}\n{v.Goals}").Prepend(n.Message + "\n" + n.Goals)) : $"{outcome}";

    private static void Proved(UnitOutcome? outcome) =>
        Assert.True(outcome is TranslatedOutcome t && t.Declarations.Any(d => d is Kernel.TheoremDecl), Describe(outcome));

    [Fact]
    public void ABoolEnsuresThatNeedsACaseSplitOnABoolParameterIsProved()
    {
        // #227: `!flagged || r` holds by cases on `flagged`, which omega does not make.
        var source = Wrap("""
            [Verified]
            public static bool NeedsReview(int amount, int threshold, bool flagged)
            {
                Spec.Ensures<bool>(r => !flagged || r);
                return amount > threshold || flagged;
            }
            """);
        Proved(Run(source).Find("M:S.NeedsReview(System.Int32,System.Int32,System.Boolean)"));
    }

    [Fact]
    public void AConditionalEnsuresOverANullTestIsProved()
    {
        // #245: the null test stays a Bool fact (`x.isNone = true`) in the goal until it is split into its two values.
        var source = """
            #nullable enable
            public sealed record Refund(int Id, int? Days);

            """ + Wrap("""
            [Verified]
            public static int DaysOrZero(int? x)
            {
                Spec.Ensures<int>(r => x is null ? r == 0 : r == x.Value);
                return x is null ? 0 : x.Value;
            }

            [Verified]
            public static int RefundDaysOrZero(Refund refund)
            {
                Spec.Ensures<int>(r => refund.Days is null ? r == 0 : r == refund.Days.Value);
                return refund.Days is null ? 0 : refund.Days.Value;
            }
            """);
        var result = Run(source);
        Proved(result.Find("M:S.DaysOrZero(System.Nullable{System.Int32})"));
        Proved(result.Find("M:S.RefundDaysOrZero(Refund)"));
    }

    [Fact]
    public void DecimalMaxAndMinOverParametersAreProvable()
    {
        // #216: Math.Max unfolds to an `if` on decimals, which omega reads once `units` moves inside it.
        var result = Run(Wrap("""
            [Verified] public static decimal Larger(decimal a, decimal b) => System.Math.Max(a, b);
            [Verified] public static decimal Smaller(decimal a, decimal b) => System.Math.Min(a, b);

            [Theorem]
            static Proof LargerIsAtLeastTheFirst(decimal a, decimal b) =>
                Prove.That(Larger(a, b) >= a)
                     .By(Tactic.Unfold(nameof(Larger)), Tactic.Simp(Lean.Const("Warrant.Decimal.max_def"), Lean.Const("Warrant.Decimal.le_iff")), Tactic.Omega());

            [Theorem]
            static Proof SmallerOfOrderedIsTheFirst(decimal a, decimal b) =>
                Prove.That(Spec.Implies(a <= b, Smaller(a, b) <= a))
                     .By(Tactic.Unfold(nameof(Smaller)), Tactic.Simp(Lean.Const("Warrant.Decimal.min_def"), Lean.Const("Warrant.Decimal.lt_iff"), Lean.Const("Warrant.Decimal.le_iff")), Tactic.Omega());
            """));
        foreach (var key in new[] { "M:S.LargerIsAtLeastTheFirst(System.Decimal,System.Decimal)", "M:S.SmallerOfOrderedIsTheFirst(System.Decimal,System.Decimal)" })
        {
            var outcome = result.Find(key);
            Assert.True(outcome is ProvedOutcome { By: ProofKind.Script }, $"{key}: {Describe(outcome)}");
        }
    }

    [Fact]
    public void ADecimalLiteralIsReadByOmega()
    {
        // #217: `units` of a literal is a closed integer, which Tactic.Omega() states when omega alone fails.
        var result = Run(Wrap("""
            [Theorem]
            static Proof NegatingAPositiveMakesItSmaller(decimal a) =>
                Prove.That(Spec.Implies(a > 0m, -a < a))
                     .By(Tactic.Simp(Lean.Const("Warrant.Decimal.lt_iff"), Lean.Const("Warrant.Decimal.units_neg")), Tactic.Omega());

            [Theorem]
            static Proof BelowAThousandIsBelowTenThousand(decimal a) =>
                Prove.That(Spec.Implies(a < 1000.5m && a > -0.25m, a < 10000m && a >= -1m))
                     .By(Tactic.Simp(Lean.Const("Warrant.Decimal.lt_iff"), Lean.Const("Warrant.Decimal.le_iff")), Tactic.Omega());
            """));
        foreach (var key in new[] { "M:S.NegatingAPositiveMakesItSmaller(System.Decimal)", "M:S.BelowAThousandIsBelowTenThousand(System.Decimal)" })
        {
            var outcome = result.Find(key);
            Assert.True(outcome is ProvedOutcome { By: ProofKind.Script }, $"{key}: {Describe(outcome)}");
        }
    }

    [Fact]
    public void AProductOfTwoBoundedVariablesIsBounded()
    {
        // #257: omega is linear, so `price * quantity` gets no bound from the Spec.Requires without a product step.
        var source = Wrap("""
            [Verified]
            public static int Total(int price, int quantity)
            {
                Spec.Requires(0 <= price && price <= 10000 && 0 <= quantity && quantity <= 1000);
                Spec.Ensures<int>(r => r >= 0 && r <= 10000000);
                return price * quantity;
            }

            [Verified]
            public static long Signed(long a, long b)
            {
                Spec.Requires(-1000 <= a && a <= 1000 && -50 <= b && b <= 2000);
                return a * b + 1;
            }
            """);
        var result = Run(source);
        Proved(result.Find("M:S.Total(System.Int32,System.Int32)"));
        Proved(result.Find("M:S.Signed(System.Int64,System.Int64)"));
    }

    [Fact]
    public void ABoolEnsuresThatIsFalseInOneCaseStillFails()
    {
        // The split proves only what holds in both cases: with `flagged` true and `amount <= threshold` the result is false.
        var source = Wrap("""
            [Verified]
            public static bool NeedsReview(int amount, int threshold, bool flagged)
            {
                Spec.Ensures<bool>(r => !flagged || r);
                return amount > threshold;
            }
            """);
        var outcome = Assert.IsType<NotProvedOutcome>(Run(source).Find("M:S.NeedsReview(System.Int32,System.Int32,System.Boolean)"));
        Assert.Equal(VcKind.Postcondition, Assert.Single(outcome.Vcs).Kind);
    }

    [Fact]
    public void AFalseClaimAboutADecimalLiteralStillFails()
    {
        var outcome = Run(Wrap("""
            [Theorem]
            static Proof PositiveIsAboveOne(decimal a) =>
                Prove.That(Spec.Implies(a > 0m, a > 1m)).By(Tactic.Simp(Lean.Const("Warrant.Decimal.lt_iff")), Tactic.Omega());
            """)).Find("M:S.PositiveIsAboveOne(System.Decimal)");
        Assert.IsType<NotProvedOutcome>(outcome);
    }

    [Fact]
    public void AProductWhoseFactorHasNoLiteralBoundFailsEvenWithAProofForScript()
    {
        // The product step reads literal bounds only: `-a <= b <= a` with `a <= 1000` bounds b, but not by a literal. A pure
        // method's no-overflow obligation ($wd) is proved by the default procedure alone; a [ProofFor] script proves its
        // contract obligation, which comes after, so it cannot rescue the product (docs/m6/06).
        var source = Wrap("""
            [Verified]
            public static int Area(int a, int b)
            {
                Spec.Requires(0 <= a && a <= 1000 && -a <= b && b <= a);
                Spec.Ensures<int>(r => r <= 1000000);
                return a * b;
            }

            [ProofFor(nameof(Area))]
            static Proof AreaProof() => Prove.Contract().By(Tactic.VcGen(), Tactic.Omega());

            [Verified]
            public static int Bounded(int a, int b)
            {
                Spec.Requires(0 <= a && a <= 1000 && 0 <= b && b <= 1000);
                Spec.Ensures<int>(r => r <= 1000000);
                return a * b;
            }

            [ProofFor(nameof(Bounded))]
            static Proof BoundedProof() => Prove.Contract().By(Tactic.VcGen(), Tactic.Omega());
            """);
        // The trace records every script that runs: the script is never reached, so its strength does not matter.
        var ran = new System.Collections.Concurrent.ConcurrentBag<string>();
        var options = engine.Options with { TacticTrace = (key, _) => ran.Add(key) };
        var result = Pipeline.Run(EngineCorpus.Inputs(EngineCorpus.Inline(source)), engine.Bundle, options);
        var outcome = Assert.IsType<NotProvedOutcome>(result.Find("M:S.Area(System.Int32,System.Int32)"));
        Assert.Equal(VcKind.ArithmeticOverflow, Assert.Single(outcome.Vcs).Kind);
        Assert.DoesNotContain("M:S.Area(System.Int32,System.Int32)", ran);
        // The control: where the no-overflow obligation holds, the script runs and the trace has it under the method's key.
        Assert.Contains("M:S.Bounded(System.Int32,System.Int32)", ran);
    }

    [Fact]
    public void AnUnboundedProductOfTwoVariablesStillFails()
    {
        // The bounded-product step needs a bound on both factors; without one the obligation fails at the operation.
        var source = Wrap("""
            [Verified]
            public static int Total(int price, int quantity)
            {
                Spec.Requires(0 <= price && price <= 10000 && 0 <= quantity);
                return price * quantity;
            }
            """);
        var outcome = Assert.IsType<NotProvedOutcome>(Run(source).Find("M:S.Total(System.Int32,System.Int32)"));
        Assert.Equal(VcKind.ArithmeticOverflow, Assert.Single(outcome.Vcs).Kind);
    }

    [Fact]
    public void SeveralBoolAndNullTestsAreEachSplit()
    {
        // Review of #263: a split's own case hypothesis must not be split again, so a second bool or null test is.
        var source = """
            #nullable enable

            """ + Wrap("""
            [Verified]
            public static bool Both(int a, int t, bool f, bool g)
            {
                Spec.Ensures<bool>(r => !(f && g) || r);
                return a > t || (f && g);
            }

            [Verified]
            public static bool EitherNot(int a, int t, bool f, bool g)
            {
                Spec.Ensures<bool>(r => !f || !g || r);
                return a > t || (f & g);
            }

            [Verified]
            public static int FirstOrSecond(int? x, int? y)
            {
                Spec.Ensures<int>(r => x is null ? (y is null ? r == 0 : r == y.Value) : r == x.Value);
                return x is null ? (y is null ? 0 : y.Value) : x.Value;
            }

            [Verified]
            public static int FlaggedNull(bool f, int? x)
            {
                Spec.Ensures<int>(r => !f || (x is null ? r == 0 : r == 1));
                return x is null ? 0 : 1;
            }

            [Verified]
            public static bool SameOrLarger(int a, int t, bool f, bool g)
            {
                Spec.Ensures<bool>(r => (f == g) || r);
                return a > t || (f != g);
            }
            """);
        var result = Run(source);
        Proved(result.Find("M:S.Both(System.Int32,System.Int32,System.Boolean,System.Boolean)"));
        Proved(result.Find("M:S.EitherNot(System.Int32,System.Int32,System.Boolean,System.Boolean)"));
        Proved(result.Find("M:S.FirstOrSecond(System.Nullable{System.Int32},System.Nullable{System.Int32})"));
        Proved(result.Find("M:S.FlaggedNull(System.Boolean,System.Nullable{System.Int32})"));
        Proved(result.Find("M:S.SameOrLarger(System.Int32,System.Int32,System.Boolean,System.Boolean)"));
    }

    [Fact]
    public void AComparisonThatIsNotAFactDoesNotDisplaceAFactorsBound()
    {
        // Review of #263, round 2: a comparison inside a condition (an `if`, a `||`) is a candidate bound but not a fact,
        // and must not take the place of the Spec.Requires bound it is tighter than.
        var source = Wrap("""
            [Verified]
            public static int GuardedAbove(int a, int b)
            {
                Spec.Requires(0 <= a && a <= 10 && 0 <= b && b <= 10);
                Spec.Ensures<int>(r => r <= 50);
                if (a > 5) { return 0; }
                return a * b;
            }

            [Verified]
            public static int GuardedBelow(int a, int b)
            {
                Spec.Requires(-10 <= a && a <= 0 && -10 <= b && b <= 0);
                Spec.Ensures<int>(r => r >= 0);
                if (a <= -5) { return 0; }
                return a * b;
            }

            [Verified]
            public static int InADisjunction(int a, int b)
            {
                Spec.Requires(0 <= a && a <= 10 && 0 <= b && b <= 10);
                Spec.Ensures<int>(r => a > 3 || r <= 30);
                return a * b;
            }

            [Verified]
            public static int InAConjunctOfADisjunction(int a, int b)
            {
                Spec.Requires(0 <= a && a <= 10 && 0 <= b && b <= 10);
                Spec.Ensures<int>(r => (a > 3 || r <= 30) && r <= 100);
                return a * b;
            }
            """);
        var result = Run(source);
        foreach (var name in new[] { "GuardedAbove", "GuardedBelow", "InADisjunction", "InAConjunctOfADisjunction" })
        {
            Proved(result.Find($"M:S.{name}(System.Int32,System.Int32)"));
        }
    }

    [Fact]
    public void TheComplementOfABranchNotTakenBoundsAFactor()
    {
        // Review of #263, round 2: after `if (a < 0) return 0;` the path knows `!(a < 0)`, whose complement `0 <= a` is the
        // lower bound the product needs. On its own: its proof is the heaviest of these for the kernel (about 2.5 s).
        var source = Wrap("""
            [Verified]
            public static int ByTheComplement(int a, int b)
            {
                Spec.Requires(a <= 10 && 0 <= b && b <= 10);
                Spec.Ensures<int>(r => r >= 0);
                if (a < 0) { return 0; }
                return a * b;
            }
            """);
        Proved(Run(source).Find("M:S.ByTheComplement(System.Int32,System.Int32)"));
    }

    [Fact]
    public void TwoSidedProductBoundsProveAtTheDefaultBudget()
    {
        // Review of #263: these came back undecided at the default fuel, each factor bound being proved again at each level.
        var source = Wrap("""
            [Verified]
            public static int Closed(int a, int b)
            {
                Spec.Requires(1 <= a && a <= 99 && 1 <= b && b <= 99);
                Spec.Ensures<int>(r => r >= 1 && r <= 9801);
                return a * b;
            }

            [Verified]
            public static int Open(int a, int b)
            {
                Spec.Requires(0 < a && a < 100 && 0 < b && b < 100);
                Spec.Ensures<int>(r => r >= 1 && r <= 9801);
                return a * b;
            }

            [Verified]
            public static int Negative(int a, int b)
            {
                Spec.Requires(-5 <= a && a <= -1 && -5 <= b && b <= -1);
                Spec.Ensures<int>(r => r >= 1 && r <= 25);
                return a * b;
            }
            """);
        var result = Run(source);
        Proved(result.Find("M:S.Closed(System.Int32,System.Int32)"));
        Proved(result.Find("M:S.Open(System.Int32,System.Int32)"));
        Proved(result.Find("M:S.Negative(System.Int32,System.Int32)"));
    }
}
