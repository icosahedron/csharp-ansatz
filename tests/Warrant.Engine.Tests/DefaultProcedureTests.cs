using Warrant.Engine.Contracts;
using Warrant.Vir;

namespace Warrant.Engine.Tests;

/// <summary>
/// The default procedure (plan M6 U11, KTD13, KTD14): contract obligations without a script, proved by the VC walker, then
/// the VC simp set, then omega, and every failing VC reported at its source line with its kind (#90).
/// </summary>
public sealed class DefaultProcedureTests(EngineFixture engine) : IClassFixture<EngineFixture>
{
    private EngineResult Run(string source) =>
        Pipeline.Run(EngineCorpus.Inputs(EngineCorpus.Inline(source)), engine.Bundle, engine.Options);

    private static string Wrap(string members) => $"public static class S\n{{\n{members}\n}}\n";

    /// <summary>The source text of a node of an inline source's unit.</summary>
    private static string Text(string source, string key, int? node)
    {
        var span = Reports.OutcomeText.SpanOf(EngineCorpus.Inline(source).Units.Single(u => u.Key == key).Spans, node);
        Assert.NotNull(span);
        var lines = ("using Warrant;\n" + source).Split('\n');
        Assert.Equal(span.StartLine, span.EndLine);
        return lines[span.StartLine - 1][(span.StartColumn - 1)..(span.EndColumn - 1)].Trim();
    }

    private static void Proved(UnitOutcome? outcome) =>
        Assert.True(outcome is TranslatedOutcome t && t.Declarations.Any(d => d is Kernel.TheoremDecl), Describe(outcome));

    private static string Describe(UnitOutcome? outcome) =>
        outcome is NotProvedOutcome n ? string.Join("\n----\n", n.Vcs.Select(v => $"{v.Kind}: {v.Message}\n{v.Goals}").Prepend(n.Message + "\n" + n.Goals)) : $"{outcome}";

    /// <summary>The one failing VC of a method: its kind and the source text at its node.</summary>
    private static (VcKind Kind, string Text) Failure(string source, string key, UnitOutcome? outcome)
    {
        var notProved = Assert.IsType<NotProvedOutcome>(outcome);
        var vc = Assert.Single(notProved.Vcs);
        Assert.StartsWith(VcKinds.Text(vc.Kind), notProved.Message, StringComparison.Ordinal);
        return (vc.Kind, Text(source, key, vc.Node));
    }

    private const string Ratio = "M:S.Ratio(System.Int32,System.Int32)";

    [Fact]
    public void RatioProvesWithItsRequires()
    {
        var source = Wrap("""
            [Verified]
            public static int Ratio(int a, int b)
            {
                Spec.Requires(b != 0 && b != -1);
                return a / b;
            }
            """);
        Proved(Run(source).Find(Ratio));
    }

    [Fact]
    public void RatioWithoutTheMinusOneGuardFailsAtTheDivisionAsOverflow()
    {
        var source = Wrap("""
            [Verified]
            public static int Ratio(int a, int b)
            {
                Spec.Requires(b != 0);
                return a / b;
            }
            """);
        Assert.Equal((VcKind.Overflow, "a / b"), Failure(source, Ratio, Run(source).Find(Ratio)));
    }

    [Fact]
    public void RatioWithoutARequiresFailsAtTheDivisionAsDivisionByZero()
    {
        var source = Wrap("""
            [Verified]
            public static int Ratio(int a, int b)
            {
                return a / b;
            }
            """);
        var outcome = Assert.IsType<NotProvedOutcome>(Run(source).Find(Ratio));
        // Both the zero divisor and MinValue / -1 are possible: two VCs at the one division, in that order.
        Assert.Equal([VcKind.DivisionByZero, VcKind.Overflow], outcome.Vcs.Select(v => v.Kind));
        Assert.All(outcome.Vcs, v => Assert.Equal("a / b", Text(source, Ratio, v.Node)));
    }

    // ---- checked arithmetic (#64) ----

    [Fact]
    public void CheckedAddProvesWithBothBoundsAndFailsAtThePlusWithOnlyTheUpperOnes()
    {
        var source = Wrap("""
            [Verified]
            public static int Bounded(int a, int b)
            {
                Spec.Requires(a > -1000 && a < 1000 && b > -1000 && b < 1000);
                return checked(a + b);
            }

            [Verified]
            public static int Upper(int a, int b)
            {
                Spec.Requires(a < 1000 && b < 1000);
                return checked(a + b);
            }
            """);
        var result = Run(source);
        Proved(result.Find("M:S.Bounded(System.Int32,System.Int32)"));
        Assert.Equal((VcKind.Overflow, "a + b"), Failure(source, "M:S.Upper(System.Int32,System.Int32)", result.Find("M:S.Upper(System.Int32,System.Int32)")));
    }

    // ---- a division reached only when Requires is violated ----

    [Fact]
    public void ADivisionReachedOnlyWhenRequiresIsViolatedProvesAndOneReachedOtherwiseFails()
    {
        var source = Wrap("""
            [Verified]
            public static int Unreached(int a, int b)
            {
                Spec.Requires(a > 0);
                if (a < 0)
                {
                    return a / b;
                }
                return a;
            }

            [Verified]
            public static int Reached(int a, int b)
            {
                Spec.Requires(a > 0);
                if (a > 5)
                {
                    return a / b;
                }
                return a;
            }
            """);
        var result = Run(source);
        Proved(result.Find("M:S.Unreached(System.Int32,System.Int32)"));
        var reached = Assert.IsType<NotProvedOutcome>(result.Find("M:S.Reached(System.Int32,System.Int32)"));
        Assert.Equal(VcKind.DivisionByZero, reached.Vcs[0].Kind);
        Assert.Equal("a / b", Text(source, "M:S.Reached(System.Int32,System.Int32)", reached.Vcs[0].Node));
    }

    // ---- explicit throws (#92) ----

    [Fact]
    public void AThrowRuledOutByRequiresIsNoMayThrowAndAReachableOneIs()
    {
        var source = Wrap("""
            [Verified]
            public static int Ruled(int a, int b)
            {
                Spec.Requires(b != 0);
                if (b == 0)
                {
                    throw new System.ArgumentException("b");
                }
                return a;
            }

            [Verified]
            public static int Reachable(int a, int b)
            {
                if (b == 0)
                {
                    throw new System.ArgumentException("b");
                }
                return a;
            }
            """);
        var result = Run(source);
        var ruled = result.Find("M:S.Ruled(System.Int32,System.Int32)");
        Proved(ruled);
        Assert.DoesNotContain(ruled!.Assumptions, a => a.Assumption.Kind == VirAssumptionKind.MayThrow);
        var reachable = result.Find("M:S.Reachable(System.Int32,System.Int32)");
        Proved(reachable);
        var mayThrow = Assert.Single(reachable!.Assumptions, a => a.Assumption.Kind == VirAssumptionKind.MayThrow);
        var subject = Reports.MayThrowSubject.Parse(mayThrow.Assumption.Subject);
        Assert.Equal("T:System.ArgumentException", subject.Thrown);
        Assert.Equal("throw new System.ArgumentException(\"b\");", Text(source, "M:S.Reachable(System.Int32,System.Int32)", subject.Node));
    }

    // ---- null (KTD5, #163) ----

    [Fact]
    public void ANullDereferenceGuardedByIsNotNullProvesAndAnUnguardedOneFailsAtItsLine()
    {
        var source = """
            public sealed record Payment(int Id);

            public static class S
            {
                [Verified]
                public static int Guarded(Payment? p)
                {
                    if (p is not null)
                    {
                        return p.Id;
                    }
                    return 0;
                }

            #pragma warning disable CS8602
                [Verified]
                public static int Unguarded(Payment? p)
                {
                    return p.Id;
                }
            #pragma warning restore CS8602
            }
            """;
        var result = Run(source);
        Proved(result.Find("M:S.Guarded(Payment)"));
        Assert.Equal((VcKind.NullRead, "p"), Failure(source, "M:S.Unguarded(Payment)", result.Find("M:S.Unguarded(Payment)")));
    }

    [Fact]
    public void ANullablePassedWhereANonNullValueIsRequiredProvesOnlyUnderItsGuard()
    {
        var source = """
            public sealed record Payment(int Id);

            public static class S
            {
                [Verified]
                public static int Validate(Payment p) => p.Id;

                [Verified]
                public static int Guarded(Payment? p)
                {
                    if (p is null)
                    {
                        return 0;
                    }
                    return Validate(p);
                }

            #pragma warning disable CS8604
                [Verified]
                public static int Unguarded(Payment? p)
                {
                    return Validate(p);
                }
            #pragma warning restore CS8604
            }
            """;
        var result = Run(source);
        Proved(result.Find("M:S.Guarded(Payment)"));
        Assert.Equal((VcKind.NullPassed, "p"), Failure(source, "M:S.Unguarded(Payment)", result.Find("M:S.Unguarded(Payment)")));
    }

    [Fact]
    public void ARecordsNullableFieldIsReadAfterANullTestInABodyAndInASpecExpression()
    {
        // #218: a null test of a field is a path condition about the field itself (refund.Original = none), which rewrites
        // the guard of a later read of it, as a null test of a parameter does.
        var source = """
            #nullable enable
            public sealed record Payment(int Id, decimal Amount);
            public sealed record Refund(int Id, int? Days, decimal? Fee, Payment? Original);

            """ + Wrap("""
            [Verified]
            public static int OriginalIdOrZero(Refund refund)
            {
                Spec.Requires(refund.Original is null || refund.Original.Id > 0);
                Spec.Ensures<int>(r => r >= 0);
                if (refund.Original is null) return 0;
                return refund.Original.Id;
            }

            [Verified]
            public static Refund WithoutFee(Refund refund)
            {
                Spec.Ensures<Refund>(r => r.Fee is null && r.Id == refund.Id);
                return refund with { Fee = null };
            }

            [Verified]
            public static int Unchecked(Refund refund) => refund.Original.Id;
            """);
        var result = Run(source);
        Proved(result.Find("M:S.OriginalIdOrZero(Refund)"));
        Proved(result.Find("M:S.WithoutFee(Refund)"));
        Assert.Equal((VcKind.NullRead, "refund.Original"), Failure(source, "M:S.Unchecked(Refund)", result.Find("M:S.Unchecked(Refund)")));
    }

    // ---- Spec expressions (KTD25, KTD26; moved from U10, #169) ----

    [Fact]
    public void ADivisionInRequiresFailsAtTheSpecLineWithoutAGuardAndProvesWithOne()
    {
        // The plan's guard is b != 0 alone, but a / b also overflows for int.MinValue / -1 (KTD6), so the guard that makes
        // the Spec expression well defined excludes -1 as well.
        var source = Wrap("""
            [Verified]
            public static int Unguarded(int a, int b)
            {
                Spec.Requires(a / b > 0);
                return a;
            }

            [Verified]
            public static int Guarded(int a, int b)
            {
                Spec.Requires(b != 0 && b != -1 && a / b > 0);
                return a;
            }
            """);
        var result = Run(source);
        var unguarded = Assert.IsType<NotProvedOutcome>(result.Find("M:S.Unguarded(System.Int32,System.Int32)"));
        Assert.All(unguarded.Vcs, v => Assert.Equal(VcKind.WellDefinedness, v.Kind));
        Assert.Equal("a / b", Text(source, "M:S.Unguarded(System.Int32,System.Int32)", unguarded.TacticNode));
        Proved(result.Find("M:S.Guarded(System.Int32,System.Int32)"));
    }

    [Fact]
    public void ArithmeticInEnsuresThatCanOverflowFailsAtTheEnsuresLineAndProvesWhenBounded()
    {
        // #183: arithmetic in a Spec expression does not wrap silently; it must not overflow.
        var source = Wrap("""
            [Verified]
            public static int Unbounded(int a, int b)
            {
                Spec.Ensures<int>(r => r == a + b);
                return a + b;
            }

            [Verified]
            public static int Bounded(int a, int b)
            {
                Spec.Requires(a < 1000 && a > -1000 && b < 1000 && b > -1000);
                Spec.Ensures<int>(r => r == a + b);
                return a + b;
            }
            """);
        var result = Run(source);
        var unbounded = Assert.IsType<NotProvedOutcome>(result.Find("M:S.Unbounded(System.Int32,System.Int32)"));
        Assert.All(unbounded.Vcs, v => Assert.Equal(VcKind.WellDefinedness, v.Kind));
        Assert.Equal("a + b", Text(source, "M:S.Unbounded(System.Int32,System.Int32)", unbounded.TacticNode));
        Proved(result.Find("M:S.Bounded(System.Int32,System.Int32)"));
    }

    // ---- Spec.Implies in a contract (#213) ----

    [Fact]
    public void AnEnsuresWithImpliesProvesWhenTrueAndFailsAtTheEnsuresLineWhenFalse()
    {
        var source = Wrap("""
            [Verified]
            public static int Clamp(int x)
            {
                Spec.Ensures<int>(r => Spec.Implies(x > 0, r > 0));
                return x > 0 ? x : 0;
            }

            [Verified]
            public static int Wrong(int x)
            {
                Spec.Ensures<int>(r => Spec.Implies(x > 0, r > 0));
                return unchecked(x - 1);
            }
            """);
        var result = Run(source);
        Proved(result.Find("M:S.Clamp(System.Int32)"));
        Assert.Equal(
            (VcKind.Postcondition, "Spec.Ensures<int>(r => Spec.Implies(x > 0, r > 0));"),
            Failure(source, "M:S.Wrong(System.Int32)", result.Find("M:S.Wrong(System.Int32)")));
    }

    [Fact]
    public void ImpliesAsABoolValueInAnEnsuresIsNotPOrQ()
    {
        var source = Wrap("""
            [Verified]
            public static bool Right(int x)
            {
                Spec.Ensures<bool>(r => r == Spec.Implies(x > 0, x > 1));
                // Written as !p || q: the VC simp set does not yet relate decide (x <= 0) to !decide (x > 0) in a bool equality.
                return !(x > 0) || x > 1;
            }

            [Verified]
            public static bool Wrong(int x)
            {
                Spec.Ensures<bool>(r => r == Spec.Implies(x > 0, x > 1));
                return x > 0 && x > 1;
            }
            """);
        var result = Run(source);
        Proved(result.Find("M:S.Right(System.Int32)"));
        Assert.Equal(
            (VcKind.Postcondition, "Spec.Ensures<bool>(r => r == Spec.Implies(x > 0, x > 1));"),
            Failure(source, "M:S.Wrong(System.Int32)", result.Find("M:S.Wrong(System.Int32)")));
    }

    [Fact]
    public void ArithmeticInTheConclusionOfImpliesIsWellDefinedUnderItsPremise()
    {
        // #183: x + 1 must not overflow, which holds only under the premise x < 100.
        var source = Wrap("""
            [Verified]
            public static int Guarded(int x)
            {
                Spec.Ensures<int>(r => Spec.Implies(x < 100, r == x + 1));
                return x < 100 ? x + 1 : 0;
            }

            [Verified]
            public static int Unguarded(int x)
            {
                Spec.Ensures<int>(r => Spec.Implies(x > 0, r == x + 1));
                return x > 0 ? x : 0;
            }
            """);
        var result = Run(source);
        Proved(result.Find("M:S.Guarded(System.Int32)"));
        var unguarded = Assert.IsType<NotProvedOutcome>(result.Find("M:S.Unguarded(System.Int32)"));
        Assert.Equal(VcKind.WellDefinedness, unguarded.Vcs[0].Kind);
        Assert.Equal("x + 1", Text(source, "M:S.Unguarded(System.Int32)", unguarded.Vcs[0].Node));
    }

    [Fact]
    public void ARequiresWithImpliesIsACallersPreconditionAndHasAVacuityCheck()
    {
        var source = Wrap("""
            [Verified]
            public static int Small(int x)
            {
                Spec.Requires(Spec.Implies(x > 0, x < 100));
                return x;
            }

            [Verified]
            public static int Fine() => unchecked(Small(50) + Small(-500));

            [Verified]
            public static int TooBig() => Small(500);

            [Verified]
            public static int Never(int x)
            {
                Spec.Requires(x > 0);
                Spec.Requires(Spec.Implies(x > 0, x < 0));
                return x;
            }
            """);
        var result = Run(source);
        Proved(result.Find("M:S.Small(System.Int32)"));
        Proved(result.Find("M:S.Fine"));
        Assert.Equal((VcKind.CalleePrecondition, "Small(500)"), Failure(source, "M:S.TooBig", result.Find("M:S.TooBig")));
        var never = Assert.IsType<NotProvedOutcome>(result.Find("M:S.Never(System.Int32)"));
        Assert.StartsWith("The contract is unsatisfiable", never.Message, StringComparison.Ordinal);
        Assert.Equal("Spec.Requires(Spec.Implies(x > 0, x < 0));", Text(source, "M:S.Never(System.Int32)", never.TacticNode));
    }

    [Fact]
    public void ArithmeticInATheoremThatCanOverflowFailsAtTheOperationAndProvesWhenBounded()
    {
        // #236: a theorem's statement follows the same rule: its default-context arithmetic must not overflow, whatever
        // proves the claim; explicit unchecked(...) wraps on purpose.
        var source = Wrap("""
            [Theorem]
            static Proof Unbounded(int a) =>
                Prove.That(a + 1 > a).By(Tactic.Omega());

            [Theorem]
            static Proof Bounded(int a) =>
                Prove.That(Spec.Implies(a < 1000 && a > -1000, a + 1 > a)).By(Tactic.Intro("h"), Tactic.Omega());

            [Theorem]
            static Proof Wraps() => Prove.That(unchecked(int.MaxValue + One()) == int.MinValue);

            [Theorem]
            static Proof Overflows() => Prove.That(int.MaxValue + One() == int.MinValue);

            [Theorem]
            static Proof Quantified() => Prove.That(Spec.ForAll<int>(y => Spec.Implies(y < 5, y + 1 <= 5))).By(Tactic.Intro("y"), Tactic.Intro("h"), Tactic.Omega());

            [Verified]
            public static int One() => 1;
            """);
        var result = Run(source);
        var unbounded = Assert.IsType<NotProvedOutcome>(result.Find("M:S.Unbounded(System.Int32)"));
        Assert.All(unbounded.Vcs, v => Assert.Equal(VcKind.WellDefinedness, v.Kind));
        Assert.StartsWith(VcKinds.Text(VcKind.WellDefinedness), unbounded.Message, StringComparison.Ordinal);
        Assert.Equal("a + 1", Text(source, "M:S.Unbounded(System.Int32)", unbounded.TacticNode));
        Assert.IsType<ProvedOutcome>(result.Find("M:S.Bounded(System.Int32)"));
        var bounded = (ProvedOutcome)result.Find("M:S.Bounded(System.Int32)")!;
        Assert.Single(bounded.WellDefinedness);
        Assert.Equal(2, bounded.Declarations.Length);
        Assert.IsType<ProvedOutcome>(result.Find("M:S.Wraps"));
        var overflows = Assert.IsType<NotProvedOutcome>(result.Find("M:S.Overflows"));
        Assert.Equal("int.MaxValue + One()", Text(source, "M:S.Overflows", overflows.TacticNode));
        Assert.IsType<ProvedOutcome>(result.Find("M:S.Quantified"));
    }

    [Fact]
    public void ArithmeticInASpecAssertThatCanOverflowFailsAtTheOperationAndProvesWhenKnownBounded()
    {
        // #235: a Spec.Assert's condition is a Spec expression; what is known where it stands (the Spec.Requires, the
        // branch taken, an earlier Spec.Assert, a local's value) bounds it.
        var source = Wrap("""
            [Verified]
            public static int Unbounded(int a, int b)
            {
                Spec.Assert(a + b == b + a);
                return a;
            }

            [Verified]
            public static int ByRequires(int a, int b)
            {
                Spec.Requires(a < 1000 && a > -1000 && b < 1000 && b > -1000);
                Spec.Assert(a + b == b + a);
                return a;
            }

            [Verified]
            public static int ByBranch(int a)
            {
                if (a < 1000 && a > -1000)
                {
                    Spec.Assert(a + 1 > a);
                }
                return a;
            }

            [Verified]
            public static int ByAssertAndLocal(int a)
            {
                var b = Cap(a);
                Spec.Assert(b >= 0 && b <= 100);
                Spec.Assert(b * 2 == b + b);
                return a;
            }

            [Verified]
            public static int Cap(int x)
            {
                Spec.Ensures<int>(r => r >= 0 && r <= 100);
                return x < 0 ? 0 : x > 100 ? 100 : x;
            }

            [Verified]
            public static int Wraps(int a)
            {
                Spec.Assert(unchecked(a + 0) == a);
                return a;
            }

            [Verified]
            public static int ByImplicitLocal(int a, int b)
            {
                Spec.Requires(a < 1000 && a > -1000 && b < 1000 && b > -1000);
                var sum = a + b;
                Spec.Assert(sum - b == a);
                return sum;
            }

            [Verified]
            public static int ByImplicitNegation(int a)
            {
                Spec.Requires(a < 1000 && a > -1000);
                var neg = -a;
                Spec.Assert(neg + a == 0);
                return neg;
            }
            """);
        var result = Run(source);
        const string unbounded = "M:S.Unbounded(System.Int32,System.Int32)";
        Assert.Equal((VcKind.WellDefinedness, "a + b"), Failure(source, unbounded, result.Find(unbounded)));
        // #246: a local bound by implicit arithmetic (#244) carries its value and exact value into the obligation.
        Proved(result.Find("M:S.ByImplicitLocal(System.Int32,System.Int32)"));
        Proved(result.Find("M:S.ByImplicitNegation(System.Int32)"));
        Proved(result.Find("M:S.ByRequires(System.Int32,System.Int32)"));
        Proved(result.Find("M:S.ByBranch(System.Int32)"));
        Proved(result.Find("M:S.ByAssertAndLocal(System.Int32)"));
        Proved(result.Find("M:S.Wraps(System.Int32)"));
    }

    [Fact]
    public void ArithmeticInAPureBodyThatCanOverflowFailsAtTheOperationAndProvesWhenBounded()
    {
        // #244: a verified method's own default-context arithmetic must not overflow either. What is known at the
        // operation bounds it: the Spec.Requires, the branch or arm taken, a guard inside the expression, a local's value
        // and a pure callee's Spec.Ensures. Explicit unchecked wraps with no obligation. A method without a contract gets
        // its obligations too, and its callers are skipped when one fails.
        var source = Wrap("""
            [Verified]
            public static int Unbounded(int a, int b) => a + b;

            [Verified]
            public static int CallsUnbounded(int a) => Unbounded(a, 1) / 2;

            [Verified]
            public static int ByRequires(int a, int b)
            {
                Spec.Requires(a < 1000 && a > -1000 && b < 1000 && b > -1000);
                return a * 3 - b;
            }

            [Verified]
            public static int ByGuard(int a) => a < 1000 ? a + 1 : 0;

            [Verified]
            public static long ByIf(long a)
            {
                if (a > 0)
                {
                    return -a;
                }
                return 0;
            }

            [Verified]
            public static int BySwitch(int a)
            {
                switch (a)
                {
                    case < 100 and > -100:
                        return a * 3;
                    default:
                        return 0;
                }
            }

            [Verified]
            public static int ByArm(int a) => a switch { 5 => a + 1, _ => 0 };

            [Verified]
            public static int ByCallee(int a)
            {
                var b = Cap(a);
                return b * 2;
            }

            [Verified]
            public static int Cap(int x)
            {
                Spec.Ensures<int>(r => r >= 0 && r <= 100);
                return x < 0 ? 0 : x > 100 ? 100 : x;
            }

            [Verified]
            public static int Steps(int a)
            {
                Spec.Requires(a < 100 && a > -100);
                var x = a;
                x += 5;
                x++;
                x--;
                x *= 2;
                return -x;
            }

            [Verified]
            public static int Wraps(int a) => unchecked(a * 31 + 7);

            [Verified]
            public static int StepUnbounded(int a)
            {
                var x = a;
                x++;
                return x;
            }
            """);
        var result = Run(source);
        const string unbounded = "M:S.Unbounded(System.Int32,System.Int32)";
        Assert.Equal((VcKind.ArithmeticOverflow, "a + b"), Failure(source, unbounded, result.Find(unbounded)));
        Assert.StartsWith("arithmetic overflow", VcKinds.Text(VcKind.ArithmeticOverflow), StringComparison.Ordinal);
        var caller = Assert.IsType<SkippedOutcome>(result.Find("M:S.CallsUnbounded(System.Int32)"));
        Assert.EndsWith("whose contract is not proved.", caller.Reason, StringComparison.Ordinal);
        Proved(result.Find("M:S.ByRequires(System.Int32,System.Int32)"));
        Proved(result.Find("M:S.ByGuard(System.Int32)"));
        Proved(result.Find("M:S.ByIf(System.Int64)"));
        Proved(result.Find("M:S.BySwitch(System.Int32)"));
        Proved(result.Find("M:S.ByArm(System.Int32)"));
        Proved(result.Find("M:S.ByCallee(System.Int32)"));
        Proved(result.Find("M:S.Steps(System.Int32)"));
        Assert.IsType<TranslatedOutcome>(result.Find("M:S.Wraps(System.Int32)"));
        const string step = "M:S.StepUnbounded(System.Int32)";
        Assert.Equal((VcKind.ArithmeticOverflow, "x++;"), Failure(source, step, result.Find(step)));
    }

    [Fact]
    public void ARecursiveMethodsArithmeticHasObligationsAndItsRecursiveResultIsUnknown()
    {
        // #244: a recursive method still translates; its arithmetic is bounded by the path to it, but nothing is known of
        // a recursive call's result, so arithmetic on one fails unless it is written unchecked.
        var source = Wrap("""
            [Verified]
            public static int Count(int n)
            {
                Spec.Decreases(n);
                if (n <= 0) return 0;
                return Count(n - 1);
            }

            [Verified]
            public static int Sum(int n)
            {
                Spec.Decreases(n);
                if (n <= 0) return 0;
                return n + Sum(n - 1);
            }

            [Verified]
            public static int SumWrapping(int n)
            {
                Spec.Decreases(n);
                if (n <= 0) return 0;
                return unchecked(n + SumWrapping(n - 1));
            }
            """);
        var result = Run(source);
        Proved(result.Find("M:S.Count(System.Int32)"));
        const string sum = "M:S.Sum(System.Int32)";
        Assert.Equal((VcKind.ArithmeticOverflow, "n + Sum(n - 1)"), Failure(source, sum, result.Find(sum)));
        Proved(result.Find("M:S.SumWrapping(System.Int32)"));
    }

    [Fact]
    public void ArithmeticInABodyThatCanRaiseIsCheckedByTheWalkWithEverythingItKnows()
    {
        // #244: in a method that can raise, an implicit operation is a site of the program, so the VC walk proves it does
        // not overflow with all it knows there, a callee's Spec.Ensures among it. checked still raises OverflowException.
        var source = Wrap("""
            [Verified]
            public static int Unbounded(int a, int b)
            {
                if (b == 0) throw new System.ArgumentException();
                return a + b;
            }

            [Verified]
            public static int ByCallee(int a)
            {
                Spec.Requires(a >= 0);
                var n = Bound(a);
                return n + 1;
            }

            [Verified]
            public static int Bound(int x)
            {
                Spec.Requires(x >= 0);
                Spec.Ensures<int>(r => r >= 0 && r <= 100);
                return x > 100 ? 100 : x;
            }

            [Verified]
            public static int ByRaisingCallee(int a) => Raises(a) * 3;

            [Verified]
            public static int Raises(int x)
            {
                Spec.Ensures<int>(r => r >= 0 && r <= 100);
                if (x < 0) throw new System.ArgumentException();
                return x > 100 ? 100 : x;
            }

            [Verified]
            public static int Wraps(int a)
            {
                if (a == 0) throw new System.ArgumentException();
                return unchecked(a + 1);
            }

            [Verified]
            public static int Checked(int a)
            {
                if (a == 0) throw new System.ArgumentException();
                return checked(a + 1);
            }
            """);
        var result = Run(source);
        const string unbounded = "M:S.Unbounded(System.Int32,System.Int32)";
        Assert.Equal((VcKind.ArithmeticOverflow, "a + b"), Failure(source, unbounded, result.Find(unbounded)));
        Proved(result.Find("M:S.ByCallee(System.Int32)"));
        Proved(result.Find("M:S.ByRaisingCallee(System.Int32)"));
        Proved(result.Find("M:S.Wraps(System.Int32)"));
        const string isChecked = "M:S.Checked(System.Int32)";
        Assert.Equal((VcKind.Overflow, "a + 1"), Failure(source, isChecked, result.Find(isChecked)));
    }

    [Fact]
    public void AnUnsatisfiableRequiresIsReportedAtItsLine()
    {
        var source = Wrap("""
            [Verified]
            public static int Never(int x)
            {
                Spec.Requires(x > 0 && x < 0);
                return x;
            }
            """);
        var outcome = Assert.IsType<NotProvedOutcome>(Run(source).Find("M:S.Never(System.Int32)"));
        Assert.StartsWith("The contract is unsatisfiable", outcome.Message, StringComparison.Ordinal);
        Assert.Equal("Spec.Requires(x > 0 && x < 0);", Text(source, "M:S.Never(System.Int32)", outcome.TacticNode));
    }

    [Fact]
    public void AFailingAssertFailsAtItsLineAndTheDivisionAfterItUsesTheAssertedFact()
    {
        var source = Wrap("""
            [Verified]
            public static int Ratio(int a, int b)
            {
                Spec.Assert(b != 0);
                return a / b;
            }
            """);
        var outcome = Assert.IsType<NotProvedOutcome>(Run(source).Find(Ratio));
        // The division's zero divisor follows from the asserted fact, so it is not a second failure; its MinValue / -1 is.
        Assert.Equal(VcKind.Assert, outcome.Vcs[0].Kind);
        Assert.Equal("Spec.Assert(b != 0);", Text(source, Ratio, outcome.Vcs[0].Node));
        Assert.DoesNotContain(outcome.Vcs, v => v.Kind == VcKind.DivisionByZero);
    }

    [Fact]
    public void ACallerThatPassesZeroToARequiresFailsAtTheCall()
    {
        var source = Wrap("""
            [Verified]
            public static int Positive(int x)
            {
                Spec.Requires(x > 0);
                return x;
            }

            [Verified]
            public static int Caller() => Positive(0);

            [Verified]
            public static int Fine(int y)
            {
                Spec.Requires(y > 3);
                return Positive(y);
            }
            """);
        var result = Run(source);
        Proved(result.Find("M:S.Positive(System.Int32)"));
        Assert.Equal((VcKind.CalleePrecondition, "Positive(0)"), Failure(source, "M:S.Caller", result.Find("M:S.Caller")));
        var fine = result.Find("M:S.Fine(System.Int32)");
        Proved(fine);
        Assert.Contains(fine!.Assumptions, a => a.Assumption.Kind == VirAssumptionKind.CalleeContract && a.Assumption.Subject == "M:S.Positive(System.Int32)" && a.UnitKey == "M:S.Fine(System.Int32)");
    }

    [Fact]
    public void AnAwaitedCallIsCheckedAgainstTheCalleesRequiresWhetherOrNotTheCalleeRaises()
    {
        // #228: an awaited call to a verified method is a call site like any other. Step cannot raise; Share can (100 / x).
        var source = "using System.Threading.Tasks;\n" + Wrap("""
            [Verified]
            public static async Task<int> Step(int x)
            {
                Spec.Requires(x < 100);
                return x + 1;
            }

            [Verified]
            public static async Task<int> Share(int x)
            {
                Spec.Requires(x > 0);
                return 100 / x;
            }

            [Verified]
            public static async Task<int> StepTooFar(int x)
            {
                Spec.Requires(x < 200);
                return await Step(x);
            }

            [Verified]
            public static async Task<int> ShareOfAny(int x)
            {
                return await Share(x);
            }

            [Verified]
            public static async Task<int> Both(int x)
            {
                Spec.Requires(x > 0 && x < 100);
                var a = await Step(x);
                return await Share(x);
            }
            """);
        var result = Run(source);
        Proved(result.Find("M:S.Step(System.Int32)"));
        Proved(result.Find("M:S.Share(System.Int32)"));
        Assert.Equal((VcKind.CalleePrecondition, "Step(x)"), Failure(source, "M:S.StepTooFar(System.Int32)", result.Find("M:S.StepTooFar(System.Int32)")));
        // The raising callee goes through the walker's call rule, not an unsupported shape.
        Assert.Equal((VcKind.CalleePrecondition, "Share(x)"), Failure(source, "M:S.ShareOfAny(System.Int32)", result.Find("M:S.ShareOfAny(System.Int32)")));
        var both = result.Find("M:S.Both(System.Int32)");
        Proved(both);
        Assert.Equal(
            ["M:S.Share(System.Int32)", "M:S.Step(System.Int32)"],
            both!.Assumptions.Where(a => a.Assumption.Kind == VirAssumptionKind.CalleeContract).Select(a => a.Assumption.Subject).Order(StringComparer.Ordinal));
    }

    [Fact]
    public void AMethodWithThreeFailingVcsReportsAllThreeEachWithItsKind()
    {
        var source = Wrap("""
            [Verified]
            public static int Three(int a, int b, int? c)
            {
                Spec.Ensures<int>(r => r > 0);
                var q = checked(a * 2);
                var v = c.Value;
                return unchecked(q + v);
            }
            """);
        // unchecked keeps the sum out of it: default-context arithmetic would be a fourth VC (#244).
        var outcome = Assert.IsType<NotProvedOutcome>(Run(source).Find("M:S.Three(System.Int32,System.Int32,System.Nullable{System.Int32})"));
        Assert.Equal([VcKind.Overflow, VcKind.NullRead, VcKind.Postcondition], outcome.Vcs.Select(v => v.Kind));
        Assert.Equal(
            ["a * 2", "c.Value", "Spec.Ensures<int>(r => r > 0);"],
            outcome.Vcs.Select(v => Text(source, "M:S.Three(System.Int32,System.Int32,System.Nullable{System.Int32})", v.Node)));
        Assert.All(outcome.Vcs, v => Assert.StartsWith(VcKinds.Text(v.Kind) + ": ", v.Message, StringComparison.Ordinal));
    }

    // ---- pure units and pure callees (#173) ----

    [Fact]
    public void APureMethodWithAnEnsuresProvesWithNoScript()
    {
        var source = Wrap("""
            [Verified]
            public static int NonNegative(int x)
            {
                Spec.Ensures<int>(r => r >= 0);
                return x < 0 ? 0 : x;
            }
            """);
        var result = Run(source);
        var outcome = result.Find("M:S.NonNegative(System.Int32)");
        Proved(outcome);
        Assert.Contains(outcome!.Declarations, d => d is Kernel.TheoremDecl t && t.Value.Name.ToString().EndsWith("$contract_spec", StringComparison.Ordinal));
    }

    [Fact]
    public void ARaisingCallerProvesAFactOnlyThroughAPureCalleesEnsures()
    {
        // Floor's body is not unfolded: its Ensures, by its $contract_spec, is all the caller knows of its value. Opaque's
        // body would show the same fact, but without an Ensures nothing brings it into scope, so the twin fails.
        var source = Wrap("""
            [Verified]
            public static int Floor(int x)
            {
                Spec.Ensures<int>(r => r >= 1);
                return x < 1 ? 1 : x;
            }

            [Verified]
            public static int Opaque(int x) => x < 1 ? 1 : x;

            [Verified]
            public static int Divide(int a, int x) => a / Floor(x);

            [Verified]
            public static int DivideOpaque(int a, int x) => a / Opaque(x);
            """);
        var result = Run(source);
        var divide = result.Find("M:S.Divide(System.Int32,System.Int32)");
        Proved(divide);
        // #223: the proof rests on Floor's contract (its $contract_spec), so the report lists it.
        Assert.Contains(divide!.Assumptions, a => a.Assumption == new VirAssumption(VirAssumptionKind.CalleeContract, "M:S.Floor(System.Int32)") && a.UnitKey == "M:S.Divide(System.Int32,System.Int32)");
        var opaque = Assert.IsType<NotProvedOutcome>(result.Find("M:S.DivideOpaque(System.Int32,System.Int32)"));
        Assert.Equal(VcKind.DivisionByZero, opaque.Vcs[0].Kind);
    }

    [Fact]
    public void ACalleeContractUsedOnlyByANoOverflowProofIsListed()
    {
        // #247: G's and the theorem's H(x) + 1 cannot overflow only by H's Spec.Ensures (its $contract_spec), which only
        // the no-overflow and well-definedness proofs use; the report lists H's contract for both.
        var source = Wrap("""
            [Verified]
            public static int H(int x)
            {
                Spec.Ensures<int>(r => r < 100);
                return x < 0 ? 0 : 1;
            }

            [Verified]
            public static int G(int x) => H(x) + 1;

            [Theorem]
            static Proof T(int x) => Prove.That(Spec.Implies(H(x) + 1 > 0, H(x) + 1 > 0)).By(Tactic.Intro("h"), Tactic.Omega());
            """);
        var result = Run(source);
        var g = result.Find("M:S.G(System.Int32)");
        Proved(g);
        Assert.Contains(g!.Assumptions, a => a.Assumption == new VirAssumption(VirAssumptionKind.CalleeContract, "M:S.H(System.Int32)") && a.UnitKey == "M:S.G(System.Int32)");
        var t = Assert.IsType<ProvedOutcome>(result.Find("M:S.T(System.Int32)"));
        Assert.NotEmpty(t.WellDefinedness);
        Assert.Contains(t.Assumptions, a => a.Assumption == new VirAssumption(VirAssumptionKind.CalleeContract, "M:S.H(System.Int32)") && a.UnitKey == "M:S.T(System.Int32)");
    }

    // ---- robustness ----

    [Fact]
    public void AShapeTheWalkerDoesNotKnowIsALeftoverNotAnException()
    {
        // A switch over a closed enum whose discriminant is not a variable is let-bound and substituted, so the walker has
        // no rule for its recursor (it splits one only on a variable): the triple is a leftover VC, reported, not thrown.
        var source = """
            [Closed] public enum Light { Red, Green }

            public static class S
            {
                [Verified]
                public static Light Flip(Light l) => l == Light.Red ? Light.Green : Light.Red;

                [Verified]
                public static int Rank(Light l, int a, int b) => Flip(l) switch { Light.Red => a / b, _ => 0 };
            }
            """;
        var outcome = Assert.IsType<NotProvedOutcome>(Run(source).Find("M:S.Rank(Light,System.Int32,System.Int32)"));
        Assert.Equal(VcKind.Unsupported, outcome.Vcs[0].Kind);
    }

    [Fact]
    public void RunningOutOfBudgetReportsWrt0006()
    {
        var source = Wrap("""
            [Verified]
            public static int Ratio(int a, int b)
            {
                Spec.Requires(b != 0 && b != -1);
                return a / b;
            }
            """);
        var options = engine.Options with { TacticFuel = 50 };
        var outcome = Pipeline.Run(EngineCorpus.Inputs(EngineCorpus.Inline(source)), engine.Bundle, options).Find(Ratio);
        Assert.IsType<UndecidedOutcome>(outcome);
        Assert.Equal("WRT0006", UndecidedOutcome.Code);
    }

    // ---- A bare `return;` (#215, #253) ----

    /// <summary>
    /// A bare <c>return;</c> ends its path wherever it is (#253): on a path that is not the last, in a switch section, in
    /// both branches of an <c>if</c>, and in a <c>ValueTask</c> method. Each assertion after it holds only because the
    /// path that returned does not reach it, so each proves; without the return, the same assertion fails.
    /// </summary>
    [Fact]
    public void ABareReturnEndsItsPathWhereverItIs()
    {
        var source = "using System.Threading.Tasks;\n" + Wrap("""
            [Verified]
            public static void NotLast(int x)
            {
                if (x == int.MaxValue) return;
                Spec.Assert(x < int.MaxValue);
            }

            [Verified]
            public static void InASwitch(int x)
            {
                switch (x)
                {
                    case 0:
                        return;
                    default:
                        Spec.Assert(x != 0);
                        break;
                }
                Spec.Assert(x != 0);
            }

            [Verified]
            public static void BothBranches(int x)
            {
                if (x > 0)
                {
                    Spec.Assert(x > 0);
                    return;
                }
                else
                {
                    Spec.Assert(x <= 0);
                    return;
                }
            }

            [Verified]
            public static async ValueTask Later(int x)
            {
                if (x == int.MaxValue) return;
                Spec.Assert(x < int.MaxValue);
                await Twice(x);
            }

            [Verified]
            public static async Task<int> Twice(int x)
            {
                Spec.Requires(x < int.MaxValue);
                return x;
            }

            [Verified]
            public static void WithoutTheReturn(int x)
            {
                if (x == 0) return;
                Spec.Assert(x < int.MaxValue);
            }
            """);
        var result = Run(source);
        foreach (var key in new[] { "M:S.NotLast(System.Int32)", "M:S.InASwitch(System.Int32)", "M:S.BothBranches(System.Int32)", "M:S.Later(System.Int32)" })
        {
            Proved(result.Find(key));
        }
        const string Without = "M:S.WithoutTheReturn(System.Int32)";
        Assert.Equal((VcKind.Assert, "Spec.Assert(x < int.MaxValue);"), Failure(source, Without, result.Find(Without)));
    }
}
