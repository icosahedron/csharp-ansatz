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
                return q + v;
            }
            """);
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
}
