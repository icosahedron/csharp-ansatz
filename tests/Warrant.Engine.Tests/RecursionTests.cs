using Warrant.Cic;
using Warrant.Kernel;
using Warrant.Semantics;

namespace Warrant.Engine.Tests;

/// <summary>
/// Well-founded recursion through the engine (plan M5a U15, KTD14, KTD15, KTD31; docs/m5a/03): the decrease theorems
/// proved by omega and admitted, the <c>Nat.fix</c> definition, and the equation lemma.
/// </summary>
public sealed class RecursionTests(EngineFixture engine) : IClassFixture<EngineFixture>
{
    private const string Sum = "M:Corpus.Recursion.Sum(System.Int32)";
    private const string Add = "M:Corpus.Recursion.Add(System.Int32,System.Int32)";
    private const string SumLong = "M:Corpus.Recursion.SumLong(System.Int64)";

    [Theory]
    [InlineData(Sum)]
    [InlineData(Add)]
    [InlineData(SumLong)]
    public void TheCorpusRecursionsAreAdmitted(string key)
    {
        var outcome = engine.Run("m5a/accepted").Find(key);
        var translated = Assert.IsType<TranslatedOutcome>(outcome);
        var names = translated.Declarations.Select(NameOf).ToList();
        var name = LeanNames.ForKey(key).ToString();
        Assert.Equal([$"{name}.$dec_1", name, $"{name}.$eq_def"], names);
    }

    [Fact]
    public void SumDependsOnLeansThreeStandardAxioms()
    {
        // docs/m5a/03 "Axioms": the decrease proof brings propext, Classical.choice (Init's Int32 lemmas) and Quot.sound,
        // the definition inherits them, and the equation lemma adds Quot.sound from Nat.fix_eq.
        var result = engine.Run("m5a/accepted");
        var translated = Assert.IsType<TranslatedOutcome>(result.Find(Sum));
        string[] standard = ["Classical.choice", "Quot.sound", "propext"];
        foreach (var declaration in translated.Declarations)
        {
            var root = declaration switch
            {
                DefinitionDecl d => d.Value.Value,
                TheoremDecl t => t.Value.Proof,
                _ => throw new InvalidOperationException(declaration.GetType().Name),
            };
            Assert.Equal(standard, TheoremTests.Axioms(result.Environment, root));
        }
    }

    [Fact]
    public void ARecursiveDefinitionIsIrreducibleForMeta()
    {
        // The sidecar marks Sum irreducible, as Lean marks its well-founded definitions: simp's decide does not evaluate
        // Sum 3 through Nat.fix, though the kernel can (the differential tests); Unfold rewrites with Sum.$eq_def instead.
        var outcome = Assert.IsType<NotProvedOutcome>(Script("""
            public static class S
            {
                [Verified]
                public static int Sum(int n)
                {
                    Spec.Decreases(n);
                    if (n <= 0) return 0;
                    return n + Sum(n - 1);
                }

                [Theorem] static Proof SumOfThree() => Prove.That(Sum(3) == 6).By(Tactic.Simp());
            }
            """).Find("M:S.SumOfThree"));
        Assert.Equal("`simp` made no progress", outcome.Message);
    }

    [Fact]
    public void ACallWithNoGuardReportsItsDecreaseGoal()
    {
        var outcome = Assert.IsType<NotProvedOutcome>(engine.Run("m5a/refuted").Find("M:Corpus.Refuted.Recursion.Bad(System.Int32)"));
        Assert.Equal("WRT0001", NotProvedOutcome.Code);
        Assert.Equal("n : Int32\n⊢ (n - 1).toInt.toNat < n.toInt.toNat", outcome.Goals);
        Assert.StartsWith("omega could not prove the goal:", outcome.Message, StringComparison.Ordinal);
        Assert.Equal(1, outcome.Decrease?.Index);
    }

    [Fact]
    public void ALetHoldingARecursiveResultIsAPlainBinderOfTheNextObligation()
    {
        var result = Script("""
            public static class S
            {
                [Verified]
                public static int Fib(int n)
                {
                    Spec.Decreases(n);
                    if (n <= 1) return n;
                    var a = Fib(n - 1);
                    return a + Fib(n - 2);
                }
            }
            """);
        var translated = Assert.IsType<TranslatedOutcome>(result.Find("M:S.Fib(System.Int32)"));
        var dec2 = translated.Declarations.OfType<TheoremDecl>().Single(t => t.Value.Name.ToString() == "Cs.S.«Fib(System.Int32)».$dec_2");
        // ∀ (n : Int32) (h : ¬n ≤ 1) (a : Int32), μ (n - 2) < μ n: `a` is bound without its value, Fib (n - 1).
        var n = Assert.IsType<ForallExpr>(dec2.Value.Type);
        var h = Assert.IsType<ForallExpr>(n.Body);
        var a = Assert.IsType<ForallExpr>(h.Body);
        Assert.Equal(["n", "h", "a"], [n.BinderName.ToString(), h.BinderName.ToString(), a.BinderName.ToString()]);
        Assert.Equal("Not", Assert.IsType<ConstExpr>(h.BinderType.GetAppFn()).Name.ToString());
        Assert.Equal("LT.lt", Assert.IsType<ConstExpr>(a.Body.GetAppFn()).Name.ToString());
    }

    [Fact]
    public void UnfoldRewritesWithTheEquationLemma()
    {
        var result = Script("""
            public static class S
            {
                [Verified]
                public static int Sum(int n)
                {
                    Spec.Decreases(n);
                    if (n <= 0) return 0;
                    return n + Sum(n - 1);
                }

                [Theorem] static Proof Unfolded(int n) => Prove.That(Sum(n) == n).By(Tactic.Unfold(nameof(Sum)));

                [Theorem] static Proof SumOfZero() => Prove.That(Sum(0) == 0).By(Tactic.Unfold(nameof(Sum)), Tactic.Simp());
            }
            """);
        // One rewrite with Sum.$eq_def at each occurrence, not again inside the result.
        var outcome = Assert.IsType<NotProvedOutcome>(result.Find("M:S.Unfolded(System.Int32)"));
        Assert.Equal("unsolved goals", outcome.Message);
        Assert.Equal("n : Int32\n⊢ (if n ≤ 0 then 0 else n + Sum (n - 1)) = n", outcome.Goals);

        var proved = Assert.IsType<ProvedOutcome>(result.Find("M:S.SumOfZero"));
        Assert.Contains("Cs.S.«Sum(System.Int32)».$eq_def", proved.Certificate.Value.Proof.ToString(), StringComparison.Ordinal);
    }

    [Fact]
    public void ACallRightOfAndHasNoGuardAndItsGoalIsReported()
    {
        // docs/m5a/03: a call right of && gets only the hypotheses in scope there, not the left side's truth; the
        // obligation is reported with its goal, and the fix is to put the call under an if.
        var result = Script("""
            public static class S
            {
                [Verified]
                public static bool AllPositive(int n)
                {
                    Spec.Decreases(n);
                    return n > 0 && AllPositive(n - 1);
                }

                [Verified]
                public static bool Guarded(int n)
                {
                    Spec.Decreases(n);
                    if (n <= 0) return true;
                    return n > 0 && Guarded(n - 1);
                }
            }
            """);
        var outcome = Assert.IsType<NotProvedOutcome>(result.Find("M:S.AllPositive(System.Int32)"));
        Assert.Equal("n : Int32\n⊢ (n - 1).toInt.toNat < n.toInt.toNat", outcome.Goals);
        Assert.IsType<TranslatedOutcome>(result.Find("M:S.Guarded(System.Int32)"));
    }

    [Fact]
    public void ACallInABranchWhoseResultIsUnusedStillHasItsDecreaseChecked()
    {
        // Code review P0: an if that returns nothing and changes no local the rest reads was skipped whole (Branches
        // rule 4), so F(n) below had no decrease obligation and F was admitted as `0`, although the C# never terminates.
        var result = Script("""
            public static class S
            {
                [Verified]
                public static int F(int n)
                {
                    Spec.Decreases(n);
                    int x = 0;
                    if (n > 0) { x = F(n); }
                    return 0;
                }

                [Theorem] static Proof FOfFive() => Prove.That(F(5) == 0).By(Tactic.Unfold(nameof(F)), Tactic.Simp());
            }
            """);
        var outcome = Assert.IsType<NotProvedOutcome>(result.Find("M:S.F(System.Int32)"));
        Assert.Equal(1, outcome.Decrease?.Index);
        Assert.IsNotType<ProvedOutcome>(result.Find("M:S.FOfFive"));
    }

    [Fact]
    public void ARecursiveMethodWithoutParametersFailsTranslation()
    {
        var result = Script("""
            public static class S
            {
                [Verified]
                public static int G()
                {
                    Spec.Decreases(0);
                    return 1;
                }

                [Verified]
                public static int H(int n) => n;
            }
            """);
        var failed = Assert.IsType<FailedOutcome>(result.Find("M:S.G"));
        Assert.Contains("needs a parameter", failed.Reason, StringComparison.Ordinal);
        Assert.IsType<TranslatedOutcome>(result.Find("M:S.H(System.Int32)"));
    }

    [Fact]
    public void TheDecreaseFailureNamesTheCallAndTheMeasure()
    {
        var outcome = Assert.IsType<NotProvedOutcome>(engine.Run("m5a/refuted").Find("M:Corpus.Refuted.Recursion.Bad(System.Int32)"));
        var spans = engine.Spans("m5a/refuted", "M:Corpus.Refuted.Recursion.Bad(System.Int32)");
        Assert.Equal(
            "The recursive call 'Bad(n - 1)' could not be shown to decrease 'n': omega could not prove the goal.",
            Reports.OutcomeText.NotProvedMessage("Bad", outcome, spans, SourceText));
        Assert.Equal("Bad(n - 1)", SourceText(Reports.OutcomeText.SpanOf(spans, outcome.TacticNode)!));
        Assert.Equal(outcome.TacticNode, outcome.Decrease!.CallNode);
        Assert.Equal("n", SourceText(Reports.OutcomeText.SpanOf(spans, outcome.Decrease.MeasureNode)!));
        Assert.StartsWith("recursive call 1 was not shown to decrease (WRT0001): ", Reports.OutcomeText.NotProvedDetail(outcome), StringComparison.Ordinal);
    }

    [Fact]
    public void TheAssumptionReportListsTheStackForRecursiveUnitsAndTheoremsAboutThem()
    {
        // KTD31: the model has no stack, so every recursive unit, and a theorem that depends on one, assumes each call returns.
        var extraction = EngineCorpus.Inline("""
            public static class S
            {
                [Verified]
                public static int Sum(int n)
                {
                    Spec.Decreases(n);
                    if (n <= 0) return 0;
                    return n + Sum(n - 1);
                }

                [Verified] public static int Twice(int x) => x + x;

                [Theorem] static Proof SumOfZero() => Prove.That(Sum(0) == 0).By(Tactic.Unfold(nameof(Sum)), Tactic.Simp());
            }
            """);
        var inputs = EngineCorpus.Inputs(extraction);
        var report = Reports.AssumptionReports.Build(
            Pipeline.Run(inputs, engine.Bundle, engine.Options), inputs, new Reports.ReportSettings(CheckOverflow: false, Bundle: "warrant-semantics test"));
        Assert.Equal([Reports.AssumptionReports.Stack], report.Find("M:S.Sum(System.Int32)")!.Global.AsEnumerable());
        Assert.Equal([Reports.AssumptionReports.Stack], report.Find("M:S.SumOfZero")!.Global.AsEnumerable());
        Assert.Empty(report.Find("M:S.Twice(System.Int32)")!.Global);

        var markdown = Reports.MarkdownReport.Render(report);
        Assert.Contains(
            "  Assumed (global):\n    - Each recursive call returns without exhausting the stack\n    - Arithmetic wraps on overflow",
            markdown,
            StringComparison.Ordinal);
        var read = Reports.JsonReport.Read(Reports.JsonReport.Render(report));
        Assert.Equal([Reports.AssumptionReports.Stack], read.Find("M:S.Sum(System.Int32)")!.Global.AsEnumerable());
        Assert.Empty(read.Find("M:S.Twice(System.Int32)")!.Global);
    }

    private static string? SourceText(Vir.VirSpan span)
    {
        var lines = File.ReadAllLines(Path.Combine(CorpusSet.M5a.Root, span.Path));
        return span.StartLine == span.EndLine ? lines[span.StartLine - 1][(span.StartColumn - 1)..(span.EndColumn - 1)] : null;
    }

    private EngineResult Script(string source) =>
        Pipeline.Run(EngineCorpus.Inputs(EngineCorpus.Inline(source)), engine.Bundle, engine.Options);

    private static string NameOf(KernelDeclaration declaration) => declaration switch
    {
        DefinitionDecl d => d.Value.Name.ToString(),
        TheoremDecl t => t.Value.Name.ToString(),
        _ => throw new InvalidOperationException(declaration.GetType().Name),
    };
}
