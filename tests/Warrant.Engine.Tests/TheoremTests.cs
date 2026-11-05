using System.Globalization;
using System.Reflection;
using Warrant.Cic;
using Warrant.Kernel;
using Warrant.Semantics;
using Warrant.Vir;

namespace Warrant.Engine.Tests;

/// <summary>The engine over the M4 corpus and inline sources (docs/m4/06, 07; plan U8, KTD12, KTD22).</summary>
public sealed class TheoremTests(EngineFixture engine) : IClassFixture<EngineFixture>
{
    // ---- Proofs ----

    [Fact]
    public void CappedAtTheLimitIsProvedByRfl()
    {
        var outcome = Assert.IsType<ProvedOutcome>(engine.Run("accepted").Find("M:Payouts.PayoutTheorems.CappedAtTheLimit"));
        Assert.Equal(ProofKind.Rfl, outcome.By);
        Assert.Equal("Cs.Payouts.PayoutTheorems.CappedAtTheLimit", outcome.Certificate.Value.Name.ToString());
    }

    [Theory]
    [InlineData("M:Corpus.Increments.IncrementIsLarger", "LT.lt")] // Increment(41) > 41
    [InlineData("M:Pricing.Discounts.NeverNegativeHere", "LE.le")] // Discounted(100, 150) >= 0
    public void OrderClaimIsProvedByDecide(string key, string relation)
    {
        var outcome = Assert.IsType<ProvedOutcome>(engine.Run("accepted").Find(key));
        Assert.Equal(ProofKind.Decide, outcome.By);
        Assert.Equal(relation, Assert.IsType<ConstExpr>(outcome.Certificate.Value.Type.GetAppFn()).Name.ToString());
    }

    [Fact]
    public void RecordEqualityIsProvedThroughEqTrue()
    {
        var outcome = Assert.IsType<ProvedOutcome>(engine.Run("accepted").Find("M:Claims.Records.MoveChangesX"));
        Assert.Equal(ProofKind.Rfl, outcome.By);
        var type = outcome.Certificate.Value.Type;
        Assert.Equal("Eq", Assert.IsType<ConstExpr>(type.GetAppFn()).Name.ToString());
        var args = type.GetAppArgs();
        Assert.Equal("Bool", Assert.IsType<ConstExpr>(args[0]).Name.ToString());
        Assert.Equal("Cs.Claims.Point.$eq", Assert.IsType<ConstExpr>(args[1].GetAppFn()).Name.ToString());
        Assert.Equal("Bool.true", Assert.IsType<ConstExpr>(args[2]).Name.ToString());
    }

    [Fact]
    public void ImplicationWithAFalsePremiseIsProved()
    {
        var result = Run("""
            public static class S
            {
                [Verified] public static int Inc(int x) => x + 1;
                [Theorem] static Proof Vacuous() => Prove.That(Spec.Implies(Inc(1) > 5, Inc(1) > 100));
            }
            """);
        var outcome = Assert.IsType<ProvedOutcome>(result.Find("M:S.Vacuous"));
        Assert.Equal(ProofKind.Decide, outcome.By);
        Assert.IsType<ForallExpr>(outcome.Certificate.Value.Type);
    }

    // ---- False and undecided ----

    [Fact]
    public void NeverWrapsIsFalseWithTheValuesOfBothSides()
    {
        var outcome = Assert.IsType<FalseOutcome>(engine.Run("refuted").Find("M:Corpus.Refuted.Increments.NeverWraps"));
        Assert.Equal("WRT0001", FalseOutcome.Code);
        Assert.Equal(2, outcome.Sides.Length);
        Assert.Equal(new Int32Value(-2147483648), outcome.Sides[0].Value);
        Assert.Equal(new Int32Value(2147483647), outcome.Sides[1].Value);
        Assert.Equal("-2147483648", outcome.Sides[0].Value.ToString());
        Assert.Equal("Increment(int.MaxValue)", SourceText(outcome.Sides[0].Span));
        Assert.Equal("int.MaxValue", SourceText(outcome.Sides[1].Span));
    }

    [Fact]
    public void WrongSumIsFalseWithTheValuesOfBothSides()
    {
        var outcome = Assert.IsType<FalseOutcome>(engine.Run("refuted").Find("M:Corpus.Refuted.Increments.WrongSum"));
        Assert.Equal([new Int32Value(3), new Int32Value(4)], outcome.Sides.Select(s => s.Value));
    }

    [Fact]
    public void ReadBackGivesSignedValuesAndBooleans()
    {
        var env = engine.Bundle.Env;
        Assert.Equal(new Int32Value(int.MinValue), ReadBack.Value(env, Literals.Int32(int.MinValue), Literals.Type(VirPrimitive.Int32)));
        Assert.Equal(new Int32Value(-1), ReadBack.Value(env, Literals.Int32(-1), Literals.Type(VirPrimitive.Int32)));
        Assert.Equal(new Int64Value(long.MinValue), ReadBack.Value(env, Literals.Int64(long.MinValue), Literals.Type(VirPrimitive.Int64)));
        Assert.Equal(new Int64Value(long.MaxValue), ReadBack.Value(env, Literals.Int64(long.MaxValue), Literals.Type(VirPrimitive.Int64)));
        Assert.Equal(new BoolValue(false), ReadBack.Value(env, Operators.Not(Literals.Bool(true)), Literals.Type(VirPrimitive.Bool)));
        Assert.IsType<UnknownValue>(ReadBack.Value(env, Expr.Const(Name.Parse("Nat.zero")), Expr.Const(Name.Parse("Nat"))));
    }

    [Fact]
    public void TinyFuelLeavesATrueClaimUndecidedNeverProved()
    {
        var extraction = EngineCorpus.Inline("""
            public static class S
            {
                [Verified] public static int Inc(int x) => x + 1;
                [Theorem] static Proof Larger() => Prove.That(Inc(41) > 41);
            }
            """);
        var inputs = EngineCorpus.Inputs(extraction);
        Assert.IsType<ProvedOutcome>(Pipeline.Run(inputs, engine.Bundle, KernelLimits.Corpus).Find("M:S.Larger"));

        // The smallest power of two that admits Inc: enough to check a definition, far too little to compute Inc(41).
        EngineResult result;
        long fuel = 1;
        while ((result = Pipeline.Run(inputs, engine.Bundle, new KernelLimits(fuel, KernelLimits.Corpus.MaxNatBytes)))
            .Find("M:S.Inc(System.Int32)") is not TranslatedOutcome)
        {
            fuel *= 2;
            Assert.True(fuel < KernelLimits.Corpus.Fuel);
        }
        var outcome = Assert.IsType<UndecidedOutcome>(result.Find("M:S.Larger"));
        Assert.Contains("ran out", outcome.Reason, StringComparison.Ordinal);
        Assert.Equal("WRT0006", UndecidedOutcome.Code);
        Assert.Null(result.Environment.Find(Name.Parse("Cs.S.Larger")));
        Assert.DoesNotContain(result.Admitted, d => d is TheoremDecl);
    }

    // ---- Independence ----

    [Fact]
    public void AFalseTheoremDoesNotStopTheOtherUnits()
    {
        var result = Run("""
            public static class S
            {
                [Verified] public static int Inc(int x) => x + 1;
                [Theorem] static Proof A() => Prove.That(Inc(1) == 3);
                [Theorem] static Proof B() => Prove.That(Inc(1) == 2);
                [Verified] public static int Twice(int x) => Inc(Inc(x));
                [Theorem] static Proof C() => Prove.That(Twice(1) == 3);
            }
            """);
        Assert.IsType<FalseOutcome>(result.Find("M:S.A"));
        Assert.IsType<ProvedOutcome>(result.Find("M:S.B"));
        Assert.IsType<TranslatedOutcome>(result.Find("M:S.Twice(System.Int32)"));
        Assert.IsType<ProvedOutcome>(result.Find("M:S.C"));
    }

    [Fact]
    public void UnitsDependingOnAFailedUnitAreSkippedAndOthersProceed()
    {
        var extraction = EngineCorpus.Inline("""
            public static class S
            {
                [Verified] public static int Inc(int x) => x + 1;
                [Verified] public static int Twice(int x) => Inc(Inc(x));
                [Verified] public static int Id(int x) => x;
                [Theorem] static Proof UsesTwice() => Prove.That(Twice(1) == 3);
                [Theorem] static Proof UsesId() => Prove.That(Id(1) == 1);
            }
            """);
        // Leave Inc out: Twice cannot be translated, and the theorem about it is skipped.
        var inputs = EngineCorpus.Inputs(extraction).Where(u => u.Unit.Key != "M:S.Inc(System.Int32)").ToList();
        var result = Pipeline.Run(inputs, engine.Bundle);
        Assert.IsType<FailedOutcome>(result.Find("M:S.Twice(System.Int32)"));
        var skipped = Assert.IsType<SkippedOutcome>(result.Find("M:S.UsesTwice"));
        Assert.Equal("M:S.Twice(System.Int32)", skipped.Dependency);
        Assert.IsType<TranslatedOutcome>(result.Find("M:S.Id(System.Int32)"));
        Assert.IsType<ProvedOutcome>(result.Find("M:S.UsesId"));
        Assert.Equal(inputs.Select(u => u.Unit.Key), result.Units.Select(u => u.Key));
    }

    // ---- The corpus ----

    [Fact]
    public void EveryTheoremInExpectedJsonGetsItsOutcomeAndProof()
    {
        int theorems = 0;
        foreach (var compilation in EngineCorpus.Compilations)
        {
            var result = engine.Run(compilation);
            foreach (var member in EngineCorpus.Expected.GetProperty("members").GetProperty(compilation).EnumerateObject())
            {
                var expected = member.Value.GetProperty("outcome").GetString();
                var actual = result.Find(member.Name);
                switch (expected)
                {
                    case "proved":
                        var proved = Assert.IsType<ProvedOutcome>(actual);
                        var by = member.Value.GetProperty("by").GetString();
                        Assert.True(by == Reports.AssumptionReports.ProofName(proved.By), $"{member.Name}: expected {by}, got {proved.By}");
                        theorems++;
                        break;
                    case "false":
                        Assert.IsType<FalseOutcome>(actual);
                        theorems++;
                        break;
                    case "translated":
                        Assert.True(actual is TranslatedOutcome, $"{member.Name}: {actual}");
                        break;
                    case "rejected":
                        Assert.Null(actual);
                        break;
                }
            }
            // Every theorem the engine ran is in expected.json, and no unit failed. (Helper types such as open enums used
            // only by rejected members translate without an entry.)
            foreach (var outcome in result.Units)
            {
                Assert.True(
                    outcome.UnitKind != VirUnitKind.Theorem
                        || EngineCorpus.Expected.GetProperty("members").GetProperty(compilation).TryGetProperty(outcome.Key, out _),
                    $"{outcome.Key} is not in expected.json");
                Assert.False(outcome is FailedOutcome or SkippedOutcome or UndecidedOutcome, $"{outcome.Key}: {outcome}");
            }
        }
        Assert.Equal(36, theorems); // 33 accepted, 2 refuted, and Specs.Valid among the rejected
    }

    [Fact]
    public void ATheoremInheritsTheAssumptionsOfTheUnitsItCalls()
    {
        var result = engine.Run("accepted");
        var validate = result.Find("M:Claims.Payments.Validate(Claims.Payment)")!;
        Assert.Contains(validate.Assumptions, a => a.UnitKey == validate.Key && a.Assumption == new VirAssumption(VirAssumptionKind.NonNull, "p"));
        var theorem = result.Find("M:Claims.Payments.RejectsZero")!;
        Assert.Contains(theorem.Assumptions, a => a.UnitKey == validate.Key && a.Assumption == new VirAssumption(VirAssumptionKind.NonNull, "p"));
    }

    [Fact]
    public void AForAllOverAReferenceTypeAssumesItsValuesAreNotNull()
    {
        // Code review: a quantified record ranges over non-null values only, which the report must say, as for a parameter.
        var result = Script("""
            public sealed record Payment(int Id, int Amount);

            public static class S
            {
                [Theorem] static Proof Reflexive() => Prove.That(Spec.ForAll<Payment>(p => p.Amount == p.Amount)).By(Tactic.Intro("p"));

                [Theorem] static Proof Witness() => Prove.That(Spec.Exists<int>(n => n == n)).By(Tactic.Exact(Lean.Const("True.intro")));
            }
            """);
        var forAll = result.Find("M:S.Reflexive")!;
        Assert.Contains(forAll.Assumptions, a => a.UnitKey == forAll.Key && a.Assumption == new VirAssumption(VirAssumptionKind.NonNull, "p"));
        var exists = result.Find("M:S.Witness")!;
        Assert.DoesNotContain(exists.Assumptions, a => a.Assumption.Kind == VirAssumptionKind.NonNull);
    }

    // ---- VIR from JSON ----

    [Fact]
    public void TheEngineRunsFromVirReadBackFromJsonWithoutRoslyn()
    {
        var extraction = EngineCorpus.Extract("accepted");
        var inputs = extraction.Units
            .Select(u => new EngineUnit(VirReader.Read(VirWriter.Write(u.Unit)), u.DisplayName, u.Spans))
            .ToList();
        var fromJson = Pipeline.Run(inputs, engine.Bundle);
        var direct = engine.Run("accepted");
        Assert.Equal(
            direct.Units.Select(u => (u.Key, Describe(u))),
            fromJson.Units.Select(u => (u.Key, Describe(u))));

        // Warrant.Engine and everything it references, transitively, never mention Roslyn (KTD3).
        var seen = new HashSet<string>(StringComparer.Ordinal);
        var work = new Stack<AssemblyName>([typeof(Pipeline).Assembly.GetName()]);
        while (work.Count > 0)
        {
            var name = work.Pop();
            if (!seen.Add(name.Name!))
            {
                continue;
            }
            Assert.False(name.Name!.StartsWith("Microsoft.CodeAnalysis", StringComparison.Ordinal), $"the engine references {name.Name}");
            if (name.Name.StartsWith("Warrant", StringComparison.Ordinal))
            {
                foreach (var reference in Assembly.Load(name).GetReferencedAssemblies())
                {
                    work.Push(reference);
                }
            }
        }
        Assert.Contains("Warrant.Semantics", seen);
    }

    // ---- KTD22 ----

    [Fact]
    public void AnAdmittedTheoremWithAnotherTypeIsNotTheStatement()
    {
        // A faulty emitter that put "a = a" on WrongSum (Increment(2) == 4): the engine builds declarations only through
        // TheoremShell.WithProof, so such a declaration cannot come out of its API; the check it relies on is tested here.
        var extraction = EngineCorpus.Extract("refuted");
        var translation = Translator.Translate(extraction.Units.Select(u => u.Unit), engine.Bundle.Env);
        var shell = translation.Find("M:Corpus.Refuted.Increments.WrongSum")!.Theorem!;
        var env = Pipeline.Run(EngineCorpus.Inputs(extraction), engine.Bundle).Environment;
        Assert.Null(env.Find(shell.Name));

        var left = shell.Type.GetAppArgs()[1];
        var eqConst = (ConstExpr)shell.Type.GetAppFn();
        var aEqA = Expr.App(eqConst, shell.Type.GetAppArgs()[0], left, left);
        var faulty = new TheoremDecl(new TheoremInfo(shell.Name, EquatableArray<Name>.Empty, aEqA, ProofTerms.Rfl(shell.Statement)!, EquatableArray.Create(shell.Name)));
        KernelThread.Run(() => Kernel.Kernel.Add(env, faulty, KernelLimits.Corpus));
        Assert.NotNull(env.Find(shell.Name));
        Assert.False(ProofTerms.IsAdmittedAs(env, shell));

        // The honest declaration for a true claim passes the same check.
        var accepted = engine.Run("accepted");
        var capped = Translator.Translate(EngineCorpus.Extract("accepted").Units.Select(u => u.Unit), engine.Bundle.Env)
            .Find("M:Payouts.PayoutTheorems.CappedAtTheLimit")!.Theorem!;
        Assert.True(ProofTerms.IsAdmittedAs(accepted.Environment, capped));
    }

    [Fact]
    public void TheProofTermsAreTheOnesLeanElaborates()
    {
        var a = Literals.Int32(1);
        var statement = Conditions.Eq(VirPrimitive.Int32, a, Literals.Int32(2));
        var rfl = ProofTerms.Rfl(statement)!;
        Assert.Equal(Expr.App(Expr.Const(Name.Parse("Eq.refl"), Level.One), Literals.Type(VirPrimitive.Int32), a), rfl);
        Assert.Null(ProofTerms.Rfl(Conditions.Lt(VirPrimitive.Int32, a, a)));
        Assert.Equal(
            Expr.App(
                Expr.Const(Name.Parse("of_decide_eq_true")),
                statement.Prop,
                statement.Instance!,
                Expr.App(Expr.Const(Name.Parse("Eq.refl"), Level.One), Expr.Const(Name.Parse("Bool")), Expr.Const(Name.Parse("Bool.true")))),
            ProofTerms.Decide(statement));
        // A quantified statement has no instance, so no decide proof (M5a KTD17).
        Assert.Null(ProofTerms.Decide(new Condition(Expr.Forall(Name.Parse("x"), Literals.Type(VirPrimitive.Int32), statement.Prop), null)));
    }

    // ---- Export ----

    [Fact]
    public void TheNdjsonForTheAcceptedCorpusLoadsIntoAnEmptyEnvironment()
    {
        var result = engine.Run("accepted");
        var path = Path.Combine(Path.GetTempPath(), $"warrant-engine-{Guid.NewGuid():N}.ndjson");
        try
        {
            using (var file = File.Create(path))
            {
                result.WriteNdjson(file);
            }
            var declarations = Lean4Export.Lean4Export.ReadFile(path).Declarations;
            Assert.Equal(engine.Bundle.Declarations.Count + result.Admitted.Length, declarations.Count);
            var checks = new ExportChecker(new KernelEnvironment(), KernelLimits.Corpus).CheckAll(declarations);
            Assert.All(checks, c => Assert.True(c.Accepted, $"{c.Name}: {c.Error}"));
            Assert.Contains(checks, c => c.Name.ToString() == "Cs.Payouts.PayoutTheorems.CappedAtTheLimit");
        }
        finally
        {
            File.Delete(path);
        }
    }

    // ---- Proof scripts (M5a U11) ----

    [Fact]
    public void ForAllWithIntroAndExactRflIsProved()
    {
        var result = Script("""
            public static class S
            {
                [Theorem]
                static Proof Reflexive() =>
                    Prove.That(Spec.ForAll<int>(x => x == x)).By(Tactic.Intro("x"), Tactic.Exact(Lean.Const("rfl")));
            }
            """);
        var proved = Assert.IsType<ProvedOutcome>(result.Find("M:S.Reflexive"));
        Assert.Equal(ProofKind.Script, proved.By);
        Assert.Equal("script", Reports.AssumptionReports.ProofName(proved.By));
        Assert.Contains(proved.Certificate, result.Admitted);
    }

    [Fact]
    public void TheParametersAreIntroducedUnderTheirCSharpNamesBeforeTheScript()
    {
        var result = Script("""
            public static class S
            {
                [Theorem] static Proof Start(int a, int b) => Prove.That(Spec.Implies(a == b, b == a));

                [Theorem]
                static Proof Symmetric(int a, int b) =>
                    Prove.That(Spec.Implies(a == b, b == a))
                         .By(Tactic.Intro("h"), Tactic.Apply(Lean.Const("Eq.symm")), Tactic.Exact("h"));
            }
            """);
        var start = Assert.IsType<NotProvedOutcome>(result.Find("M:S.Start(System.Int32,System.Int32)"));
        Assert.Equal("unsolved goals", start.Message);
        Assert.Equal("a b : Int32\n⊢ a = b → b = a", start.Goals);
        Assert.Null(start.TacticSpan);

        var proved = Assert.IsType<ProvedOutcome>(result.Find("M:S.Symmetric(System.Int32,System.Int32)"));
        var proof = proved.Certificate.Value.Value;
        Assert.False(proof.HasFVar || proof.HasExprMVar || proof.HasLevelMVar);
        // fun a b h => Eq.symm h: the parameters, then the script's own binder.
        Assert.Equal(["a", "b", "h"], Binders(proof));
    }

    [Fact]
    public void ALemmaNamedWithNameofIsApplied()
    {
        var result = Script("""
            public static class S
            {
                [Theorem]
                static Proof Reflexive() =>
                    Prove.That(Spec.ForAll<int>(x => x == x)).By(Tactic.Intro("x"), Tactic.Exact(Lean.Const("rfl")));

                [Theorem] static Proof UsesIt(int a) => Prove.That(a == a).By(Tactic.Apply(nameof(Reflexive)));
            }
            """);
        Assert.IsType<ProvedOutcome>(result.Find("M:S.Reflexive"));
        Assert.IsType<ProvedOutcome>(result.Find("M:S.UsesIt(System.Int32)"));
    }

    [Fact]
    public void AFalseClaimWithNoScriptShowsItsGoalAndACounterexample()
    {
        var result = Script("""
            public static class Increments
            {
                [Verified] public static int Increment(int x) => x + 1;
                [Theorem] static Proof AlwaysLarger(int x) => Prove.That(Increment(x) > x);
            }
            """);
        var outcome = Assert.IsType<NotProvedOutcome>(result.Find("M:Increments.AlwaysLarger(System.Int32)"));
        Assert.Equal("WRT0001", NotProvedOutcome.Code);
        Assert.Equal("unsolved goals", outcome.Message);
        Assert.Equal("x : Int32\n⊢ Increment x > x", outcome.Goals);
        Assert.Equal([new CounterexampleValue("x", "2147483647")], outcome.Counterexample.AsEnumerable());
        Assert.Equal(
            "Theorem 'AlwaysLarger' could not be proved: unsolved goals. Counterexample: x = 2147483647.",
            Reports.OutcomeText.NotProvedMessage("AlwaysLarger", outcome));
        Assert.Equal(["x : Int32", "⊢ Increment x > x"], Reports.OutcomeText.NotProvedDetails(outcome));
        Assert.Null(result.Environment.Find(Name.Parse("Cs.Increments.AlwaysLarger")));
    }

    [Fact]
    public void UnfoldShowsTheBodyAndAFailedTryLeavesItsGoal()
    {
        const string Source = """
            public static class Increments
            {
                [Verified] public static int Increment(int x) => x + 1;

                [Theorem]
                static Proof AlwaysLarger(int x) =>
                    Prove.That(Increment(x) > x).By(Tactic.Unfold(nameof(Increment)), Tactic.Try(Tactic.Omega()));
            }
            """;
        var outcome = Assert.IsType<NotProvedOutcome>(Script(Source).Find("M:Increments.AlwaysLarger(System.Int32)"));
        // omega fails on the false claim, and Try leaves the goal Unfold made.
        Assert.Equal("unsolved goals", outcome.Message);
        Assert.Equal("x : Int32\n⊢ x + 1 > x", outcome.Goals);
        Assert.Null(outcome.TacticSpan);
        Assert.Equal([new CounterexampleValue("x", "2147483647")], outcome.Counterexample.AsEnumerable());
    }

    [Fact]
    public void OmegaWithoutArithmeticFailsAtItsCallShowingTheGoal()
    {
        const string Source = """
            public static class S
            {
                [Theorem] static Proof T(bool b) => Prove.That(b == b).By(Tactic.AllGoals(Tactic.Omega()));
            }
            """;
        var outcome = Assert.IsType<NotProvedOutcome>(Script(Source).Find("M:S.T(System.Boolean)"));
        Assert.StartsWith("omega could not prove the goal:\nNo usable constraints found.", outcome.Message, StringComparison.Ordinal);
        Assert.Equal("Tactic.Omega()", InlineText(Source, outcome.TacticSpan));
        Assert.Equal("b : Bool\n⊢ b = b", outcome.Goals);
        Assert.Empty(outcome.Counterexample);
    }

    [Fact]
    public void AScriptThatLeavesTwoGoalsShowsBoth()
    {
        var outcome = Assert.IsType<NotProvedOutcome>(Script("""
            public static class S
            {
                [Theorem]
                static Proof Both(int a, int b) =>
                    Prove.That(Spec.Implies(a == b, a == b && b == a)).By(Tactic.Intro("h"), Tactic.Apply(Lean.Const("And.intro")));
            }
            """).Find("M:S.Both(System.Int32,System.Int32)"));
        Assert.Equal("unsolved goals", outcome.Message);
        Assert.Equal("case left\na b : Int32\nh : a = b\n⊢ a = b\n\ncase right\na b : Int32\nh : a = b\n⊢ b = a", outcome.Goals);
    }

    [Fact]
    public void ExactOfTheWrongTypeReportsATypeMismatchAtTheExactCall()
    {
        const string Source = """
            public static class S
            {
                [Theorem] static Proof Mismatch(int a) => Prove.That(a == a).By(Tactic.Exact(Lean.Const("Nat.zero")));
            }
            """;
        var outcome = Assert.IsType<NotProvedOutcome>(Script(Source).Find("M:S.Mismatch(System.Int32)"));
        Assert.Equal("Tactic `exact` failed: type mismatch\n  Nat.zero\nhas type\n  Nat\nbut is expected to have type\n  a = a", outcome.Message);
        Assert.Equal("a : Int32\n⊢ a = a", outcome.Goals);
        Assert.Equal("Tactic.Exact(Lean.Const(\"Nat.zero\"))", InlineText(Source, outcome.TacticSpan));
        Assert.Equal(
            "Theorem 'Mismatch' could not be proved: Tactic `exact` failed: type mismatch",
            Reports.OutcomeText.NotProvedMessage("Mismatch", outcome));
    }

    [Fact]
    public void ATacticFuelOfOneReportsTacticFuel()
    {
        const string Source = """
            public static class S
            {
                [Theorem] static Proof Default(int a) => Prove.That(a == a).By(Tactic.Exact(Lean.Const("rfl")));
                [Theorem(TacticFuel = 1)] static Proof Starved(int a) => Prove.That(a == a).By(Tactic.Exact(Lean.Const("rfl")));
            }
            """;
        var result = Script(Source);
        Assert.IsType<ProvedOutcome>(result.Find("M:S.Default(System.Int32)"));
        var starved = Assert.IsType<UndecidedOutcome>(result.Find("M:S.Starved(System.Int32)"));
        Assert.Equal("WRT0006", UndecidedOutcome.Code);
        Assert.Equal("tactic fuel ran out (1 steps) while running the proof script.", starved.Reason);

        var project = Assert.IsType<UndecidedOutcome>(Script(Source, engine.Options with { TacticFuel = 1 }).Find("M:S.Default(System.Int32)"));
        Assert.Contains("tactic fuel ran out", project.Reason, StringComparison.Ordinal);
    }

    [Fact]
    public void AZeroSecondTimeLimitReportsTheTimeLimit()
    {
        var result = Script("""
            public static class S
            {
                [Verified] public static int Inc(int x) => x + 1;
                [Theorem] static Proof Scripted(int a) => Prove.That(a == a).By(Tactic.Exact(Lean.Const("rfl")));
                [Theorem] static Proof Computed() => Prove.That(Inc(1) == 2);
            }
            """, engine.Options with { Timeout = TimeSpan.Zero });
        Assert.IsType<TranslatedOutcome>(result.Find("M:S.Inc(System.Int32)"));
        foreach (var key in new[] { "M:S.Scripted(System.Int32)", "M:S.Computed" })
        {
            var outcome = Assert.IsType<UndecidedOutcome>(result.Find(key));
            Assert.Contains("the time limit of 0 s was reached", outcome.Reason, StringComparison.Ordinal);
        }
    }

    [Fact]
    public void AWrongProofWarrantBuildsIsAnInternalErrorNeverAProof()
    {
        // After the script, swap the proof of x = x for Bool.true, a term of another type: the kernel must reject it.
        var options = engine.Options with { TamperWithProof = _ => Expr.Const(Name.Parse("Bool.true")) };
        var result = Script("""
            public static class S
            {
                [Theorem] static Proof Reflexive(int a) => Prove.That(a == a).By(Tactic.Exact(Lean.Const("rfl")));
            }
            """, options);
        var outcome = Assert.IsType<InternalErrorOutcome>(result.Find("M:S.Reflexive(System.Int32)"));
        Assert.Equal("WRT0010", InternalErrorOutcome.Code);
        Assert.StartsWith("the kernel rejected the proof Warrant built: ", outcome.Reason, StringComparison.Ordinal);
        Assert.Null(result.Environment.Find(Name.Parse("Cs.S.Reflexive")));
        Assert.Equal("internal", Reports.AssumptionReports.OutcomeName(outcome));
    }

    [Fact]
    public void ATheoremWhoseLemmaFailedIsSkippedNamingTheLemma()
    {
        var result = Script("""
            public static class S
            {
                [Theorem] static Proof Lemma(int a) => Prove.That(a == a + 0);
                [Theorem] static Proof UsesLemma(int a) => Prove.That(a == a + 0).By(Tactic.Exact(nameof(Lemma)));
            }
            """);
        Assert.IsType<NotProvedOutcome>(result.Find("M:S.Lemma(System.Int32)"));
        var skipped = Assert.IsType<SkippedOutcome>(result.Find("M:S.UsesLemma(System.Int32)"));
        Assert.Equal("M:S.Lemma(System.Int32)", skipped.Dependency);
        Assert.Contains("Lemma", skipped.Reason, StringComparison.Ordinal);
    }

    // ---- omega (M5a U18) ----

    [Fact]
    public void LargerBelowMaxIsProvedByUnfoldSimpAndOmega()
    {
        // The plan's Success Criterion: Spec.Implies(x < int.MaxValue, Increment(x) > x), through the omega-prep set's
        // bmod_def and omega's reflective proof, which the kernel checked before the outcome was reported.
        var result = engine.Run("m5a/accepted");
        var proved = Assert.IsType<ProvedOutcome>(result.Find("M:Corpus.Increments.LargerBelowMax(System.Int32)"));
        var proof = proved.Certificate.Value.Proof;
        var text = proof.ToString();
        // Int.bmod_def is a definitional rewrite, so it leaves no trace; the if it makes is the disjunction omega splits.
        Assert.Contains("Int32.toInt_add", text, StringComparison.Ordinal);
        Assert.Contains("Lean.Omega.ite_disjunction", text, StringComparison.Ordinal);
        Assert.Contains("Lean.Omega.LinearCombo.coordinate_eval_0", text, StringComparison.Ordinal);
        Assert.Contains("Int32.le_toInt", text, StringComparison.Ordinal);
        Assert.Equal(["Classical.choice", "Quot.sound", "propext"], Axioms(result.Environment, proof));
    }

    [Fact]
    public void ClampIsBoundedThroughItsLiterals()
    {
        var proved = Assert.IsType<ProvedOutcome>(engine.Run("m5a/accepted").Find("M:Corpus.Clamps.AtMostOneHundred(System.Int32)"));
        var text = proved.Certificate.Value.Proof.ToString();
        Assert.Contains("Warrant.Int32.toInt_ofNat_lit", text, StringComparison.Ordinal);
        Assert.Contains("apply_ite", text, StringComparison.Ordinal);
    }

    [Fact]
    public void AlwaysLargerFailsAtOmegaWithItsConstraintsAndTheCounterexample()
    {
        // The exit criterion's false claim: the goal omega was given (after Unfold, before the prep step) with C# names,
        // omega's constraints with its atoms printed the same way, and the boundary search's counterexample.
        var outcome = Assert.IsType<NotProvedOutcome>(engine.Run("m5a/refuted").Find("M:Corpus.Refuted.Increments.AlwaysLarger(System.Int32)"));
        Assert.Equal("WRT0001", NotProvedOutcome.Code);
        Assert.Equal("x : Int32\n⊢ x + 1 > x", outcome.Goals);
        Assert.StartsWith("omega could not prove the goal:\na possible counterexample may satisfy the constraints\n", outcome.Message, StringComparison.Ordinal);
        Assert.Contains("\n b := (x.toInt + ↑1) / 4294967296", outcome.Message, StringComparison.Ordinal);
        Assert.NotNull(outcome.TacticSpan);
        Assert.Equal([new CounterexampleValue("x", "2147483647")], outcome.Counterexample.AsEnumerable());
        Assert.Equal(
            "Theorem 'AlwaysLarger' could not be proved: omega could not prove the goal. Counterexample: x = 2147483647.",
            Reports.OutcomeText.NotProvedMessage("AlwaysLarger", outcome));
    }

    [Fact]
    public void EveryEmittedConstantIsABundleRoot()
    {
        var roots = File.ReadAllLines(TestData.Path("bundle-roots.txt"))
            .Select(l => l.Trim())
            .Where(l => l.Length > 0 && !l.StartsWith('#'))
            .Select(Name.Parse)
            .ToHashSet();
        Assert.NotEmpty(EmittedConstants.All);
        Assert.All(EmittedConstants.All, n =>
        {
            Assert.Contains(n, roots);
            Assert.NotNull(engine.Bundle.Env.Find(n));
        });
    }

    // ---- cases and induction (M5a U14) ----

    [Fact]
    public void CasesOnAClosedEnumGivesOneGoalPerMemberInDeclarationOrder()
    {
        var outcome = Assert.IsType<NotProvedOutcome>(Script("""
            [Closed]
            public enum ClaimStatus { Open, Paid, Denied, Withdrawn }

            public static class S
            {
                [Verified] public static int Priority(ClaimStatus s) => s switch { ClaimStatus.Open => 2, ClaimStatus.Paid => 0, _ => 1 };
                [Theorem] static Proof Split(ClaimStatus s) => Prove.That(Priority(s) >= 0).By(Tactic.Cases("s"));
            }
            """).Find("M:S.Split(ClaimStatus)"));
        Assert.Equal("unsolved goals", outcome.Message);
        Assert.Equal(
            "case Open\n⊢ Priority ClaimStatus.Open ≥ 0\n\ncase Paid\n⊢ Priority ClaimStatus.Paid ≥ 0\n\n"
            + "case Denied\n⊢ Priority ClaimStatus.Denied ≥ 0\n\ncase Withdrawn\n⊢ Priority ClaimStatus.Withdrawn ≥ 0",
            outcome.Goals);
    }

    [Fact]
    public void CasesOnARecordGivesOneGoalWithItsFieldsAsHypotheses()
    {
        var outcome = Assert.IsType<NotProvedOutcome>(Script("""
            public enum PaymentStatus { Pending, Processed, Failed }
            public sealed record Payment(int Id, int Amount, PaymentStatus Status);

            public static class S
            {
                [Theorem] static Proof Split(Payment p) => Prove.That(p.Amount == p.Amount).By(Tactic.Cases("p"));
            }
            """).Find("M:S.Split(Payment)"));
        Assert.Equal("unsolved goals", outcome.Message);
        Assert.Equal(
            "Id Amount : Int32\nStatus : PaymentStatus\n⊢ (new Payment Id Amount Status).Amount = (new Payment Id Amount Status).Amount",
            outcome.Goals);
    }

    [Fact]
    public void AClosedEnumTheoremIsProvedByCasesAndRflInEachBranch()
    {
        var result = Script("""
            [Closed]
            public enum Light { Red, Amber, Green }

            public static class S
            {
                [Verified] public static Light Next(Light l) => l switch { Light.Red => Light.Amber, Light.Amber => Light.Green, _ => Light.Red };

                [Theorem]
                static Proof ThreeStepsComeBack(Light l) =>
                    Prove.That(Next(Next(Next(l))) == l).By(Tactic.Cases("l"), Tactic.AllGoals(Tactic.Exact(Lean.Const("rfl"))));
            }
            """);
        var proved = Assert.IsType<ProvedOutcome>(result.Find("M:S.ThreeStepsComeBack(Light)"));
        Assert.Equal(ProofKind.Script, proved.By);
        Assert.Contains("Cs.Light.casesOn", proved.Certificate.Value.Value.ToString(), StringComparison.Ordinal);
    }

    [Fact]
    public void InductionOnABoolProvesAndTrueIsIdentityWithRflForSimp()
    {
        // The corpus's AndTrueIsIdentity closes its goals with simp (U17); with rfl, it is proved now.
        var result = Script("""
            public static class S
            {
                [Verified] public static bool AndTrue(bool b) => b && true;

                [Theorem]
                static Proof AndTrueIsIdentity(bool b) =>
                    Prove.That(AndTrue(b) == b)
                         .By(Tactic.Unfold(nameof(AndTrue)), Tactic.Induction("b"), Tactic.AllGoals(Tactic.Exact(Lean.Const("rfl"))));
            }
            """);
        Assert.Equal(ProofKind.Script, Assert.IsType<ProvedOutcome>(result.Find("M:S.AndTrueIsIdentity(System.Boolean)")).By);
    }

    [Fact]
    public void CasesOnAnEquationReportsThatIndexedFamiliesAreNotSupportedYet()
    {
        var outcome = Assert.IsType<NotProvedOutcome>(Script("""
            public static class S
            {
                [Theorem]
                static Proof Symmetric(int a, int b) => Prove.That(Spec.Implies(a == b, b == a)).By(Tactic.Intro("h"), Tactic.Cases("h"));
            }
            """).Find("M:S.Symmetric(System.Int32,System.Int32)"));
        Assert.Equal("Tactic `cases` failed: cases on an indexed family is not supported yet", outcome.Message);
        Assert.Equal("a b : Int32\nh : a = b\n⊢ b = a", outcome.Goals);
    }

    // ---- simp (M5a U17) ----

    [Fact]
    public void ValidImpliesPositiveIsProvedByUnfoldAndSimpDependingOnlyOnPropext()
    {
        // The plan's Success Criterion: design §5.1's theorem, Unfold(nameof(Validate)) then Simp(), end to end.
        var result = engine.Run("m5a/accepted");
        var proved = Assert.IsType<ProvedOutcome>(result.Find("M:Claims.Payments.ValidImpliesPositive(Claims.Payment)"));
        Assert.Equal(ProofKind.Script, proved.By);
        var proof = proved.Certificate.Value.Proof;
        var text = proof.ToString();
        Assert.Contains("Warrant.ite_eq_iff", text, StringComparison.Ordinal);
        Assert.Contains("eq_false_of_decide", text, StringComparison.Ordinal);
        Assert.Contains("implies_congr_ctx", text, StringComparison.Ordinal);
        Assert.Equal(["propext"], Axioms(result.Environment, proof));
    }

    [Fact]
    public void WithoutDecideSimpLeavesTheClosedComparisonsAndShowsTheGoal()
    {
        const string Source = """
            public enum PaymentStatus { Pending, Processed, Failed }
            public sealed record Payment(int Id, int Amount, PaymentStatus Status);
            public enum PaymentResult { Valid, InvalidAmount, InvalidStatus }

            public static class Payments
            {
                [Verified]
                public static PaymentResult Validate(Payment p)
                {
                    if (p.Amount <= 0) return PaymentResult.InvalidAmount;
                    if (p.Status != PaymentStatus.Pending) return PaymentResult.InvalidStatus;
                    return PaymentResult.Valid;
                }

                [Theorem]
                static Proof ValidImpliesPositive(Payment p) =>
                    Prove.That(Spec.Implies(Validate(p) == PaymentResult.Valid, p.Amount > 0))
                         .By(Tactic.Unfold(nameof(Validate)), Tactic.Simp().With(decide: false));
            }
            """;
        var outcome = Assert.IsType<NotProvedOutcome>(Script(Source).Find("M:Payments.ValidImpliesPositive(Payment)"));
        Assert.Equal("unsolved goals", outcome.Message);
        // Without decide, nothing turns InvalidAmount = Valid or InvalidStatus = Valid into False.
        Assert.Equal(
            "p : Payment\n⊢ p.Amount ≤ 0 ∧ PaymentResult.InvalidAmount = PaymentResult.Valid ∨ 0 < p.Amount ∧ "
            + "(¬p.Status = PaymentStatus.Pending → PaymentResult.InvalidStatus = PaymentResult.Valid) → 0 < p.Amount",
            outcome.Goals);
    }

    [Fact]
    public void SimpWithACSharpTheoremRewritesWithIt()
    {
        var result = Script("""
            public static class S
            {
                [Verified] public static int Twice(int x) => x + x;

                [Theorem]
                static Proof TwiceIsDoubling() =>
                    Prove.That(Spec.ForAll<int>(x => Twice(x) == x + x)).By(Tactic.Intro("x"), Tactic.Exact(Lean.Const("rfl")));

                [Theorem] static Proof WithIt(int a) => Prove.That(Twice(a) == a + a).By(Tactic.Simp(nameof(TwiceIsDoubling)));

                [Theorem] static Proof WithoutIt(int a) => Prove.That(Twice(a) == a + a).By(Tactic.Simp());
            }
            """);
        var proved = Assert.IsType<ProvedOutcome>(result.Find("M:S.WithIt(System.Int32)"));
        Assert.Contains("Cs.S.TwiceIsDoubling", proved.Certificate.Value.Proof.ToString(), StringComparison.Ordinal);
        var without = Assert.IsType<NotProvedOutcome>(result.Find("M:S.WithoutIt(System.Int32)"));
        Assert.Equal("`simp` made no progress", without.Message);
        Assert.Equal("a : Int32\n⊢ Twice a = a + a", without.Goals);
    }

    [Fact]
    public void ALoopingLemmaStopsAtTheTacticFuel()
    {
        var outcome = Assert.IsType<UndecidedOutcome>(Script("""
            public static class S
            {
                [Verified] public static int Same(int x) => x;

                [Theorem]
                static Proof Grows() =>
                    Prove.That(Spec.ForAll<int>(x => Same(x) == Same(Same(x)))).By(Tactic.Intro("x"), Tactic.Exact(Lean.Const("rfl")));

                [Theorem] static Proof Loops(int a) => Prove.That(Same(a) == a).By(Tactic.Simp(nameof(Grows)));
            }
            """).Find("M:S.Loops(System.Int32)"));
        Assert.Equal("WRT0006", UndecidedOutcome.Code);
        Assert.Equal(
            string.Create(CultureInfo.InvariantCulture, $"tactic fuel ran out ({EngineOptions.DefaultTacticFuel:N0} steps) while running the proof script."),
            outcome.Reason);
    }

    /// <summary>The axioms a proof depends on, through every constant it mentions (Lean's <c>collectAxioms</c>).</summary>
    internal static List<string> Axioms(KernelEnvironment env, Expr proof)
    {
        var seen = new HashSet<Name>();
        var axioms = new SortedSet<string>(StringComparer.Ordinal);
        var pending = new Stack<Expr>([proof]);
        while (pending.Count > 0)
        {
            ExprOps.ForEach(pending.Pop(), (x, _) =>
            {
                if (x is ConstExpr c && seen.Add(c.Name) && env.Find(c.Name) is { } info)
                {
                    if (info is AxiomInfo)
                    {
                        axioms.Add(c.Name.ToString());
                    }
                    pending.Push(info.Type);
                    if (info is DefinitionInfo d)
                    {
                        pending.Push(d.Value);
                    }
                    else if (info is TheoremInfo t)
                    {
                        pending.Push(t.Proof);
                    }
                    else if (info is InductiveInfo ind)
                    {
                        foreach (var ctor in ind.Constructors)
                        {
                            pending.Push(Expr.Const(ctor));
                        }
                    }
                }
                return true;
            });
        }
        return [.. axioms];
    }

    // ---- Helpers ----

    private EngineResult Run(string source) => Pipeline.Run(EngineCorpus.Inputs(EngineCorpus.Inline(source)), engine.Bundle);

    private EngineResult Script(string source, EngineOptions? options = null) =>
        Pipeline.Run(EngineCorpus.Inputs(EngineCorpus.Inline(source)), engine.Bundle, options ?? engine.Options);

    private static List<string> Binders(Expr e)
    {
        var names = new List<string>();
        while (e is LamExpr lam)
        {
            names.Add(lam.BinderName.ToString());
            e = lam.Body;
        }
        return names;
    }

    /// <summary>The text of a span in an inline source, which <see cref="EngineCorpus.Inline"/> compiles after one using line.</summary>
    private static string InlineText(string source, VirSpan? span)
    {
        Assert.NotNull(span);
        Assert.Equal(span.StartLine, span.EndLine);
        var lines = ("using Warrant;\n" + source).Split('\n');
        return lines[span.StartLine - 1][(span.StartColumn - 1)..(span.EndColumn - 1)];
    }

    private static string Describe(UnitOutcome outcome) => outcome switch
    {
        ProvedOutcome p => $"proved {p.By}",
        FalseOutcome => "false",
        _ => outcome.GetType().Name,
    };

    private static string SourceText(VirSpan? span)
    {
        Assert.NotNull(span);
        var lines = File.ReadAllLines(Path.Combine(EngineCorpus.Root, span.Path));
        Assert.Equal(span.StartLine, span.EndLine);
        return lines[span.StartLine - 1][(span.StartColumn - 1)..(span.EndColumn - 1)];
    }
}
