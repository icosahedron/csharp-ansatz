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
                        Assert.True(by == (proved.By == ProofKind.Rfl ? "rfl" : "decide"), $"{member.Name}: expected {by}, got {proved.By}");
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

    // ---- Helpers ----

    private EngineResult Run(string source) => Pipeline.Run(EngineCorpus.Inputs(EngineCorpus.Inline(source)), engine.Bundle);

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
