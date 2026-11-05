using Warrant.Extraction;
using Warrant.Vir;
using static Warrant.Extraction.Tests.Inline;

namespace Warrant.Extraction.Tests;

/// <summary>Quantified theorems, proof scripts and recursion measures (plan M5a U9, test scenarios).</summary>
public class M5aExtractionTests
{
    private const string Increment = """
        public static class C
        {
            [Verified] public static int Increment(int x) => x + 1;
        """;

    private static ExtractionResult Theorems(string theorems) => Extract(Increment + theorems + "\n}");

    [Fact]
    public void ATheoremsParametersBecomeTheUnitsParameters()
    {
        var unit = Unit(Theorems("[Theorem] static Proof AlwaysLarger(int x) => Prove.That(Increment(x) > x);"), "M:C.AlwaysLarger(System.Int32)");
        Assert.Equal([new VirParam("x", VirType.Int32)], unit.Params);
        var call = new CallExpr(VirType.Int32, "M:C.Increment(System.Int32)", VirList.Of<VirExpr>(new ParamExpr(VirType.Int32, 0)));
        Assert.Equal(new CompareExpr(CompareOp.Gt, CompareKind.Int, call, new ParamExpr(VirType.Int32, 0)), unit.Statement);
        Assert.Null(unit.Script);
        Assert.Null(unit.Budget);
    }

    [Fact]
    public void ARecordParameterOfATheoremIsAssumedNonNull()
    {
        var unit = Unit(
            Extract("""
                public sealed record P(int A);
                public static class C
                {
                    [Theorem] static Proof Positive(P p) => Prove.That(p.A == p.A);
                }
                """),
            "M:C.Positive(P)");
        Assert.Equal(["p"], NonNull(unit));
    }

    [Fact]
    public void SpecForAllBindsALocalReadInItsBody()
    {
        var unit = Unit(Theorems("[Theorem] static Proof ZeroIsNeutral() => Prove.That(Spec.ForAll<int>(y => y + 0 == y));"), "M:C.ZeroIsNeutral");
        var y = new LocalExpr(VirType.Int32, 0);
        Assert.Equal(
            new ForAllExpr(0, "y", VirType.Int32, new CompareExpr(
                CompareOp.Eq, CompareKind.Int, new BinaryExpr(VirType.Int32, BinaryOp.Add, VirOverflow.Wrap, y, LitExpr.Int32(0)), y)),
            unit.Statement);
    }

    [Fact]
    public void NestedQuantifiersGetDistinctLocals()
    {
        var unit = Unit(
            Theorems("[Theorem] static Proof Nested(int x) => Prove.That(Spec.ForAll<int>(a => Spec.Exists<bool>(b => b == (a > x))));"),
            "M:C.Nested(System.Int32)");
        var forAll = Assert.IsType<ForAllExpr>(unit.Statement);
        var exists = Assert.IsType<ExistsExpr>(forAll.Body);
        Assert.Equal((0, "a", VirType.Int32), (forAll.Local, forAll.Name, forAll.Domain));
        Assert.Equal((1, "b", VirType.Bool), (exists.Local, exists.Name, exists.Domain));
        var compare = Assert.IsType<CompareExpr>(exists.Body);
        Assert.Equal(new LocalExpr(VirType.Bool, 1), compare.L);
    }

    [Fact]
    public void AScriptIsAListOfTacticNodesAndANameofAddsADependency()
    {
        var result = Extract("""
            public enum PaymentResult { Valid, Invalid }
            public sealed record Payment(int Amount);
            public static class C
            {
                [Verified] public static PaymentResult Validate(Payment p) => p.Amount > 0 ? PaymentResult.Valid : PaymentResult.Invalid;

                [Theorem]
                static Proof ValidImpliesPositive(Payment p) =>
                    Prove.That(Spec.Implies(Validate(p) == PaymentResult.Valid, p.Amount > 0))
                         .By(Tactic.Unfold(nameof(Validate)), Tactic.Simp());
            }
            """);
        var extracted = result.Find("M:C.ValidImpliesPositive(Payment)")!;
        var unit = extracted.Unit;
        Assert.Equal(
            VirList.Of(
                new TacticNode("unfold", VirList.Of<VirTacticArg>(new UnitRefArg("M:C.Validate(Payment)"))),
                new TacticNode("simp", VirList<VirTacticArg>.Empty)),
            unit.Script);
        Assert.Contains("M:C.Validate(Payment)", unit.Deps);

        // Each tactic's span is its Tactic.X(...) call, so a failure points at the step that failed.
        var nodes = VirTree.PreOrder(unit);
        int unfold = nodes.Count - 2;
        Assert.True(extracted.Spans.TryGetSpan(unfold, out var span));
        Assert.Equal(new VirSpan("Test.cs", 11, 18, 11, 49), span);
    }

    [Fact]
    public void LeanConstStringsNestedTacticsAndOptionsAreArguments()
    {
        var unit = Unit(
            Theorems("""
                [Theorem]
                static Proof Steps(int x) =>
                    Prove.That(Spec.Implies(x > 0, Increment(x) > x))
                         .By(Tactic.Intro("h"), Tactic.Exact(Lean.Const("Nat.add_comm")), Tactic.Apply("h"),
                             Tactic.AllGoals(Tactic.Try(Tactic.Simp(Lean.Const("Int32.add_def")).With(decide: false))), Tactic.Omega());
                """),
            "M:C.Steps(System.Int32)");
        Assert.Equal(
            VirList.Of(
                new TacticNode("intro", VirList.Of<VirTacticArg>(new StringArg("h"))),
                new TacticNode("exact", VirList.Of<VirTacticArg>(new LeanRefArg("Nat.add_comm"))),
                new TacticNode("apply", VirList.Of<VirTacticArg>(new StringArg("h"))),
                new TacticNode("all_goals", VirList.Of<VirTacticArg>(new TacticArg(new TacticNode("try", VirList.Of<VirTacticArg>(new TacticArg(
                    new TacticNode("simp", VirList.Of<VirTacticArg>(new LeanRefArg("Int32.add_def"), new OptionArg("decide", new BoolArg(false)))))))))),
                new TacticNode("omega", VirList<VirTacticArg>.Empty)),
            unit.Script);
    }

    [Fact]
    public void ANameofOfAnOverloadedTheoremIsWrt0004()
    {
        var result = Theorems("""
            [Theorem] static Proof MyLemma() => Prove.That(Increment(1) == 2);
            [Theorem] static Proof MyLemma(int x) => Prove.That(Increment(x) == x + 1);
            [Theorem] static Proof UsesIt(int x) => Prove.That(Increment(x) == x + 1).By(Tactic.Simp(nameof(MyLemma)));
            """);
        Assert.Equal("WRT0004 | nameof of an overloaded method", Only(result, "M:C.UsesIt(System.Int32)"));
        Assert.NotNull(result.Find("M:C.MyLemma"));
    }

    [Theory]
    [InlineData("Tactic.Simp(\"h\")", "string literal where a lemma is expected")]
    [InlineData("Tactic.Unfold(\"Increment\")", "string literal where a member name is expected")]
    [InlineData("Tactic.Unfold(nameof(System.Math.PI))", "nameof that names no verified member or theorem")]
    [InlineData("Tactic.Exact(1)", "unsupported script argument")]
    public void AMalformedScriptIsWrt0004(string step, string construct)
    {
        var result = Theorems($"[Theorem] static Proof T(int x) => Prove.That(Increment(x) == x + 1).By({step});");
        Assert.Equal("WRT0004 | " + construct, Only(result, "M:C.T(System.Int32)"));
    }

    [Fact]
    public void ATheoremUsedInItsOwnProofIsWrt0004()
    {
        var result = Theorems("[Theorem] static Proof T(int x) => Prove.That(Increment(x) == x + 1).By(Tactic.Exact(nameof(T)));");
        Assert.Equal("WRT0004 | theorem used in its own proof", Only(result, "M:C.T(System.Int32)"));
    }

    [Fact]
    public void BudgetOverridesComeFromTheTheoremAttribute()
    {
        var result = Theorems("""
            [Theorem(TimeoutSeconds = 60)] static Proof Slow(int x) => Prove.That(Increment(x) == x + 1);
            [Theorem(TacticFuel = 5, KernelFuel = 5000000000)] static Proof Fuelled(int x) => Prove.That(Increment(x) == x + 1);
            """);
        Assert.Equal(new VirBudget(60, 0, 0), Unit(result, "M:C.Slow(System.Int32)").Budget);
        Assert.Equal(new VirBudget(0, 5, 5_000_000_000), Unit(result, "M:C.Fuelled(System.Int32)").Budget);
    }

    [Fact]
    public void ARecursiveMethodWithALeadingMeasureExtractsWithADecreasesNode()
    {
        // Spec.Decreases is [Conditional("WARRANT_CONTRACTS")], which this compilation does not define: the call is not in
        // the IL, but it is in the operation tree extraction reads.
        var result = Extract("""
            public static class C
            {
                [Verified]
                public static int Sum(int n)
                {
                    Spec.Decreases(n);
                    if (n <= 0) return 0;
                    return n + Sum(n - 1);
                }

                [Verified]
                public static long SumLong(long n)
                {
                    Spec.Decreases(n);
                    if (n <= 0) return 0;
                    return n + SumLong(n - 1);
                }
            }
            """);
        Assert.Empty(result.Diagnostics);
        var sum = Unit(result, "M:C.Sum(System.Int32)");
        var body = Assert.IsType<BlockStmt>(sum.Body);
        // An int measure keeps its type; the parameter's long is an implicit widening the call adds.
        Assert.Equal(new DecreasesStmt(new ParamExpr(VirType.Int32, 0)), body.Stmts[0]);
        Assert.Empty(sum.Deps);
        var sumLong = Assert.IsType<BlockStmt>(Unit(result, "M:C.SumLong(System.Int64)").Body);
        Assert.Equal(new DecreasesStmt(new ParamExpr(VirType.Int64, 0)), sumLong.Stmts[0]);
    }

    [Fact]
    public void RecursionWithoutALeadingMeasureIsRejected()
    {
        var result = Extract("""
            public static class C
            {
                [Verified] public static int Factorial(int n) => n <= 1 ? 1 : n * Factorial(n - 1);

                [Verified]
                public static int Late(int n)
                {
                    if (n <= 0) return 0;
                    Spec.Decreases(n);
                    return Late(n - 1);
                }

                [Verified]
                public static int Nested(int n)
                {
                    Spec.Decreases(n);
                    if (n <= 0) return 0;
                    return Nested(Nested(n - 1));
                }

                [Verified] public static int Caller(int n) => Factorial(n);
            }
            """);
        Assert.Equal("WRT0002 | recursion without Spec.Decreases", Only(result, "M:C.Factorial(System.Int32)"));
        Assert.Equal("WRT0002 | Spec.Decreases not first", Only(result, "M:C.Late(System.Int32)"));
        Assert.Equal("WRT0002 | nested recursion", Only(result, "M:C.Nested(System.Int32)"));
        Assert.Equal("WRT0002 | depends on a rejected unit", Only(result, "M:C.Caller(System.Int32)"));
    }

    [Fact]
    public void ALambdaOutsideAQuantifierStaysWrt0002AndAQuantifierOutsideATheoremIsWrt0004()
    {
        var result = Extract("""
            public static class C
            {
                [Verified] public static int Apply(System.Func<int, int> f, int x) => x;
                [Verified] public static int Lambda(int x) => Apply(y => y, x);
                [Verified] public static bool InCode() => Spec.Exists<int>(y => y == 0);
            }
            """);
        Assert.Equal("WRT0002 | lambda", Only(result, "M:C.Lambda(System.Int32)"));
        Assert.Equal("WRT0004 | Spec.Exists outside a theorem statement", Only(result, "M:C.InCode"));
    }
}
