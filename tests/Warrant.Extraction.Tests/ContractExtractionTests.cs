using Warrant.Extraction;
using Warrant.Vir;
using static Warrant.Extraction.Tests.Inline;

namespace Warrant.Extraction.Tests;

/// <summary>
/// M6 U8: extraction reads <c>Spec.Requires</c>, <c>Spec.Ensures</c> and <c>Spec.Assert</c> and <c>[ProofFor]</c> methods
/// (R6, R10, KTD8, KTD16), and reports KTD11's rejections with the construct and callee that caused them.
/// </summary>
public class ContractExtractionTests
{
    private static readonly ParamExpr X = new(VirType.Int32, 0);

    private static ExtractionResult Members(string members, bool checkOverflow = false) =>
        Extract($$"""
            using System;
            public static class C
            {
            {{members}}
            }
            """, checkOverflow);

    private static ExtractionDiagnostic Single(ExtractionResult result, string key) => Assert.Single(result.DiagnosticsFor(key));

    // ---- The leading Spec statements (KTD8) ----

    [Fact]
    public void RequiresEnsuresAndAssertBecomeTheirVirStatements()
    {
        var result = Members("""
                [Verified]
                public static int Clamp(int x)
                {
                    Spec.Requires(x >= 0);
                    Spec.Ensures<int>(r => r >= 0 && r <= x);
                    Spec.Assert(x >= 0, Tactic.VcGen(), Tactic.Omega());
                    return x;
                }
            """);

        Assert.Empty(result.Diagnostics);
        var body = Assert.IsType<BlockStmt>(Unit(result, "M:C.Clamp(System.Int32)").Body);
        var zero = new LitExpr(VirType.Int32, 0);
        var r = new LocalExpr(VirType.Int32, 0);
        Assert.Equal(
            [
                new RequiresStmt(new CompareExpr(CompareOp.Ge, CompareKind.Int, X, zero)),
                new EnsuresStmt(0, "r", new LogicalExpr(
                    LogicalOp.And,
                    new CompareExpr(CompareOp.Ge, CompareKind.Int, r, zero),
                    new CompareExpr(CompareOp.Le, CompareKind.Int, r, X))),
                new AssertStmt(
                    new CompareExpr(CompareOp.Ge, CompareKind.Int, X, zero),
                    new VirList<TacticNode>([new TacticNode("vcgen", VirList<VirTacticArg>.Empty), new TacticNode("omega", VirList<VirTacticArg>.Empty)])),
                new ReturnStmt(X),
            ],
            body.Stmts);
    }

    [Fact]
    public void ADecreasesRequiresEnsuresPrefixIsReadInOrderAndAnAssertMayStandAnywhere()
    {
        var result = Members("""
                [Verified]
                public static int Pick(int x, int y)
                {
                    Spec.Requires(x >= 0);
                    Spec.Requires(y >= 0);
                    Spec.Ensures<int>(r => r >= 0);
                    if (x > y)
                    {
                        Spec.Assert(x > 0);
                        return x;
                    }
                    return y;
                }
            """);

        var body = Assert.IsType<BlockStmt>(Unit(result, "M:C.Pick(System.Int32,System.Int32)").Body);
        Assert.IsType<RequiresStmt>(body.Stmts[0]);
        Assert.IsType<RequiresStmt>(body.Stmts[1]);
        Assert.IsType<EnsuresStmt>(body.Stmts[2]);
        var then = Assert.IsType<BlockStmt>(Assert.IsType<IfStmt>(body.Stmts[3]).Then);
        Assert.Equal(VirList<TacticNode>.Empty, Assert.IsType<AssertStmt>(then.Stmts[0]).Script);
    }

    [Fact]
    public void AnEnsuresAfterAnotherStatementMustLeadTheBody()
    {
        var result = Members("""
                [Verified]
                public static int F(int x)
                {
                    var y = x;
                    Spec.Ensures<int>(r => r == x);
                    return y;
                }
            """);

        var d = Single(result, "M:C.F(System.Int32)");
        Assert.Equal("WRT0002 | Spec.Ensures not leading the body", d.Id + " | " + d.Construct);
        Assert.Contains("must lead the body", d.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ARequiresInsideABranchMustLeadTheBody()
    {
        var result = Members("""
                [Verified]
                public static int F(int x)
                {
                    if (x > 0) { Spec.Requires(x > 1); }
                    return x;
                }
            """);

        Assert.Equal("WRT0002 | Spec.Requires not leading the body", Only(result, "M:C.F(System.Int32)"));
    }

    [Fact]
    public void ARequiresAfterAnEnsuresIsOutOfOrder()
    {
        var result = Members("""
                [Verified]
                public static int F(int x)
                {
                    Spec.Ensures<int>(r => r == x);
                    Spec.Requires(x > 0);
                    return x;
                }
            """);

        var d = Single(result, "M:C.F(System.Int32)");
        Assert.Equal("WRT0002 | Spec.Requires after Spec.Ensures", d.Id + " | " + d.Construct);
        Assert.Contains("out of order", d.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ARequiresBeforeADecreasesIsOutOfOrder()
    {
        var result = Members("""
                [Verified]
                public static int Down(int n)
                {
                    Spec.Requires(n >= 0);
                    Spec.Decreases(n);
                    return n <= 0 ? 0 : Down(n - 1);
                }
            """);

        var d = Single(result, "M:C.Down(System.Int32)");
        Assert.Equal("WRT0002 | Spec.Decreases not first", d.Id + " | " + d.Construct);
        Assert.Contains("out of order", d.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void AContractOnARecursiveMethodIsRejected()
    {
        var result = Members("""
                [Verified]
                public static int Down(int n)
                {
                    Spec.Decreases(n);
                    Spec.Requires(n >= 0);
                    return n <= 0 ? 0 : Down(n - 1);
                }

                [Verified]
                public static int Up(int n)
                {
                    Spec.Decreases(n);
                    Spec.Ensures<int>(r => r >= 0);
                    return n <= 0 ? 0 : Up(n - 1);
                }
            """);

        Assert.Equal("WRT0002 | contract on a recursive method", Only(result, "M:C.Down(System.Int32)"));
        Assert.Equal("WRT0002 | contract on a recursive method", Only(result, "M:C.Up(System.Int32)"));
    }

    [Fact]
    public void EnsuresOfAnotherTypeThanTheReturnTypeIsRejectedNamingTheReturnType()
    {
        var result = Members("""
                [Verified]
                public static int F(int x)
                {
                    Spec.Ensures<long>(r => r >= 0);
                    return x;
                }
            """);

        var d = Single(result, "M:C.F(System.Int32)");
        Assert.Equal("WRT0002 | Spec.Ensures type argument that is not the return type", d.Id + " | " + d.Construct);
        Assert.Contains("Spec.Ensures<int>", d.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void EnsuresWithoutTheResultOnAMethodThatReturnsAValueIsRejectedNamingTheReturnType()
    {
        var result = Members("""
                [Verified]
                public static int F(int x)
                {
                    Spec.Ensures(() => x >= 0);
                    return x;
                }
            """);

        var d = Single(result, "M:C.F(System.Int32)");
        Assert.Equal("WRT0002 | Spec.Ensures without the result", d.Id + " | " + d.Construct);
        Assert.Contains("Spec.Ensures<int>", d.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void EnsuresOfANullableReferenceMustKeepTheAnnotation()
    {
        var result = Extract("""
            #nullable enable
            public sealed record Payment(int Id);
            public static class C
            {
                [Verified]
                public static Payment? Find(Payment? p)
                {
                    Spec.Ensures<Payment?>(r => r is null || r.Id == r.Id);
                    return p;
                }

                [Verified]
                public static Payment? Lost(Payment? p)
                {
                    Spec.Ensures<Payment>(r => r.Id > 0);
                    return p;
                }
            }
            """);

        Assert.NotNull(result.Find("M:C.Find(Payment)"));
        var d = Single(result, "M:C.Lost(Payment)");
        Assert.Equal("Spec.Ensures type argument that is not the return type", d.Construct);
        Assert.Equal("Spec.Ensures<Payment> does not match the method's result, Payment?: write Spec.Ensures<Payment?>(r => ...).", d.Message);
    }

    [Fact]
    public void AnEnsuresConditionThatIsNotALambdaIsMalformed()
    {
        var result = Members("""
                static bool Positive(int r) => r > 0;

                [Verified]
                public static int F(int x)
                {
                    Spec.Ensures<int>(Positive);
                    return x;
                }
            """);

        Assert.Equal("WRT0004 | Spec.Ensures whose condition is not a lambda", Only(result, "M:C.F(System.Int32)"));
    }

    // ---- KTD11: raise-ability ----

    [Fact]
    public void AnEnsuresThatCallsAMethodWhichDividesByAVariableIsRejectedNamingItAndItsDivision()
    {
        var result = Members("""
                [Verified] public static int Scale(int x, int d) => x / d;

                [Verified]
                public static int F(int x, int d)
                {
                    Spec.Ensures<int>(r => r == Scale(x, d));
                    return x / d;
                }
            """);

        var d = Single(result, "M:C.F(System.Int32,System.Int32)");
        Assert.Equal("WRT0002 | Spec expression calling a raising method", d.Id + " | " + d.Construct);
        Assert.Contains("Scale", d.Message, StringComparison.Ordinal);
        Assert.Contains("division", d.Message, StringComparison.Ordinal);
        Assert.NotNull(result.Find("M:C.Scale(System.Int32,System.Int32)"));
    }

    [Fact]
    public void ASpecExpressionMayCallAPureMethodThatHasARequires()
    {
        var result = Members("""
                [Verified]
                public static int Half(int x)
                {
                    Spec.Requires(x >= 0);
                    return x / 2;
                }

                [Verified]
                public static int F(int x)
                {
                    Spec.Requires(x >= 0 && Half(x) <= x);
                    Spec.Ensures<int>(r => r == Half(x));
                    return x;
                }
            """);

        Assert.Empty(result.Diagnostics);
        Assert.NotNull(result.Find("M:C.F(System.Int32)"));
    }

    [Fact]
    public void ATheoremAboutAMethodThatCallsAThrowingMethodIsRejectedNamingTheThrow()
    {
        var result = Members("""
                [Verified] public static int B(int x) => x >= 0 ? x : throw new ArgumentException();
                [Verified] public static int A(int x) => B(x) + 1;
                [Theorem] static Proof AIsPositive(int x) => Prove.That(A(x) > 0);
            """);

        var d = Single(result, "M:C.AIsPositive(System.Int32)");
        Assert.Equal("WRT0002 | theorem calling a raising method", d.Id + " | " + d.Construct);
        Assert.Contains("C.A(int)", d.Message, StringComparison.Ordinal);
        Assert.Contains("throw in C.B(int)", d.Message, StringComparison.Ordinal);
        Assert.Contains("Spec.Ensures", d.Message, StringComparison.Ordinal);
        Assert.NotNull(result.Find("M:C.A(System.Int32)"));
    }

    [Fact]
    public void ATheoremWhoseStatementDividesByAVariableIsRejectedNamingTheDivision()
    {
        var result = Members("""
                [Theorem] static Proof T(int a, int b) => Prove.That(Spec.Implies(a >= 0 && b > 0, a / b * b <= a));
            """);

        var d = Single(result, "M:C.T(System.Int32,System.Int32)");
        Assert.Equal("WRT0002 | division", d.Id + " | " + d.Construct);
        Assert.Contains("Spec.Ensures", d.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ATheoremWithAdditionInACheckedProjectIsRejectedAsCheckedArithmetic()
    {
        var result = Members("""
                [Theorem] static Proof T(int a) => Prove.That(Spec.Implies(a >= 0 && a < 100, a + 1 > a));
            """, checkOverflow: true);

        Assert.Equal("WRT0002 | checked arithmetic", Only(result, "M:C.T(System.Int32)"));
    }

    /// <summary>
    /// U8's scenario: <c>a / 2</c> and <c>a % 2</c> in a theorem statement cannot raise (KTD11), so the statement is
    /// accepted, and M6 U9 translates them as Lean's <c>/</c> and <c>%</c>.
    /// </summary>
    [Fact]
    public void ATheoremDividingByAConstantIsAccepted()
    {
        var result = Members("""
                [Theorem] static Proof T(int a) => Prove.That(Spec.Implies(a >= 0, a / 2 <= a));
                [Theorem] static Proof U(long a) => Prove.That(Spec.Implies(a >= 0, a % 2 < 2));
            """);

        Assert.Empty(result.Diagnostics);
        Assert.Contains(VirTree.PreOrder(result.Find("M:C.T(System.Int32)")!.Unit), n => n is BinaryExpr { Op: BinaryOp.Div });
        Assert.Contains(VirTree.PreOrder(result.Find("M:C.U(System.Int64)")!.Unit), n => n is BinaryExpr { Op: BinaryOp.Rem });
    }

    [Fact]
    public void ARecursiveMethodThatCanRaiseIsRejectedAsRecursionWithEffects()
    {
        var result = Members("""
                [Verified]
                public static int Down(int n)
                {
                    Spec.Decreases(n);
                    if (n < 0) throw new ArgumentException();
                    return n == 0 ? 0 : Down(n - 1);
                }

                [Verified]
                public static int Steps(int n, int d)
                {
                    Spec.Decreases(n / d);
                    return n <= 0 ? 0 : Steps(n - d, d);
                }
            """);

        var down = Single(result, "M:C.Down(System.Int32)");
        Assert.Equal("WRT0002 | recursion with effects", down.Id + " | " + down.Construct);
        Assert.Contains("throw", down.Message, StringComparison.Ordinal);
        var steps = Single(result, "M:C.Steps(System.Int32,System.Int32)");
        Assert.Equal("recursion with effects", steps.Construct);
        Assert.Contains("division", steps.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ACallToAMethodWithARequiresMakesTheCallerRaisingButKeepsATheoremAboutItPure()
    {
        var result = Members("""
                [Verified]
                public static int Half(int x)
                {
                    Spec.Requires(x >= 0);
                    return x / 2;
                }

                [Verified] public static int Quarter(int x) => Half(Half(x));
                [Theorem] static Proof HalfOfZero() => Prove.That(Half(0) == 0);
            """);

        Assert.Empty(result.Diagnostics);
        var analysis = Effects.Analyze(result.Units.Select(u => u.Unit));
        Assert.Equal("call to a method with Spec.Requires", analysis.CauseOf("M:C.Quarter(System.Int32)")?.Construct);
        Assert.False(analysis.IsRaising("M:C.HalfOfZero"));
    }

    // ---- [ProofFor] (KTD16) ----

    [Fact]
    public void AProofForScriptBecomesTheMethodsScript()
    {
        var result = Members("""
                [Verified]
                public static int Id(int x)
                {
                    Spec.Ensures<int>(r => r == x);
                    return x;
                }

                [ProofFor(nameof(Id))]
                static Proof IdProof() => Prove.Contract().By(Tactic.VcGen(), Tactic.Unfold(nameof(Id)), Tactic.Omega());
            """);

        Assert.Empty(result.Diagnostics);
        var script = Unit(result, "M:C.Id(System.Int32)").Script;
        Assert.NotNull(script);
        Assert.Equal(["vcgen", "unfold", "omega"], script.Select(t => t.Name));
        Assert.Equal(new UnitRefArg("M:C.Id(System.Int32)"), Assert.Single(script[1].Args));
        Assert.Equal(["M:C.Id(System.Int32)"], result.Units.Select(u => u.Key));
    }

    [Fact]
    public void AProofForNamingNoMethodIsRejectedNamingIt()
    {
        var result = Members("""
                [ProofFor("Missing")]
                static Proof MissingProof() => Prove.Contract().By(Tactic.Omega());
            """);

        var d = Single(result, "M:C.MissingProof");
        Assert.Equal("WRT0002 | [ProofFor] naming no method", d.Id + " | " + d.Construct);
        Assert.Contains("Missing", d.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("static Proof P() => Prove.Contract();")]
    [InlineData("static Proof P() => Prove.That(Id(1) == 1);")]
    [InlineData("static Proof P() { var p = Prove.Contract(); return p.By(Tactic.Omega()); }")]
    public void AProofForWhoseBodyIsNotProveContractByIsRejected(string method)
    {
        var result = Members($$"""
                [Verified] public static int Id(int x) { Spec.Ensures<int>(r => r == x); return x; }

                [ProofFor(nameof(Id))]
                {{method}}
            """);

        Assert.Equal("WRT0002 | [ProofFor] body that is not Prove.Contract().By(...)", Only(result, "M:C.P"));
        Assert.Null(Unit(result, "M:C.Id(System.Int32)").Script);
    }

    [Theory]
    [InlineData("Proof P() => Prove.Contract().By(Tactic.Omega());", "M:D.P")]
    [InlineData("static Proof P(int x) => Prove.Contract().By(Tactic.Omega());", "M:D.P(System.Int32)")]
    [InlineData("static Proof P<T>() => Prove.Contract().By(Tactic.Omega());", "M:D.P``1")]
    public void AProofForMethodMustBeStaticParameterlessAndNotGeneric(string method, string key)
    {
        var result = Extract($$"""
            public sealed class D
            {
                [Verified] public static int Id(int x) { Spec.Ensures<int>(r => r == x); return x; }

                [ProofFor(nameof(Id))]
                {{method}}
            }
            """);

        Assert.Equal("WRT0002 | [ProofFor] method that is not static and parameterless", Only(result, key));
        Assert.Null(Unit(result, "M:D.Id(System.Int32)").Script);
    }

    [Fact]
    public void ASecondProofForTheSameMethodIsRejectedNamingTheFirst()
    {
        var result = Members("""
                [Verified] public static int Id(int x) { Spec.Ensures<int>(r => r == x); return x; }

                [ProofFor(nameof(Id))]
                static Proof First() => Prove.Contract().By(Tactic.Omega());

                [ProofFor(nameof(Id))]
                static Proof Second() => Prove.Contract().By(Tactic.Simp());
            """);

        var d = Single(result, "M:C.Second");
        Assert.Equal("WRT0002 | second [ProofFor] for a method", d.Id + " | " + d.Construct);
        Assert.Contains("C.First()", d.Message, StringComparison.Ordinal);
        Assert.Empty(result.DiagnosticsFor("M:C.First"));
        Assert.Equal(["omega"], Unit(result, "M:C.Id(System.Int32)").Script!.Select(t => t.Name));
    }

    [Fact]
    public void AProofForAnOverloadedMethodIsRejected()
    {
        var result = Members("""
                [Verified] public static int Id(int x) => x;
                [Verified] public static long Id(long x) => x;

                [ProofFor(nameof(Id))]
                static Proof IdProof() => Prove.Contract().By(Tactic.Omega());
            """);

        var d = Single(result, "M:C.IdProof");
        Assert.Equal("WRT0002 | [ProofFor] of an overloaded method", d.Id + " | " + d.Construct);
        Assert.Contains("Id", d.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void AProofForAMethodThatIsNotVerifiedIsRejected()
    {
        var result = Members("""
                public static int Id(int x) => x;

                [ProofFor(nameof(Id))]
                static Proof IdProof() => Prove.Contract().By(Tactic.Omega());
            """);

        Assert.Equal("WRT0002 | [ProofFor] of a member that is not verified", Only(result, "M:C.IdProof"));
    }

    [Fact]
    public void AMalformedProofForScriptRejectsTheMethodItProves()
    {
        var result = Members("""
                [Verified] public static int Id(int x) { Spec.Ensures<int>(r => r == x); return x; }

                [ProofFor(nameof(Id))]
                static Proof IdProof() => Prove.Contract().By(Tactic.Simp("h"));
            """);

        Assert.Equal("WRT0004 | string literal where a lemma is expected", Only(result, "M:C.Id(System.Int32)"));
    }

    [Fact]
    public void VcGenIsStillNotATacticOfATheoremScript()
    {
        var result = Members("""
                [Verified] public static int Id(int x) => x;
                [Theorem] static Proof T(int x) => Prove.That(Id(x) == x).By(Tactic.VcGen());
            """);

        Assert.Equal("WRT0004 | unsupported script argument", Only(result, "M:C.T(System.Int32)"));
    }

    [Fact]
    public void AWellShapedContractClassThatNoVerifiedMethodUsesGivesNoUnitAndNoDiagnostic()
    {
        var result = Extract("""
            public interface IStore { int Get(int id); }

            [ContractFor(typeof(IStore))]
            internal abstract class StoreContract : IStore
            {
                public int Get(int id) { Spec.Requires(id > 0); Spec.Ensures<int>(r => r >= 0); return default!; }
            }

            public static class C
            {
                [Verified] public static int Id(int x) => x;
            }
            """);

        Assert.Empty(result.Diagnostics);
        Assert.Equal(["M:C.Id(System.Int32)"], result.Units.Select(u => u.Key));
    }
}
