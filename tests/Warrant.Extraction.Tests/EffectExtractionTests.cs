using Warrant.Extraction;
using Warrant.Vir;
using static Warrant.Extraction.Tests.Inline;

namespace Warrant.Extraction.Tests;

/// <summary>
/// M6 U7: extraction accepts <c>throw</c>, checked arithmetic and narrowing, <c>/</c>, <c>%</c> and the modelled
/// <c>Math</c> members on <c>int</c> and <c>long</c> in verified code (R1, R4, KTD6, KTD23), keeps them out of theorem
/// statements (KTD11), and still rejects the rest with a named construct.
/// </summary>
public class EffectExtractionTests
{
    private static readonly ParamExpr A = new(VirType.Int32, 0);
    private static readonly ParamExpr B = new(VirType.Int32, 1);

    private static VirNode? Body(string member, string key, bool checkOverflow = false) =>
        Unit(Extract($$"""
            using System;
            public static class C
            {
                {{member}}
            }
            """, checkOverflow), key).Body;

    [Fact]
    public void CheckedAdditionIsACheckedBinaryNode()
    {
        Assert.Equal(
            new BinaryExpr(VirType.Int32, BinaryOp.Add, VirOverflow.Checked, A, B),
            Body("[Verified] public static int F(int a, int b) => checked(a + b);", "M:C.F(System.Int32,System.Int32)"));
    }

    [Fact]
    public void CheckedNegationAndMultiplicationAreCheckedNodes()
    {
        Assert.Equal(
            new UnaryExpr(VirType.Int32, UnaryOp.Neg, VirOverflow.Checked, A),
            Body("[Verified] public static int F(int a) => checked(-a);", "M:C.F(System.Int32)"));
        Assert.Equal(
            new BinaryExpr(VirType.Int64, BinaryOp.Mul, VirOverflow.Checked, new ParamExpr(VirType.Int64, 0), new ParamExpr(VirType.Int64, 1)),
            Body("[Verified] public static long F(long a, long b) => checked(a * b);", "M:C.F(System.Int64,System.Int64)"));
    }

    [Fact]
    public void CheckedNarrowingIsACheckedConversion()
    {
        Assert.Equal(
            new ConvertExpr(VirType.Int64, VirType.Int32, VirOverflow.Checked, new ParamExpr(VirType.Int64, 0)),
            Body("[Verified] public static int F(long l) => checked((int)l);", "M:C.F(System.Int64)"));
    }

    [Fact]
    public void DivisionAndRemainderAreBinaryNodes()
    {
        Assert.Equal(
            new BinaryExpr(VirType.Int32, BinaryOp.Div, VirOverflow.Wrap, A, B),
            Body("[Verified] public static int F(int a, int b) => a / b;", "M:C.F(System.Int32,System.Int32)"));
        Assert.Equal(
            new BinaryExpr(VirType.Int32, BinaryOp.Rem, VirOverflow.Wrap, A, B),
            Body("[Verified] public static int F(int a, int b) => a % b;", "M:C.F(System.Int32,System.Int32)"));
        Assert.Equal(
            new BinaryExpr(VirType.Int64, BinaryOp.Div, VirOverflow.Wrap, new ParamExpr(VirType.Int64, 0), new LitExpr(VirType.Int64, 3)),
            Body("[Verified] public static long F(long a) => a / 3;", "M:C.F(System.Int64)"));
    }

    [Fact]
    public void DivisionInACheckedContextHasOneMeaning()
    {
        // `/` throws on a zero divisor and on MinValue / -1 whatever the context (KTD6), so its node is the same.
        Assert.Equal(
            new BinaryExpr(VirType.Int32, BinaryOp.Div, VirOverflow.Wrap, A, B),
            Body("[Verified] public static int F(int a, int b) => checked(a / b);", "M:C.F(System.Int32,System.Int32)"));
    }

    [Fact]
    public void CompoundDivisionAssignsADivision()
    {
        var body = Assert.IsType<BlockStmt>(Body("""
            [Verified]
            public static int F(int a, int b)
            {
                var x = a;
                x /= b;
                x %= 7;
                return x;
            }
            """, "M:C.F(System.Int32,System.Int32)"));
        var div = Assert.IsType<AssignStmt>(body.Stmts[1]);
        Assert.Equal(new BinaryExpr(VirType.Int32, BinaryOp.Div, VirOverflow.Wrap, new LocalExpr(VirType.Int32, 0), B), div.Value);
        var rem = Assert.IsType<AssignStmt>(body.Stmts[2]);
        Assert.Equal(BinaryOp.Rem, Assert.IsType<BinaryExpr>(rem.Value).Op);
    }

    [Fact]
    public void AThrowStatementIsAThrowNodeNamingTheType()
    {
        var body = Assert.IsType<BlockStmt>(Body("""
            [Verified]
            public static int F(int a)
            {
                if (a < 0)
                {
                    throw new ArgumentException("x");
                }
                return a;
            }
            """, "M:C.F(System.Int32)"));
        var @if = Assert.IsType<IfStmt>(body.Stmts[0]);
        Assert.Equal(new ThrowStmt("T:System.ArgumentException"), Assert.Single(Assert.IsType<BlockStmt>(@if.Then).Stmts));
    }

    [Fact]
    public void AThrowStatementEndsItsBlock()
    {
        var result = Extract("""
            using System;
            public static class C
            {
                [Verified]
                public static int F(int a)
                {
                    if (a < 0) throw new ArgumentException("negative", nameof(a));
                    else throw new InvalidOperationException();
                }
            }
            """);
        var body = Assert.IsType<BlockStmt>(Unit(result, "M:C.F(System.Int32)").Body);
        var @if = Assert.IsType<IfStmt>(Assert.Single(body.Stmts));
        Assert.Equal(new ThrowStmt("T:System.InvalidOperationException"), Assert.Single(Assert.IsType<BlockStmt>(@if.Else).Stmts));
    }

    [Fact]
    public void AThrowExpressionHasTheTypeItsContextExpects()
    {
        Assert.Equal(
            new CondExpr(
                VirType.Int32,
                new CompareExpr(CompareOp.Ge, CompareKind.Int, A, LitExpr.Int32(0)),
                A,
                new ThrowExpr(VirType.Int32, "T:System.ArgumentOutOfRangeException")),
            Body("[Verified] public static int F(int a) => a >= 0 ? a : throw new ArgumentOutOfRangeException(nameof(a), a, \"negative\");", "M:C.F(System.Int32)"));
    }

    [Fact]
    public void AnExpressionBodyThatOnlyThrowsIsAThrowExpression()
    {
        Assert.Equal(
            new ThrowExpr(VirType.Int32, "T:System.NotSupportedException"),
            Body("[Verified] public static int F(int a) => throw new NotSupportedException();", "M:C.F(System.Int32)"));
    }

    [Fact]
    public void AUserExceptionThatOnlyChainsToASystemExceptionMayBeThrown()
    {
        var result = Extract("""
            using System;
            public sealed class RejectedPayment : Exception
            {
                public RejectedPayment(string message) : base(message) { }
            }
            public static class C
            {
                [Verified] public static int F(int a) => a > 0 ? a : throw new RejectedPayment("not positive");
            }
            """);
        var body = Assert.IsType<CondExpr>(Unit(result, "M:C.F(System.Int32)").Body);
        Assert.Equal(new ThrowExpr(VirType.Int32, "T:RejectedPayment"), body.Else);
    }

    [Fact]
    public void AUserExceptionWhoseConstructorDividesIsRejectedNamingTheType()
    {
        var result = Extract("""
            using System;
            public sealed class Odd : Exception
            {
                public Odd(int x) : base("odd") { Code = 100 / x; }
                public int Code { get; }
            }
            public static class C
            {
                [Verified] public static int F(int x) => x != 0 ? x : throw new Odd(x);
            }
            """);
        var d = Assert.Single(result.DiagnosticsFor("M:C.F(System.Int32)"));
        Assert.Equal(("WRT0002", "exception type that is not a System exception or a plain subclass of one"), (d.Id, d.Construct));
        Assert.Contains("Odd", d.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("public Odd(int x) : base(\"odd\" + x) { }", "chains with an argument that is not a parameter or constant")]
    [InlineData("public Odd(int x) : base(\"odd\") { }\n    private readonly int _code = 1 / 1;", "has a field initializer")]
    [InlineData("public Odd(int x) : this() { }\n    public Odd() : base(\"odd\") { }", "chains to its own constructor")]
    public void AUserExceptionWithAnyOtherConstructionIsRejected(string members, string why)
    {
        var result = Extract($$"""
            using System;
            public sealed class Odd : Exception
            {
                {{members}}
            }
            public static class C
            {
                [Verified] public static int F(int x) => x != 0 ? x : throw new Odd(x);
            }
            """);
        Assert.True(
            Only(result, "M:C.F(System.Int32)") == "WRT0002 | exception type that is not a System exception or a plain subclass of one",
            why);
    }

    [Theory]
    [InlineData("throw new ArgumentException(Twice(a).ToString());", "exception argument that is not a constant or a parameter")]
    [InlineData("throw a > -10 ? new ArgumentException() : new InvalidOperationException();", "throw of a value other than a new exception")]
    public void AThrowWhoseExceptionIsNotBuiltFromConstantsAndParametersIsRejected(string statement, string construct)
    {
        var result = Extract($$"""
            using System;
            public static class C
            {
                [Verified] public static int Twice(int a) => a + a;
                [Verified]
                public static int F(int a)
                {
                    if (a < 0)
                    {
                        {{statement}}
                    }
                    return a;
                }
            }
            """);
        Assert.Equal("WRT0002 | " + construct, Only(result, "M:C.F(System.Int32)"));
    }

    [Fact]
    public void TheModelledMathMembersAreModelledCalls()
    {
        Assert.Equal(
            new ModelledCallExpr(VirType.Int32, "M:System.Math.Max(System.Int32,System.Int32)", VirList.Of<VirExpr>(A, B)),
            Body("[Verified] public static int F(int a, int b) => Math.Max(a, b);", "M:C.F(System.Int32,System.Int32)"));
        Assert.Equal(
            new ModelledCallExpr(VirType.Int32, "M:System.Math.Min(System.Int32,System.Int32)", VirList.Of<VirExpr>(A, LitExpr.Int32(100))),
            Body("[Verified] public static int F(int a, int b) => Math.Min(a, 100);", "M:C.F(System.Int32,System.Int32)"));
        Assert.Equal(
            new ModelledCallExpr(VirType.Int64, "M:System.Math.Abs(System.Int64)", VirList.Of<VirExpr>(new ParamExpr(VirType.Int64, 0))),
            Body("[Verified] public static long F(long a) => Math.Abs(a);", "M:C.F(System.Int64)"));
    }

    [Fact]
    public void TheModelledMembersAreMinMaxAndAbsOnIntLongAndDecimalAndTheThrowingOnesAreTheVirs()
    {
        Assert.Equal(
            [
                "M:System.Math.Abs(System.Decimal)", "M:System.Math.Abs(System.Int32)", "M:System.Math.Abs(System.Int64)",
                "M:System.Math.Max(System.Decimal,System.Decimal)", "M:System.Math.Max(System.Int32,System.Int32)", "M:System.Math.Max(System.Int64,System.Int64)",
                "M:System.Math.Min(System.Decimal,System.Decimal)", "M:System.Math.Min(System.Int32,System.Int32)", "M:System.Math.Min(System.Int64,System.Int64)",
            ],
            ModelledMembers.Keys.Order(StringComparer.Ordinal));
        Assert.Subset(ModelledMembers.Keys.ToHashSet(StringComparer.Ordinal), Effects.ThrowingModelledMembers.ToHashSet(StringComparer.Ordinal));
    }

    [Theory]
    [InlineData("Math.Round(1.5)", "WRT0005 | M:System.Math.Round(System.Double)")]
    [InlineData("Math.Clamp(a, 0, 10)", "WRT0005 | M:System.Math.Clamp(System.Int32,System.Int32,System.Int32)")]
    [InlineData("Math.Sign(a)", "WRT0005 | M:System.Math.Sign(System.Int32)")]
    public void OtherMathMembersAreStillNotModelled(string call, string expected)
    {
        var result = Extract($$"""
            using System;
            public static class C
            {
                [Verified] public static int F(int a) { {{call}}; return a; }
            }
            """);
        Assert.Equal(expected, Only(result, "M:C.F(System.Int32)"));
    }

    [Theory]
    [InlineData("try { return a; } catch (InvalidOperationException) { return 0; }", "try")]
    [InlineData("try { return a; } finally { }", "try")]
    [InlineData("try { return a; } catch (InvalidOperationException) { throw; }", "try")]
    public void TryCatchFinallyAndRethrowAreStillRejected(string body, string construct)
    {
        var result = Extract($$"""
            using System;
            public static class C
            {
                [Verified] public static int F(int a) { {{body}} }
            }
            """);
        Assert.Equal("WRT0002 | " + construct, Only(result, "M:C.F(System.Int32)"));
    }

    [Fact]
    public void ACheckedProjectsArithmeticIsChecked()
    {
        var result = Extract("""
            public static class C
            {
                [Verified] public static int Add(int a, int b) => a + b;
                [Verified] public static long Widen(int a) => a;
                [Verified]
                public static int Next(int a)
                {
                    var x = a;
                    x++;
                    return x;
                }
            }
            """, checkOverflow: true);
        Assert.Equal(new BinaryExpr(VirType.Int32, BinaryOp.Add, VirOverflow.Checked, A, B), Unit(result, "M:C.Add(System.Int32,System.Int32)").Body);
        Assert.Equal(new ConvertExpr(VirType.Int32, VirType.Int64, VirOverflow.Wrap, A), Unit(result, "M:C.Widen(System.Int32)").Body);
        var next = Assert.IsType<BlockStmt>(Unit(result, "M:C.Next(System.Int32)").Body);
        var increment = Assert.IsType<AssignStmt>(next.Stmts[1]);
        Assert.Equal(VirOverflow.Checked, Assert.IsType<BinaryExpr>(increment.Value).Overflow);
    }

    /// <summary>
    /// The one rule for C# arithmetic (#183, #236, #244): explicit <c>unchecked</c> wraps on purpose, so its node is
    /// <c>unchecked</c>, apart from the implicit default, <c>wrap</c>, which must not overflow.
    /// </summary>
    [Fact]
    public void ExplicitUncheckedArithmeticIsUncheckedNotTheDefault()
    {
        Assert.Equal(
            new BinaryExpr(VirType.Int32, BinaryOp.Add, VirOverflow.Unchecked, A, B),
            Body("[Verified] public static int F(int a, int b) => unchecked(a + b);", "M:C.F(System.Int32,System.Int32)"));
        Assert.Equal(
            new BinaryExpr(VirType.Int32, BinaryOp.Add, VirOverflow.Wrap, A, B),
            Body("[Verified] public static int F(int a, int b) => a + b;", "M:C.F(System.Int32,System.Int32)"));
        Assert.Equal(
            new UnaryExpr(VirType.Int64, UnaryOp.Neg, VirOverflow.Unchecked, new ParamExpr(VirType.Int64, 0)),
            Body("[Verified] public static long F(long a) => unchecked(-a);", "M:C.F(System.Int64)"));
        Assert.Equal(
            new ConvertExpr(VirType.Int64, VirType.Int32, VirOverflow.Unchecked, new ParamExpr(VirType.Int64, 0)),
            Body("[Verified] public static int F(long l) => unchecked((int)l);", "M:C.F(System.Int64)"));
        // `/` throws whatever the context (KTD6): its node keeps one meaning.
        Assert.Equal(
            new BinaryExpr(VirType.Int32, BinaryOp.Div, VirOverflow.Wrap, A, B),
            Body("[Verified] public static int F(int a, int b) => unchecked(a / b);", "M:C.F(System.Int32,System.Int32)"));
    }

    [Fact]
    public void TheNearestCheckedOrUncheckedDecides()
    {
        // unchecked inside checked wraps; checked inside unchecked raises; a checked project's unchecked block wraps.
        Assert.Equal(
            new BinaryExpr(VirType.Int32, BinaryOp.Mul, VirOverflow.Unchecked, A, B),
            Body("[Verified] public static int F(int a, int b) => checked(unchecked(a * b));", "M:C.F(System.Int32,System.Int32)"));
        Assert.Equal(
            new BinaryExpr(VirType.Int32, BinaryOp.Mul, VirOverflow.Checked, A, B),
            Body("[Verified] public static int F(int a, int b) => unchecked(checked(a * b));", "M:C.F(System.Int32,System.Int32)"));
        Assert.Equal(
            new BinaryExpr(VirType.Int32, BinaryOp.Sub, VirOverflow.Unchecked, A, B),
            Body("[Verified] public static int F(int a, int b) => unchecked(a - b);", "M:C.F(System.Int32,System.Int32)", checkOverflow: true));
        var block = Assert.IsType<BlockStmt>(Body("""
            [Verified]
            public static int F(int a, int b)
            {
                var x = a;
                unchecked
                {
                    x += b;
                    x++;
                }
                return x;
            }
            """, "M:C.F(System.Int32,System.Int32)", checkOverflow: true));
        var inner = Assert.IsType<BlockStmt>(block.Stmts[1]);
        Assert.All(inner.Stmts, s => Assert.Equal(VirOverflow.Unchecked, Assert.IsType<BinaryExpr>(Assert.IsType<AssignStmt>(s).Value).Overflow));
    }

    [Theory]
    [InlineData("x / x <= 1", "division")]
    [InlineData("x % -1 == 0", "remainder")]
    [InlineData("checked(x + 1) > x", "checked arithmetic")]
    [InlineData("checked(-x) != x", "checked arithmetic")]
    [InlineData("checked((int)l) == l", "checked narrowing")]
    [InlineData("(x > 0 ? x : throw new ArgumentException()) > 0", "throw")]
    [InlineData("Math.Abs(x) >= 0", "modelled member M:System.Math.Abs(System.Int32)")]
    public void ARaisingOperationInATheoremStatementIsStillRejected(string claim, string construct)
    {
        var result = Extract($$"""
            using System;
            public static class C
            {
                [Theorem] static Proof T(int x, long l) => Prove.That({{claim}});
            }
            """);
        Assert.Equal("WRT0002 | " + construct, Only(result, "M:C.T(System.Int32,System.Int64)"));
    }

    [Fact]
    public void ANonThrowingModelledMemberMayAppearInATheoremStatement()
    {
        var result = Extract("""
            using System;
            public static class C
            {
                [Theorem] static Proof T(int x) => Prove.That(Math.Max(x, 0) >= 0);
            }
            """);
        var statement = Assert.IsType<CompareExpr>(Unit(result, "M:C.T(System.Int32)").Statement);
        Assert.Equal("M:System.Math.Max(System.Int32,System.Int32)", Assert.IsType<ModelledCallExpr>(statement.L).Member);
    }

    [Fact]
    public void EffectInferenceSeesTheExtractedRaisingConstructs()
    {
        var result = Extract("""
            using System;
            public static class C
            {
                [Verified] public static int Halve(int x) => x / 2;
                [Verified] public static int Ratio(int a, int b) => a / b;
                [Verified] public static int Guard(int a) => a >= 0 ? a : throw new ArgumentException();
                [Verified] public static int Biggest(int a, int b) => Math.Max(a, b);
                [Verified] public static int Size(int a) => Math.Abs(a);
            }
            """);
        var analysis = Effects.Analyze(result.Units.Select(u => u.Unit));
        Assert.False(analysis.IsRaising("M:C.Halve(System.Int32)"));
        Assert.Equal("division", analysis.CauseOf("M:C.Ratio(System.Int32,System.Int32)")?.Construct);
        Assert.Equal("throw", analysis.CauseOf("M:C.Guard(System.Int32)")?.Construct);
        Assert.False(analysis.IsRaising("M:C.Biggest(System.Int32,System.Int32)"));
        Assert.Equal("modelled member M:System.Math.Abs(System.Int32)", analysis.CauseOf("M:C.Size(System.Int32)")?.Construct);
    }
}
