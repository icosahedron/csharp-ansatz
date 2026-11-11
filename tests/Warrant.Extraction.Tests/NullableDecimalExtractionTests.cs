using Warrant.Extraction;
using Warrant.Vir;
using static Warrant.Extraction.Tests.Inline;

namespace Warrant.Extraction.Tests;

/// <summary>
/// M6 U17: extraction accepts <c>int?</c>, <c>long?</c>, nullable references to records and closed classes, and
/// <c>decimal</c> (R2, R3, KTD5, KTD7); a nullable value used where a non-nullable one is required becomes a non-null unwrap
/// whatever Roslyn's flow state says (#163); and lifted operators, <c>!</c> and raising reads in theorem statements are
/// rejected with their names.
/// </summary>
public class NullableDecimalExtractionTests
{
    private const string PaymentKey = "T:Payment";
    private static readonly RefType Payment = VirType.Ref(PaymentKey);
    private static readonly NullableType MaybePayment = VirType.Nullable(Payment);
    private static readonly NullableType MaybeInt = VirType.Nullable(VirType.Int32);
    private static readonly ParamExpr X = new(MaybeInt, 0);

    private static ExtractionResult Extract(string members) => Inline.Extract($$"""
        using System;
        public sealed record Payment(int Id, decimal Amount);
        public static class C
        {
            [Verified] public static int Use(Payment p) => p.Id;
            {{members}}
        }
        """);

    private static VirNode? Body(string member, string key) => Unit(Extract(member), key).Body;

    [Fact]
    public void ANullableRecordParameterAndIsNullExtract()
    {
        var result = Extract("[Verified] public static bool Missing(Payment? payment) => payment is null;");
        var unit = Unit(result, "M:C.Missing(Payment)");
        Assert.Equal(new VirParam("payment", MaybePayment), Assert.Single(unit.Params!));
        Assert.Equal(new IsNullExpr(new ParamExpr(MaybePayment, 0)), unit.Body);

        // A nullable parameter can be null, so nothing assumes it is not.
        Assert.Empty(NonNull(unit));
    }

    [Fact]
    public void TheNullTestsAreIsNullAndItsNegation()
    {
        var p = new ParamExpr(MaybePayment, 0);
        Assert.Equal(new NotExpr(new IsNullExpr(p)), Body("[Verified] public static bool F(Payment? p) => p is not null;", "M:C.F(Payment)"));
        Assert.Equal(new IsNullExpr(p), Body("[Verified] public static bool F(Payment? p) => p == null;", "M:C.F(Payment)"));
        Assert.Equal(new NotExpr(new IsNullExpr(p)), Body("[Verified] public static bool F(Payment? p) => null != p;", "M:C.F(Payment)"));
        Assert.Equal(new IsNullExpr(X), Body("[Verified] public static bool F(int? x) => x == null;", "M:C.F(System.Nullable{System.Int32})"));
        Assert.Equal(new NotExpr(new IsNullExpr(X)), Body("[Verified] public static bool F(int? x) => x.HasValue;", "M:C.F(System.Nullable{System.Int32})"));
    }

    [Fact]
    public void NullIsANullLiteralOfTheNullableType()
    {
        Assert.Equal(new NullExpr(MaybePayment), Body("[Verified] public static Payment? F() => null;", "M:C.F"));
        Assert.Equal(new NullExpr(MaybeInt), Body("[Verified] public static int? F() => null;", "M:C.F"));
    }

    [Fact]
    public void AValueWhereANullableOneIsRequiredIsLifted()
    {
        Assert.Equal(
            new ConvertExpr(VirType.Int32, MaybeInt, VirOverflow.Wrap, new ParamExpr(VirType.Int32, 0)),
            Body("[Verified] public static int? F(int a) => a;", "M:C.F(System.Int32)"));
        Assert.Equal(
            new ConvertExpr(Payment, MaybePayment, VirOverflow.Wrap, new ParamExpr(Payment, 0)),
            Body("[Verified] public static Payment? F(Payment p) => p;", "M:C.F(Payment)"));
        Assert.Equal(
            new CondExpr(MaybePayment, new ParamExpr(VirType.Bool, 0), new ConvertExpr(Payment, MaybePayment, VirOverflow.Wrap, new ParamExpr(Payment, 1)), new NullExpr(MaybePayment)),
            Body("[Verified] public static Payment? F(bool b, Payment p) => b ? p : null;", "M:C.F(System.Boolean,Payment)"));
    }

    [Fact]
    public void CoalesceValueAndCastProduceTheirNodes()
    {
        const string key = "M:C.F(System.Nullable{System.Int32})";
        Assert.Equal(new CoalesceExpr(VirType.Int32, X, LitExpr.Int32(0)), Body("[Verified] public static int F(int? x) => x ?? 0;", key));
        Assert.Equal(new UnwrapExpr(VirType.Int32, UnwrapKind.Value, X), Body("[Verified] public static int F(int? x) => x.Value;", key));
        Assert.Equal(new UnwrapExpr(VirType.Int32, UnwrapKind.Value, X), Body("[Verified] public static int F(int? x) => (int)x;", key));
        Assert.Equal(new CoalesceExpr(VirType.Int32, X, LitExpr.Int32(0)), Body("[Verified] public static int F(int? x) => x.GetValueOrDefault();", key));
        var y = new ParamExpr(VirType.Nullable(VirType.Int64), 0);
        Assert.Equal(new CoalesceExpr(VirType.Int64, y, LitExpr.Int64(0)), Body("[Verified] public static long F(long? y) => y.GetValueOrDefault();", "M:C.F(System.Nullable{System.Int64})"));
    }

    [Fact]
    public void ACoalesceThatThrowsHasAThrowOfTheValueType()
    {
        Assert.Equal(
            new CoalesceExpr(Payment, new ParamExpr(MaybePayment, 0), new ThrowExpr(Payment, "T:System.ArgumentNullException")),
            Body("[Verified] public static Payment F(Payment? p) => p ?? throw new ArgumentNullException(nameof(p));", "M:C.F(Payment)"));
    }

    [Fact]
    public void ANullableArgumentAfterANullCheckIsAnUnwrapAtTheArgument()
    {
        // #163: Roslyn's flow state says p is not null at Use(p); the model checks it anyway, and the walker must prove it.
        var body = Assert.IsType<BlockStmt>(Body("""
            [Verified]
            public static int F(Payment? p)
            {
                if (p is null) return 0;
                return Use(p);
            }
            """, "M:C.F(Payment)"));
        var p = new ParamExpr(MaybePayment, 0);
        Assert.Equal(new IfStmt(new IsNullExpr(p), new BlockStmt(VirList.Of<VirStmt>(new ReturnStmt(LitExpr.Int32(0)))), null), body.Stmts[0]);
        Assert.Equal(
            new ReturnStmt(new CallExpr(VirType.Int32, "M:C.Use(Payment)", VirList.Of<VirExpr>(new UnwrapExpr(Payment, UnwrapKind.NonNull, p)))),
            body.Stmts[1]);
    }

    [Fact]
    public void EveryPlaceThatRequiresANonNullableValueUnwraps()
    {
        var p = new ParamExpr(MaybePayment, 0);
        var unwrapped = new UnwrapExpr(Payment, UnwrapKind.NonNull, p);
        Assert.Equal(unwrapped, Body("[Verified] public static Payment F(Payment? p) => p;", "M:C.F(Payment)"));
        Assert.Equal(new GetExpr(VirType.Int32, "Id", unwrapped), Body("[Verified] public static int F(Payment? p) => p.Id;", "M:C.F(Payment)"));
        Assert.Equal(
            new WithExpr(Payment, unwrapped, VirList.Of(new WithUpdate("Id", LitExpr.Int32(1)))),
            Body("[Verified] public static Payment F(Payment? p) => p with { Id = 1 };", "M:C.F(Payment)"));
        var block = Assert.IsType<BlockStmt>(Body("""
            [Verified]
            public static int F(Payment? p)
            {
                Payment q = p;
                var r = p;
                return Use(q) + Use(r);
            }
            """, "M:C.F(Payment)"));
        Assert.Equal(new DeclStmt(0, "q", unwrapped), block.Stmts[0]);
        Assert.Equal(new DeclStmt(1, "r", p), block.Stmts[1]);
        var sum = Assert.IsType<BinaryExpr>(Assert.IsType<ReturnStmt>(block.Stmts[2]).Value);
        Assert.Equal(new CallExpr(VirType.Int32, "M:C.Use(Payment)", VirList.Of<VirExpr>(new LocalExpr(Payment, 0))), sum.L);
        Assert.Equal(
            new CallExpr(VirType.Int32, "M:C.Use(Payment)", VirList.Of<VirExpr>(new UnwrapExpr(Payment, UnwrapKind.NonNull, new LocalExpr(MaybePayment, 1)))),
            sum.R);
    }

    [Fact]
    public void ANullableRecordFieldIsNullableAndNotAssumedNonNull()
    {
        var result = Inline.Extract("""
            public sealed record Payment(int Id);
            public sealed record Claim(Payment? Payment, Payment Backup);
            public static class C
            {
                [Verified] public static bool Unpaid(Claim c) => c.Payment is null;
            }
            """);
        var claim = Assert.IsType<RecordDefinition>(Unit(result, "T:Claim").Definition);
        Assert.Equal(VirType.Nullable(VirType.Ref("T:Payment")), claim.Fields[0].Type);
        Assert.Equal(["c", "c.Backup"], NonNull(Unit(result, "M:C.Unpaid(Claim)")));
    }

    [Fact]
    public void TheForgivingOperatorIsRejected()
    {
        var result = Extract("[Verified] public static int F(Payment? p) => Use(p!);");
        Assert.Equal("WRT0002 | null-forgiving operator", Only(result, "M:C.F(Payment)"));
    }

    [Theory]
    [InlineData("public static bool F(int? x) => x > 0;", "M:C.F(System.Nullable{System.Int32})", "lifted comparison")]
    [InlineData("public static bool F(int? x) => x == 5;", "M:C.F(System.Nullable{System.Int32})", "lifted comparison")]
    [InlineData("public static int? F(int? a, int? b) => a + b;", "M:C.F(System.Nullable{System.Int32},System.Nullable{System.Int32})", "lifted arithmetic")]
    [InlineData("public static int? F(int? a) => -a;", "M:C.F(System.Nullable{System.Int32})", "lifted arithmetic")]
    [InlineData("public static bool F(Payment? a, Payment b) => a == b;", "M:C.F(Payment,Payment)", "lifted comparison")]
    [InlineData("public static bool F(Payment p) => p == null;", "M:C.F(Payment)", "null")]
    [InlineData("public static bool F(Payment p) => p is null;", "M:C.F(Payment)", "null")]
    [InlineData("public static int F(Payment? p) => p switch { null => 0, _ => 1 };", "M:C.F(Payment)", "switch on a nullable value")]
    public void LiftedOperatorsAndNullOnNonNullableValuesAreRejected(string member, string key, string construct)
    {
        Assert.Equal("WRT0002 | " + construct, Only(Extract("[Verified] " + member), key));
    }

    [Fact]
    public void DecimalLiteralsAreExact()
    {
        var d = new ParamExpr(VirType.Decimal, 0);
        Assert.Equal(
            new BinaryExpr(VirType.Decimal, BinaryOp.Add, VirOverflow.Checked, new DecimalLitExpr(false, 125, 2), d),
            Body("[Verified] public static decimal F(decimal d) => 1.25m + d;", "M:C.F(System.Decimal)"));
        Assert.Equal(new DecimalLitExpr(true, 1500, 3), Body("[Verified] public static decimal F() => -1.500m;", "M:C.F"));
        Assert.Equal(new DecimalLitExpr(false, 1, 28), Body("[Verified] public static decimal F() => 0.0000000000000000000000000001m;", "M:C.F"));
        Assert.Equal(new DecimalLitExpr(false, 7, 0), Body("[Verified] public static decimal F() => 7;", "M:C.F"));
    }

    [Fact]
    public void DecimalComparisonsSubtractionNegationAndMathAreTheirNodes()
    {
        var a = new ParamExpr(VirType.Decimal, 0);
        var b = new ParamExpr(VirType.Decimal, 1);
        const string key = "M:C.F(System.Decimal,System.Decimal)";
        Assert.Equal(new CompareExpr(CompareOp.Eq, CompareKind.Decimal, a, b), Body("[Verified] public static bool F(decimal a, decimal b) => a == b;", key));
        Assert.Equal(new CompareExpr(CompareOp.Lt, CompareKind.Decimal, a, new DecimalLitExpr(false, 10, 1)), Body("[Verified] public static bool F(decimal a, decimal b) => a < 1.0m;", key));
        Assert.Equal(new BinaryExpr(VirType.Decimal, BinaryOp.Sub, VirOverflow.Checked, a, b), Body("[Verified] public static decimal F(decimal a, decimal b) => a - b;", key));
        Assert.Equal(new UnaryExpr(VirType.Decimal, UnaryOp.Neg, VirOverflow.Wrap, a), Body("[Verified] public static decimal F(decimal a, decimal b) => -a;", key));
        Assert.Equal(
            new ModelledCallExpr(VirType.Decimal, "M:System.Math.Max(System.Decimal,System.Decimal)", VirList.Of<VirExpr>(a, b)),
            Body("[Verified] public static decimal F(decimal a, decimal b) => Math.Max(a, b);", key));
        Assert.Equal(
            new ModelledCallExpr(VirType.Decimal, "M:System.Math.Abs(System.Decimal)", VirList.Of<VirExpr>(a)),
            Body("[Verified] public static decimal F(decimal a, decimal b) => Math.Abs(a);", key));
    }

    [Fact]
    public void ARecordMayHaveADecimalField()
    {
        var result = Extract("[Verified] public static decimal Amount(Payment p) => p.Amount;");
        var payment = Assert.IsType<RecordDefinition>(Unit(result, PaymentKey).Definition);
        Assert.Equal(new VirField("Amount", VirType.Decimal), payment.Fields[1]);
        Assert.Equal(new GetExpr(VirType.Decimal, "Amount", new ParamExpr(Payment, 0)), Unit(result, "M:C.Amount(Payment)").Body);
    }

    [Theory]
    [InlineData("public static decimal F(decimal a, decimal b) => a * b;", "decimal operator other than + and -")]
    [InlineData("public static decimal F(decimal a, decimal b) => a / b;", "decimal operator other than + and -")]
    [InlineData("public static decimal F(decimal a, decimal b) => a + (int)b;", "unsupported conversion")]
    [InlineData("public static decimal F(decimal a, decimal b) => Math.Round(a);", "WRT0005")]
    public void OtherDecimalOperationsAreStillRejected(string member, string construct)
    {
        var got = Only(Extract("[Verified] " + member), "M:C.F(System.Decimal,System.Decimal)");
        Assert.StartsWith(construct.StartsWith("WRT", StringComparison.Ordinal) ? construct : "WRT0002 | " + construct, got, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("x.Value > 0", "nullable read")]
    [InlineData("(int)x > 0", "nullable read")]
    [InlineData("p.Id > 0", "non-null unwrap")]
    [InlineData("C.Use(p) > 0", "non-null unwrap")]
    [InlineData("d + 1m > d", "decimal arithmetic")]
    [InlineData("d - 1m < d", "decimal arithmetic")]
    public void ARaisingNullableOrDecimalOperationInATheoremStatementIsRejected(string claim, string construct)
    {
        var result = Inline.Extract($$"""
            public sealed record Payment(int Id);
            public static class C
            {
                [Verified] public static int Use(Payment p) => p.Id;
            }
            public static class T
            {
                [Theorem] static Proof Claim(int? x, Payment? p, decimal d) => Prove.That({{claim}});
            }
            """);
        Assert.Equal("WRT0002 | " + construct, Only(result, "M:T.Claim(System.Nullable{System.Int32},Payment,System.Decimal)"));
    }

    [Fact]
    public void ANonRaisingNullableOrDecimalOperationMayAppearInATheoremStatement()
    {
        var result = Inline.Extract("""
            public static class T
            {
                [Theorem] static Proof Claim(int? x, decimal d) => Prove.That((x ?? 0) == (x ?? 0) && -d == -d && (x is null || x.HasValue));
            }
            """);
        Assert.NotNull(result.Find("M:T.Claim(System.Nullable{System.Int32},System.Decimal)"));
    }

    [Fact]
    public void EffectInferenceSeesNullableReadsUnwrapsAndDecimalArithmetic()
    {
        var result = Extract("""
            [Verified] public static int Read(int? x) => x.Value;
            [Verified] public static int Guarded(Payment? p) => p is null ? 0 : Use(p);
            [Verified] public static decimal Add(decimal a, decimal b) => a + b;
            [Verified] public static int OrZero(int? x) => x ?? 0;
            [Verified] public static decimal Negate(decimal a) => -a;
            """);
        var analysis = Effects.Analyze(result.Units.Select(u => u.Unit));
        Assert.Equal("nullable read", analysis.CauseOf("M:C.Read(System.Nullable{System.Int32})")?.Construct);
        Assert.Equal("non-null unwrap", analysis.CauseOf("M:C.Guarded(Payment)")?.Construct);
        Assert.Equal("decimal arithmetic", analysis.CauseOf("M:C.Add(System.Decimal,System.Decimal)")?.Construct);
        Assert.False(analysis.IsRaising("M:C.OrZero(System.Nullable{System.Int32})"));
        Assert.False(analysis.IsRaising("M:C.Negate(System.Decimal)"));
    }
}
