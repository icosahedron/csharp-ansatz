using Warrant.Vir;

namespace Warrant.Semantics.Tests;

/// <summary>
/// VIR version 3's forms (plan M6 U6) are not translated before U9: each is a translation error, never silently accepted
/// or translated as something else.
/// </summary>
public sealed class VersionThreeRejectionTests(SemanticsBundleFixture bundle) : IClassFixture<SemanticsBundleFixture>
{
    private static readonly VirFacts Facts = new(VirOverflow.Wrap, "14", "test", "test");
    private static readonly ParamExpr X = new(VirType.Int32, 0);

    private static VirUnit Fn(VirNode body, VirType? returns = null, VirList<VirDependency>? dependencies = null) => VirUnit.Function(
        "M:C.F(System.Int32)",
        VirList.Of(new VirParam("x", VirType.Int32)),
        returns ?? VirType.Int32,
        body,
        VirList<VirAssumption>.Empty,
        Facts,
        VirList<string>.Empty,
        dependencies: dependencies);

    private static BlockStmt Block(params VirStmt[] stmts) => new(new VirList<VirStmt>(stmts));

    private static VirUnit Type(string key, VirDefinition definition) =>
        VirUnit.TypeUnit(key, definition, VirList<VirAssumption>.Empty, Facts, VirList<string>.Empty);

    public static TheoryData<string> Cases => new()
    {
        "division", "remainder", "decimal return", "unit return", "nullable return", "decimal literal", "decimal comparison",
        "throw", "eval", "requires", "ensures", "assert", "unwrap", "await", "external call", "modelled call",
        "decimal record field", "decimal enum", "contract unit", "dependencies",
    };

    private static VirUnit[] Units(string name) => name switch
    {
        "division" => [Fn(new BinaryExpr(VirType.Int32, BinaryOp.Div, VirOverflow.Wrap, X, LitExpr.Int32(2)))],
        "remainder" => [Fn(new BinaryExpr(VirType.Int32, BinaryOp.Rem, VirOverflow.Wrap, X, LitExpr.Int32(4)))],
        "decimal return" => [Fn(DecimalLitExpr.Of(1.5m), VirType.Decimal)],
        "unit return" => [Fn(Block(), VirType.Unit)],
        "nullable return" => [Fn(new NullExpr(VirType.Nullable(VirType.Int32)), VirType.Nullable(VirType.Int32))],
        "decimal literal" => [Fn(new CondExpr(VirType.Int32, new CompareExpr(CompareOp.Eq, CompareKind.Int, DecimalLitExpr.Of(1m), DecimalLitExpr.Of(1m)), X, X))],
        "decimal comparison" => [Fn(new CondExpr(VirType.Int32, new CompareExpr(CompareOp.Eq, CompareKind.Decimal, X, X), X, X))],
        "throw" => [Fn(Block(new ThrowStmt("T:System.ArgumentException")))],
        "eval" => [Fn(Block(new EvalStmt(X), new ReturnStmt(X)))],
        "requires" => [Fn(Block(new RequiresStmt(LitExpr.Bool(true)), new ReturnStmt(X)))],
        "ensures" => [Fn(Block(new EnsuresStmt(null, null, LitExpr.Bool(true)), new ReturnStmt(X)))],
        "assert" => [Fn(Block(new AssertStmt(LitExpr.Bool(true), VirList<TacticNode>.Empty), new ReturnStmt(X)))],
        "unwrap" => [Fn(new UnwrapExpr(VirType.Int32, UnwrapKind.Value, new NullExpr(VirType.Nullable(VirType.Int32))))],
        "await" => [Fn(new AwaitExpr(VirType.Int32, new CallExpr(VirType.Task(VirType.Int32), "M:C.G", VirList<VirExpr>.Empty)))],
        "external call" => [Fn(new ExternalCallExpr(VirType.Int32, 0, "M:I.Get", VirList<VirExpr>.Empty))],
        "modelled call" => [Fn(new ModelledCallExpr(VirType.Int32, "M:System.Math.Max(System.Int32,System.Int32)", VirList.Of<VirExpr>(X, X)))],
        "decimal record field" => [Type("T:R", new RecordDefinition(VirList.Of(new VirField("Amount", VirType.Decimal))))],
        "decimal enum" => [Type("T:E", new EnumDefinition(VirType.Decimal, VirList.Of(new VirEnumMember("A", 0))))],
        "contract unit" => [VirUnit.Contract("M:I.Get", VirList<VirParam>.Empty, VirType.Int32, Block(), VirList<VirAssumption>.Empty, Facts, VirList<string>.Empty)],
        // A pure body that uses no dependency would translate, and the dependency's contract would be dropped unread.
        "dependencies" => [Fn(X, dependencies: VirList.Of(new VirDependency("store", "T:I", VirList<string>.Empty)))],
        _ => throw new ArgumentOutOfRangeException(nameof(name)),
    };

    [Theory]
    [MemberData(nameof(Cases))]
    public void AVersionThreeFormIsATranslationError(string name)
    {
        Assert.Throws<TranslationException>(() => Translator.Translate(Units(name), bundle.Env));
    }

    [Fact]
    public void ThePlacesThatDefaultedSaySoExplicitly()
    {
        Assert.Contains("M6 U19", Assert.Throws<TranslationException>(() => Translator.Translate(Units("dependencies"), bundle.Env)).Message, StringComparison.Ordinal);
        Assert.Contains("M6 U19", Assert.Throws<TranslationException>(() => Translator.Translate(Units("contract unit"), bundle.Env)).Message, StringComparison.Ordinal);
        Assert.Contains("M6 U9", Assert.Throws<TranslationException>(() => Translator.Translate(Units("division"), bundle.Env)).Message, StringComparison.Ordinal);
        Assert.Contains("M6 U9", Assert.Throws<TranslationException>(() => Conditions.Eq(VirPrimitive.Decimal, Literals.Int32(0), Literals.Int32(0))).Message, StringComparison.Ordinal);
        Assert.Contains("M6 U9", Assert.Throws<TranslationException>(() => Literals.Type(VirPrimitive.Unit)).Message, StringComparison.Ordinal);
    }
}
