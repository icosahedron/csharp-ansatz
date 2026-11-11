using Warrant.Vir;

namespace Warrant.Semantics.Tests;

/// <summary>
/// VIR version 3's forms (plan M6 U6) that M6 U9, U10 and U21 do not translate: each is a translation error, never
/// silently accepted or translated as something else. Async, dependencies and contract units wait for U19; an enum's
/// underlying type is never decimal. The forms U9 translates are in <see cref="MonadicTranslationTests"/>, U10's
/// contracts in <see cref="ContractObligationTests"/>, and U21's decimal forms in <see cref="DecimalTranslationTests"/>.
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
        "unit return", "eval", "await", "external call", "decimal enum", "contract unit", "dependencies",
    };

    private static VirUnit[] Units(string name) => name switch
    {
        "unit return" => [Fn(Block(), VirType.Unit)],
        "eval" => [Fn(Block(new EvalStmt(X), new ReturnStmt(X)))],
        "await" => [Fn(new AwaitExpr(VirType.Int32, new CallExpr(VirType.Task(VirType.Int32), "M:C.G", VirList<VirExpr>.Empty)))],
        "external call" => [Fn(new ExternalCallExpr(VirType.Int32, 0, "M:I.Get", VirList<VirExpr>.Empty))],
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
        string Message(string name) => Assert.Throws<TranslationException>(() => Translator.Translate(Units(name), bundle.Env)).Message;
        Assert.Contains("M6 U19", Message("dependencies"), StringComparison.Ordinal);
        Assert.Contains("M6 U19", Message("contract unit"), StringComparison.Ordinal);
        Assert.Contains("M6 U19", Assert.Throws<TranslationException>(() => Literals.Type(VirPrimitive.Unit)).Message, StringComparison.Ordinal);
    }
}
