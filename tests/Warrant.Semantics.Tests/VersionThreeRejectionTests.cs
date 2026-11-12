using Warrant.Vir;

namespace Warrant.Semantics.Tests;

/// <summary>
/// VIR version 3's forms (plan M6 U6) in shapes extraction never makes: each is a translation error, never silently
/// accepted or translated as something else. An enum's underlying type is never decimal, an external call names a
/// dependency its unit lists, a unit lists only dependencies it calls, and only a call that returns a task is awaited.
/// The forms U9 translates are in <see cref="MonadicTranslationTests"/>, U10's contracts in
/// <see cref="ContractObligationTests"/>, U21's decimal forms in <see cref="DecimalTranslationTests"/>, and U19's
/// dependencies, contract units and async methods in <see cref="DependencyObligationTests"/>.
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

    private static readonly VirUnit Get = VirUnit.Contract("M:I.Get", VirList<VirParam>.Empty, VirType.Int32, Block(), VirList<VirAssumption>.Empty, Facts, VirList<string>.Empty);

    private static VirUnit Type(string key, VirDefinition definition) =>
        VirUnit.TypeUnit(key, definition, VirList<VirAssumption>.Empty, Facts, VirList<string>.Empty);

    public static TheoryData<string> Cases => new()
    {
        "await of a value", "external call", "decimal enum", "dependencies", "unawaited task",
    };

    private static VirUnit[] Units(string name) => name switch
    {
        "await of a value" => [Fn(new AwaitExpr(VirType.Int32, X))],
        // No dependency lists the member, so there is no operation to call.
        "external call" => [Fn(new ExternalCallExpr(VirType.Int32, 0, "M:I.Get", VirList<VirExpr>.Empty)), Get],
        "decimal enum" => [Type("T:E", new EnumDefinition(VirType.Decimal, VirList.Of(new VirEnumMember("A", 0))))],
        // A pure body that uses no dependency would translate, and the dependency's contract would be dropped unread.
        "dependencies" => [Fn(X, dependencies: VirList.Of(new VirDependency("store", "T:I", VirList.Of("M:I.Get")))), Get],
        // A task that is not awaited would make the model throw where the CLR returns (KTD22).
        "unawaited task" => [
            Fn(new ExternalCallExpr(VirType.Task(VirType.Int32), 0, "M:I.Load", VirList<VirExpr>.Empty), VirType.Task(VirType.Int32), VirList.Of(new VirDependency("store", "T:I", VirList.Of("M:I.Load")))),
            VirUnit.Contract("M:I.Load", VirList<VirParam>.Empty, VirType.Task(VirType.Int32), Block(), VirList<VirAssumption>.Empty, Facts, VirList<string>.Empty)],
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
        Assert.Contains("lists dependencies, but calls none of them", Message("dependencies"), StringComparison.Ordinal);
        Assert.Contains("which does not list it", Message("external call"), StringComparison.Ordinal);
        Assert.Contains("only its awaited result is", Message("unawaited task"), StringComparison.Ordinal);
    }
}
