namespace Warrant.Vir.Tests;

/// <summary>Raise-ability (plan M6 U6, KTD11): which units translate into the effect monad, and why.</summary>
public class EffectsTests
{
    private static readonly ParamExpr X = new(VirType.Int32, 0);
    private static readonly ParamExpr Y = new(VirType.Int32, 1);

    private static VirUnit Fn(string name, VirNode body, string returns = "int32") => VirUnit.Function(
        "M:C." + name,
        VirList.Of(new VirParam("x", VirType.Int32), new VirParam("y", VirType.Int32)),
        returns == "bool" ? VirType.Bool : VirType.Int32,
        body,
        VirList<VirAssumption>.Empty,
        Samples.Facts,
        VirList<string>.Empty);

    private static VirUnit Theorem(string name, VirExpr statement) =>
        VirUnit.Theorem("M:C." + name, statement, VirList<VirAssumption>.Empty, Samples.Facts, VirList<string>.Empty,
            parameters: VirList.Of(new VirParam("x", VirType.Int32), new VirParam("y", VirType.Int32)));

    private static CallExpr Call(string name, params VirExpr[] args) => new(VirType.Int32, "M:C." + name, new VirList<VirExpr>(args));

    private static BinaryExpr Div(VirExpr l, VirExpr r) => new(VirType.Int32, BinaryOp.Div, VirOverflow.Wrap, l, r);

    private static BinaryExpr Rem(VirExpr l, VirExpr r) => new(VirType.Int32, BinaryOp.Rem, VirOverflow.Wrap, l, r);

    private static BlockStmt Block(params VirStmt[] stmts) => new(new VirList<VirStmt>(stmts));

    private static RaiseCause? CauseOfOnly(VirExpr body) => Effects.Analyze([Fn("F", body)]).CauseOf("M:C.F");

    public static TheoryData<string, VirExpr, string?> Expressions() => new()
    {
        { "x / 2", Div(X, LitExpr.Int32(2)), null },
        { "year % 4", Rem(X, LitExpr.Int32(4)), null },
        { "x / 2L", new BinaryExpr(VirType.Int64, BinaryOp.Div, VirOverflow.Wrap, new ConvertExpr(VirType.Int32, VirType.Int64, VirOverflow.Wrap, X), LitExpr.Int64(2)), null },
        { "x / -1", Div(X, LitExpr.Int32(-1)), "division" },
        { "x % -1", Rem(X, LitExpr.Int32(-1)), "remainder" },
        { "x / 0", Div(X, LitExpr.Int32(0)), "division" },
        { "x % 0", Rem(X, LitExpr.Int32(0)), "remainder" },
        { "x / y", Div(X, Y), "division" },
        { "x / -(2)", Div(X, new UnaryExpr(VirType.Int32, UnaryOp.Neg, VirOverflow.Wrap, LitExpr.Int32(2))), "division" },
        { "1.5m + 2m", new BinaryExpr(VirType.Decimal, BinaryOp.Add, VirOverflow.Wrap, DecimalLitExpr.Of(1.5m), DecimalLitExpr.Of(2m)), "decimal arithmetic" },
        { "-1.5m", new UnaryExpr(VirType.Decimal, UnaryOp.Neg, VirOverflow.Checked, DecimalLitExpr.Of(1.5m)), null },
        { "x + y", new BinaryExpr(VirType.Int32, BinaryOp.Add, VirOverflow.Wrap, X, Y), null },
        { "checked(x + y)", new BinaryExpr(VirType.Int32, BinaryOp.Add, VirOverflow.Checked, X, Y), "checked arithmetic" },
        { "checked(-x)", new UnaryExpr(VirType.Int32, UnaryOp.Neg, VirOverflow.Checked, X), "checked arithmetic" },
        { "checked(+x)", new UnaryExpr(VirType.Int32, UnaryOp.Plus, VirOverflow.Checked, X), null },
        { "checked((long)x)", new ConvertExpr(VirType.Int32, VirType.Int64, VirOverflow.Checked, X), null },
        { "checked((int)l)", new ConvertExpr(VirType.Int64, VirType.Int32, VirOverflow.Checked, new ConvertExpr(VirType.Int32, VirType.Int64, VirOverflow.Wrap, X)), "checked narrowing" },
        { "(int)l", new ConvertExpr(VirType.Int64, VirType.Int32, VirOverflow.Wrap, new ConvertExpr(VirType.Int32, VirType.Int64, VirOverflow.Wrap, X)), null },
        { "n.Value", new UnwrapExpr(VirType.Int32, UnwrapKind.Value, new NullExpr(VirType.Nullable(VirType.Int32))), "nullable read" },
        { "Use(n)", new UnwrapExpr(VirType.Int32, UnwrapKind.NonNull, new NullExpr(VirType.Nullable(VirType.Int32))), "non-null unwrap" },
        { "n ?? 0", new CoalesceExpr(VirType.Int32, new NullExpr(VirType.Nullable(VirType.Int32)), LitExpr.Int32(0)), null },
        { "n is null", new CondExpr(VirType.Int32, new IsNullExpr(new NullExpr(VirType.Nullable(VirType.Int32))), X, Y), null },
        { "n ?? throw", new CoalesceExpr(VirType.Int32, new NullExpr(VirType.Nullable(VirType.Int32)), new ThrowExpr(VirType.Int32, "T:System.ArgumentException")), "throw" },
        { "Math.Abs(x)", new ModelledCallExpr(VirType.Int32, "M:System.Math.Abs(System.Int32)", VirList.Of<VirExpr>(X)), "modelled member M:System.Math.Abs(System.Int32)" },
        { "Math.Max(x, y)", new ModelledCallExpr(VirType.Int32, "M:System.Math.Max(System.Int32,System.Int32)", VirList.Of<VirExpr>(X, Y)), null },
        { "Math.Abs(1.5m)", new ModelledCallExpr(VirType.Decimal, "M:System.Math.Abs(System.Decimal)", VirList.Of<VirExpr>(DecimalLitExpr.Of(1.5m))), null },
        { "store.Get(x)", new ExternalCallExpr(VirType.Int32, 0, "M:IStore.Get(System.Int32)", VirList.Of<VirExpr>(X)), "external call" },
        { "await F(x)", new AwaitExpr(VirType.Int32, new CallExpr(VirType.Task(VirType.Int32), "M:C.Elsewhere", VirList<VirExpr>.Empty)), "await" },
    };

    [Theory]
    [MemberData(nameof(Expressions))]
    public void EachConstructIsPureOrRaisingAndNamed(string source, VirExpr body, string? construct)
    {
        var cause = CauseOfOnly(body);

        Assert.True(construct == cause?.Construct, $"{source}: expected {construct ?? "pure"}, got {cause?.Construct ?? "pure"}");
        if (cause is not null)
        {
            Assert.Equal("M:C.F", cause.Unit);
            Assert.Null(cause.Callee);
            Assert.NotNull(VirTree.IdOf(Fn("F", body), cause.Node));
        }
    }

    [Fact]
    public void ACauseNamesItsNodeInTheUnit()
    {
        var unit = Fn("F", Block(
            new DeclStmt(0, "a", new BinaryExpr(VirType.Int32, BinaryOp.Add, VirOverflow.Wrap, X, Y)),
            new ReturnStmt(Div(new LocalExpr(VirType.Int32, 0), Y))));

        var cause = Effects.Analyze([unit]).CauseOf(unit.Key)!;

        Assert.Equal("division", cause.Construct);
        Assert.Equal(6, VirTree.IdOf(unit, cause.Node)); // block, decl, add, x, y and return come first
    }

    [Fact]
    public void StatementsThatRaiseAreNamed()
    {
        Assert.Equal("throw", Effects.Analyze([Fn("F", Block(new ThrowStmt("T:System.ArgumentException")))]).CauseOf("M:C.F")?.Construct);
        Assert.Equal("Spec.Assert", Effects.Analyze([Fn("F", Block(new AssertStmt(LitExpr.Bool(true), VirList<TacticNode>.Empty), new ReturnStmt(X)))]).CauseOf("M:C.F")?.Construct);
        Assert.Equal("external call", Effects.Analyze([Fn("F", Block(new EvalStmt(new ExternalCallExpr(VirType.Unit, 0, "M:IStore.Save", VirList<VirExpr>.Empty)), new ReturnStmt(X)))]).CauseOf("M:C.F")?.Construct);
    }

    [Fact]
    public void ACallToAUnitWithRequiresIsRaisingAndNamesTheCallee()
    {
        var guarded = Fn("Guarded", Block(new RequiresStmt(new CompareExpr(CompareOp.Gt, CompareKind.Int, Y, LitExpr.Int32(0))), new ReturnStmt(X)));
        var caller = Fn("Caller", Call("Guarded", X, Y));

        var analysis = Effects.Analyze([guarded, caller]);

        Assert.False(analysis.IsRaising("M:C.Guarded"));
        var cause = analysis.CauseOf("M:C.Caller")!;
        Assert.Equal(("call to a method with Spec.Requires", "M:C.Caller", "M:C.Guarded"), (cause.Construct, cause.Unit, cause.Callee));
        Assert.Same(caller.Body, cause.Node);
    }

    [Fact]
    public void TheClaimsOfRequiresAndEnsuresAreNotRun()
    {
        var unit = Fn("F", Block(
            new RequiresStmt(new CompareExpr(CompareOp.Gt, CompareKind.Int, Div(X, Y), LitExpr.Int32(0))),
            new EnsuresStmt(0, "r", new CompareExpr(CompareOp.Eq, CompareKind.Int, new LocalExpr(VirType.Int32, 0), Rem(X, Y))),
            new ReturnStmt(X)));

        Assert.False(Effects.Analyze([unit]).IsRaising(unit.Key));
    }

    [Fact]
    public void ACallToARaisingUnitIsRaisingAndNamesTheConstructAndTheCallee()
    {
        var thrower = Fn("C", Block(new ThrowStmt("T:System.ArgumentException")));
        var middle = Fn("B", new BinaryExpr(VirType.Int32, BinaryOp.Add, VirOverflow.Wrap, Call("C", X, Y), X));
        var top = Fn("A", Call("B", X, Y));
        var pure = Fn("P", X);

        var analysis = Effects.Analyze([top, pure, middle, thrower]);

        var cause = analysis.CauseOf("M:C.A")!;
        Assert.Equal(("throw", "M:C.C", "M:C.B"), (cause.Construct, cause.Unit, cause.Callee));
        Assert.IsType<ThrowStmt>(cause.Node);
        Assert.Equal(("throw", "M:C.C", "M:C.C"), (analysis.CauseOf("M:C.B")!.Construct, analysis.CauseOf("M:C.B")!.Unit, analysis.CauseOf("M:C.B")!.Callee));
        Assert.False(analysis.IsRaising("M:C.P"));
        Assert.Equal(["M:C.A", "M:C.B", "M:C.C"], analysis.Causes.Keys.Order(StringComparer.Ordinal));
    }

    [Fact]
    public void ATheoremWhoseStatementDividesIsRaisingNamingTheDivision()
    {
        var theorem = Theorem("T", new CompareExpr(CompareOp.Le, CompareKind.Int,
            new BinaryExpr(VirType.Int32, BinaryOp.Mul, VirOverflow.Wrap, Div(X, Y), Y), X));
        var halves = Theorem("Halves", new CompareExpr(CompareOp.Le, CompareKind.Int, Div(X, LitExpr.Int32(2)), X));

        var analysis = Effects.Analyze([theorem, halves]);

        var cause = analysis.CauseOf("M:C.T")!;
        Assert.Equal(("division", "M:C.T", (string?)null), (cause.Construct, cause.Unit, cause.Callee));
        Assert.Equal(2, VirTree.IdOf(theorem, cause.Node));
        Assert.False(analysis.IsRaising("M:C.Halves"));
    }

    [Fact]
    public void ATheoremThatCallsARaisingUnitIsRaisingButOneThatCallsAUnitWithRequiresIsNot()
    {
        var thrower = Fn("Thrower", Block(new ThrowStmt("T:System.ArgumentException")));
        var guarded = Fn("Guarded", Block(new RequiresStmt(LitExpr.Bool(true)), new ReturnStmt(X)));
        var aboutThrower = Theorem("AboutThrower", new CompareExpr(CompareOp.Eq, CompareKind.Int, Call("Thrower", X, Y), X));
        var aboutGuarded = Theorem("AboutGuarded", new CompareExpr(CompareOp.Eq, CompareKind.Int, Call("Guarded", X, Y), X));

        var analysis = Effects.Analyze([thrower, guarded, aboutThrower, aboutGuarded]);

        Assert.Equal(("throw", "M:C.Thrower", "M:C.Thrower"), (analysis.CauseOf("M:C.AboutThrower")!.Construct, analysis.CauseOf("M:C.AboutThrower")!.Unit, analysis.CauseOf("M:C.AboutThrower")!.Callee));
        Assert.False(analysis.IsRaising("M:C.AboutGuarded"));
    }

    [Fact]
    public void AStronglyConnectedComponentRaisesTogetherAndIsRecursive()
    {
        // Even calls Odd, Odd calls Even and divides; Count calls itself and is pure; Outside calls Even.
        var even = Fn("Even", Call("Odd", X, Y));
        var odd = Fn("Odd", new BinaryExpr(VirType.Int32, BinaryOp.Add, VirOverflow.Wrap, Call("Even", X, Y), Div(X, Y)));
        var count = Fn("Count", Call("Count", X, Y));
        var outside = Fn("Outside", Call("Even", X, Y));

        var analysis = Effects.Analyze([outside, count, odd, even]);

        Assert.True(analysis.IsRecursive("M:C.Even"));
        Assert.True(analysis.IsRecursive("M:C.Odd"));
        Assert.True(analysis.IsRecursive("M:C.Count"));
        Assert.False(analysis.IsRecursive("M:C.Outside"));
        Assert.Equal(("division", "M:C.Odd", (string?)null), (analysis.CauseOf("M:C.Odd")!.Construct, analysis.CauseOf("M:C.Odd")!.Unit, analysis.CauseOf("M:C.Odd")!.Callee));
        Assert.Equal(("division", "M:C.Odd", "M:C.Odd"), (analysis.CauseOf("M:C.Even")!.Construct, analysis.CauseOf("M:C.Even")!.Unit, analysis.CauseOf("M:C.Even")!.Callee));
        Assert.Equal("M:C.Even", analysis.CauseOf("M:C.Outside")!.Callee);
        Assert.False(analysis.IsRaising("M:C.Count"));
    }

    [Fact]
    public void TypeAndContractUnitsAndCallsOutsideTheSetAreIgnored()
    {
        var caller = Fn("F", Call("Missing", X, Y));

        var analysis = Effects.Analyze([caller, Samples.RecordType(), Samples.GetContract()]);

        Assert.Empty(analysis.Causes);
        Assert.False(analysis.IsRaising(Samples.GetKey));
    }

    [Fact]
    public void TheEffectfulSampleRaisesAtItsFirstConstruct()
    {
        var cause = Effects.Analyze([Samples.Effectful()]).CauseOf(Samples.ProcessKey)!;

        Assert.Equal("throw", cause.Construct); // the ThrowExpr inside the first declaration's ??
        Assert.IsType<ThrowExpr>(cause.Node);
    }
}
