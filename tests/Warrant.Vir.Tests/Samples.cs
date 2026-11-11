namespace Warrant.Vir.Tests;

/// <summary>Units used by the tests: the doc's running example, and units that use every node kind.</summary>
internal static class Samples
{
    public const string PayoutKey = "M:Payouts.PayoutRules.Payout(System.Int32,System.Int32,System.Int32)";
    public const string CappedKey = "M:Payouts.PayoutRules.CappedAtTheLimit";
    public const string PaymentKey = "T:Payouts.Payment";
    public const string StatusKey = "T:Payouts.Status";
    public const string OutcomeKey = "T:Payouts.Outcome";
    public const string KindKey = "T:Payouts.Kind";

    public static readonly VirFacts Facts = new(VirOverflow.Wrap, "14", "0.1.0", "5.0.0");

    private static readonly RefType Payment = VirType.Ref(PaymentKey);
    private static readonly RefType Status = VirType.Ref(StatusKey);
    private static readonly RefType Outcome = VirType.Ref(OutcomeKey);

    private static ParamExpr P(int i) => new(VirType.Int32, i);

    private static LocalExpr L(int i) => new(VirType.Int32, i);

    /// <summary>The <c>Payout</c> unit of docs/m4/04, "The running example in VIR".</summary>
    public static VirUnit Payout(int zero = 0) => VirUnit.Function(
        PayoutKey,
        VirList.Of(
            new VirParam("loss", VirType.Int32),
            new VirParam("deductible", VirType.Int32),
            new VirParam("limit", VirType.Int32)),
        VirType.Int32,
        new BlockStmt(VirList.Of<VirStmt>(
            new IfStmt(
                new CompareExpr(CompareOp.Le, CompareKind.Int, P(0), P(1)),
                new BlockStmt(VirList.Of<VirStmt>(new ReturnStmt(LitExpr.Int32(zero)))),
                null),
            new DeclStmt(0, "covered", new BinaryExpr(VirType.Int32, BinaryOp.Sub, VirOverflow.Wrap, P(0), P(1))),
            new ReturnStmt(new CondExpr(
                VirType.Int32,
                new CompareExpr(CompareOp.Gt, CompareKind.Int, L(0), P(2)),
                P(2),
                L(0))))),
        VirList<VirAssumption>.Empty,
        Facts,
        VirList<string>.Empty);

    /// <summary>A theorem proved by computing <c>Payout</c>.</summary>
    public static VirUnit Capped() => VirUnit.Theorem(
        CappedKey,
        new CompareExpr(
            CompareOp.Eq,
            CompareKind.Int,
            new CallExpr(VirType.Int32, PayoutKey, VirList.Of<VirExpr>(LitExpr.Int32(5000), LitExpr.Int32(500), LitExpr.Int32(1000))),
            LitExpr.Int32(1000)),
        VirList<VirAssumption>.Empty,
        Facts,
        VirList.Of(PayoutKey));

    /// <summary>An instance member of a record whose block body uses every statement and most expression kinds.</summary>
    public static VirUnit Everything()
    {
        var stmts = new List<VirStmt>
        {
            new DeclStmt(0, "a", new UnaryExpr(VirType.Int32, UnaryOp.Neg, VirOverflow.Wrap, P(0))),
            new DeclStmt(1, "b", new UnaryExpr(VirType.Int32, UnaryOp.Plus, VirOverflow.Wrap, LitExpr.Int32(-5))),
            new DeclStmt(2, "big", new ConvertExpr(VirType.Int32, VirType.Int64, VirOverflow.Wrap, L(0))),
            new DeclStmt(3, "min", LitExpr.Int64(long.MinValue)),
            new DeclStmt(4, "max", LitExpr.Int64(long.MaxValue)),
            new AssignStmt(1, new ConvertExpr(VirType.Int64, VirType.Int32, VirOverflow.Wrap, new LocalExpr(VirType.Int64, 4))),
        };
        foreach (var op in Enum.GetValues<BinaryOp>())
        {
            stmts.Add(new AssignStmt(0, new BinaryExpr(VirType.Int32, op, VirOverflow.Wrap, L(0), L(1))));
        }
        int local = 5;
        foreach (var op in Enum.GetValues<LogicalOp>())
        {
            stmts.Add(new DeclStmt(local++, "l", new LogicalExpr(op, LitExpr.Bool(true), new NotExpr(LitExpr.Bool(false)))));
        }
        foreach (var op in Enum.GetValues<CompareOp>())
        {
            stmts.Add(new DeclStmt(local++, "c", new CompareExpr(op, CompareKind.Int, L(0), L(1))));
        }
        stmts.Add(new DeclStmt(local++, "p", new NewExpr(Payment, VirList.Of<VirExpr>(LitExpr.Int32(7), new MemberExpr(Status, "Open")))));
        stmts.Add(new DeclStmt(local++, "q", new WithExpr(
            Payment,
            new SelfExpr(Payment),
            VirList.Of(new WithUpdate("Amount", new GetExpr(VirType.Int32, "Amount", new SelfExpr(Payment)))))));
        stmts.Add(new DeclStmt(local++, "r", new CallExpr(
            VirType.Bool,
            "M:Payouts.Payment.IsLarge",
            VirList.Of<VirExpr>(new SelfExpr(Payment)))));
        stmts.Add(new IfStmt(
            new CompareExpr(CompareOp.Ne, CompareKind.Bool, LitExpr.Bool(true), LitExpr.Bool(false)),
            new BlockStmt(VirList.Of<VirStmt>(new AssignStmt(0, LitExpr.Int32(1)))),
            new BlockStmt(VirList.Of<VirStmt>(new AssignStmt(0, LitExpr.Int32(2))))));
        stmts.Add(new SwitchStmt(
            L(0),
            VirList.Of(
                new SwitchSection(
                    VirList.Of<VirPattern>(new ConstPattern(LitExpr.Int32(1)), new ConstPattern(LitExpr.Int32(2))),
                    VirList.Of<VirStmt>(new AssignStmt(1, LitExpr.Int32(3)))),
                new SwitchSection(
                    VirList.Of<VirPattern>(new DiscardPattern()),
                    VirList.Of<VirStmt>(new ReturnStmt(LitExpr.Int32(4)))))));

        var arms = new List<SwitchArm>();
        foreach (var op in Enum.GetValues<RelationalOp>())
        {
            arms.Add(new SwitchArm(new RelationalPattern(op, LitExpr.Int32(10)), LitExpr.Int32(1)));
        }
        arms.Add(new SwitchArm(
            new AndPattern(new RelationalPattern(RelationalOp.Ge, LitExpr.Int32(0)), new NotPattern(new ConstPattern(LitExpr.Int32(5)))),
            LitExpr.Int32(2)));
        arms.Add(new SwitchArm(new OrPattern(new ConstPattern(LitExpr.Int32(6)), new ConstPattern(LitExpr.Int32(7))), LitExpr.Int32(3)));
        arms.Add(new SwitchArm(new DiscardPattern(), LitExpr.Int32(4)));
        stmts.Add(new ReturnStmt(new SwitchExpr(VirType.Int32, L(0), new VirList<SwitchArm>(arms))));

        return VirUnit.Function(
            "M:Payouts.Payment.Everything(System.Int32)",
            VirList.Of(new VirParam("x", VirType.Int32)),
            VirType.Int32,
            new BlockStmt(new VirList<VirStmt>(stmts)),
            VirList.Of(
                new VirAssumption(VirAssumptionKind.NonNull, "this"),
                new VirAssumption(VirAssumptionKind.Closed, OutcomeKey),
                new VirAssumption(VirAssumptionKind.ClosedEquality, OutcomeKey),
                new VirAssumption(VirAssumptionKind.ReferencedSource, OutcomeKey)),
            Facts,
            VirList.Of(StatusKey, PaymentKey, "M:Payouts.Payment.IsLarge"),
            self: PaymentKey);
    }

    /// <summary>An expression-bodied function comparing closed and enum values.</summary>
    public static VirUnit ExpressionBodied() => VirUnit.Function(
        "M:Payouts.PayoutRules.Same(Payouts.Outcome,Payouts.Status)",
        VirList.Of(new VirParam("o", Outcome), new VirParam("s", Status)),
        VirType.Bool,
        new LogicalExpr(
            LogicalOp.And,
            new CompareExpr(CompareOp.Eq, CompareKind.Closed, new ParamExpr(Outcome, 0), new MemberExpr(Outcome, "Matched")),
            new CompareExpr(CompareOp.Eq, CompareKind.Enum, new ParamExpr(Status, 1), new MemberExpr(Status, "Open"))),
        VirList.Of(new VirAssumption(VirAssumptionKind.Closed, OutcomeKey)),
        Facts,
        VirList.Of(OutcomeKey, StatusKey));

    /// <summary>A theorem using <c>implies</c> and record equality.</summary>
    public static VirUnit ImpliesTheorem() => VirUnit.Theorem(
        "M:Payouts.PayoutRules.SameIsSame",
        new ImpliesExpr(
            new CompareExpr(CompareOp.Eq, CompareKind.Record, new NewExpr(Payment, VirList.Of<VirExpr>(LitExpr.Int32(1), new MemberExpr(Status, "Open"))), new NewExpr(Payment, VirList.Of<VirExpr>(LitExpr.Int32(1), new MemberExpr(Status, "Open")))),
            LitExpr.Bool(true)),
        VirList<VirAssumption>.Empty,
        Facts,
        VirList.Of(PaymentKey, StatusKey));

    public const string SumKey = "M:Payouts.Recursion.Sum(System.Int32)";
    public const string QuantifiedKey = "M:Payouts.PayoutRules.Quantified(System.Int32)";

    /// <summary>A recursive function whose body starts with its measure (M5a).</summary>
    public static VirUnit Sum() => VirUnit.Function(
        SumKey,
        VirList.Of(new VirParam("n", VirType.Int32)),
        VirType.Int32,
        new BlockStmt(VirList.Of<VirStmt>(
            new DecreasesStmt(P(0)),
            new IfStmt(
                new CompareExpr(CompareOp.Le, CompareKind.Int, P(0), LitExpr.Int32(0)),
                new BlockStmt(VirList.Of<VirStmt>(new ReturnStmt(LitExpr.Int32(0)))),
                null),
            new ReturnStmt(new BinaryExpr(
                VirType.Int32,
                BinaryOp.Add,
                VirOverflow.Wrap,
                P(0),
                new CallExpr(VirType.Int32, SumKey, VirList.Of<VirExpr>(new BinaryExpr(VirType.Int32, BinaryOp.Sub, VirOverflow.Wrap, P(0), LitExpr.Int32(1)))))))),
        VirList<VirAssumption>.Empty,
        Facts,
        VirList<string>.Empty);

    /// <summary>A theorem with a parameter, both quantifiers, a script using every argument kind, and a budget (M5a).</summary>
    public static VirUnit Quantified() => VirUnit.Theorem(
        QuantifiedKey,
        new ForAllExpr(0, "y", VirType.Int32, new ExistsExpr(1, "b", VirType.Bool, new CompareExpr(
            CompareOp.Eq,
            CompareKind.Int,
            new BinaryExpr(VirType.Int32, BinaryOp.Add, VirOverflow.Wrap, P(0), L(0)),
            new CallExpr(VirType.Int32, SumKey, VirList.Of<VirExpr>(L(0)))))),
        VirList<VirAssumption>.Empty,
        Facts,
        VirList.Of(SumKey),
        parameters: VirList.Of(new VirParam("x", VirType.Int32)),
        script: VirList.Of(
            new TacticNode("intro", VirList.Of<VirTacticArg>(new StringArg("y"))),
            new TacticNode("unfold", VirList.Of<VirTacticArg>(new UnitRefArg(SumKey))),
            new TacticNode("simp", VirList.Of<VirTacticArg>(
                new LeanRefArg("Nat.add_comm"),
                new NumberArg(long.MinValue),
                new OptionArg("decide", new BoolArg(false)))),
            new TacticNode("all_goals", VirList.Of<VirTacticArg>(
                new TacticArg(new TacticNode("try", VirList.Of<VirTacticArg>(new TacticArg(new TacticNode("omega", VirList<VirTacticArg>.Empty)))))))),
        budget: new VirBudget(60, 0, 5_000_000_000));

    public static VirUnit RecordType() => VirUnit.TypeUnit(
        PaymentKey,
        new RecordDefinition(VirList.Of(new VirField("Amount", VirType.Int32), new VirField("Status", Status), new VirField("Big", VirType.Int64), new VirField("Ok", VirType.Bool))),
        VirList<VirAssumption>.Empty,
        Facts,
        VirList.Of(StatusKey));

    public static VirUnit EnumType() => VirUnit.TypeUnit(
        StatusKey,
        new EnumDefinition(VirType.Int32, VirList.Of(new VirEnumMember("Open", 0), new VirEnumMember("Closed", -1))),
        VirList<VirAssumption>.Empty,
        Facts,
        VirList<string>.Empty);

    public static VirUnit ClosedEnumType() => VirUnit.TypeUnit(
        KindKey,
        new ClosedDefinition(VirList.Of(new VirClosedMember("Small", 0), new VirClosedMember("Large", long.MaxValue))),
        VirList<VirAssumption>.Empty,
        Facts,
        VirList<string>.Empty);

    public static VirUnit ClosedClassType() => VirUnit.TypeUnit(
        OutcomeKey,
        new ClosedDefinition(VirList.Of(new VirClosedMember("Matched", null), new VirClosedMember("Missed", null))),
        VirList<VirAssumption>.Empty,
        Facts,
        VirList<string>.Empty);

    /// <summary>A unit whose strings need escaping: <c>+</c>, <c>&lt;</c>, quotes, backslash, control and non-ASCII characters.</summary>
    public static VirUnit Escapes() => VirUnit.TypeUnit(
        "T:N.R<T>+\"q\"\\",
        new RecordDefinition(VirList.Of(
            new VirField("café名", VirType.Int32),
            new VirField("a\u0000b\tc\nd\u001fe\u007ff\u009fg>&'h", VirType.Int32),
            new VirField("😀", VirType.Int32))),
        VirList<VirAssumption>.Empty,
        Facts,
        VirList<string>.Empty);

    public const string StoreKey = "T:Payments.IStore";
    public const string GetKey = "M:Payments.IStore.Get(System.Int32)";
    public const string SaveKey = "M:Payments.IStore.Save(System.Decimal)";
    public const string ProcessKey = "M:Payments.Service.Process(System.Nullable{System.Int32},Payouts.Payment)";

    /// <summary>The smallest positive decimal, 1e-28: 28 digits of scale.</summary>
    public static readonly decimal Tiny = 0.0000000000000000000000000001m;

    /// <summary>The contract unit of <c>IStore.Get</c> (M6): its result is null or at least <paramref name="floor"/>.</summary>
    public static VirUnit GetContract(int floor = 0)
    {
        var result = new LocalExpr(VirType.Nullable(VirType.Int32), 0);
        return VirUnit.Contract(
            GetKey,
            VirList.Of(new VirParam("id", VirType.Int32)),
            VirType.Task(VirType.Nullable(VirType.Int32)),
            new BlockStmt(VirList.Of<VirStmt>(
                new RequiresStmt(new CompareExpr(CompareOp.Gt, CompareKind.Int, P(0), LitExpr.Int32(0))),
                new EnsuresStmt(0, "r", new LogicalExpr(
                    LogicalOp.Or,
                    new IsNullExpr(result),
                    new CompareExpr(CompareOp.Ge, CompareKind.Int, new UnwrapExpr(VirType.Int32, UnwrapKind.Value, result), LitExpr.Int32(floor)))))),
            VirList<VirAssumption>.Empty,
            Facts,
            VirList<string>.Empty);
    }

    /// <summary>The contract unit of <c>IStore.Save</c>, a <c>Task</c> member with a result-free <c>Ensures</c> (M6).</summary>
    public static VirUnit SaveContract() => VirUnit.Contract(
        SaveKey,
        VirList.Of(new VirParam("amount", VirType.Decimal)),
        VirType.Task(VirType.Unit),
        new BlockStmt(VirList.Of<VirStmt>(new EnsuresStmt(null, null, LitExpr.Bool(true)))),
        VirList<VirAssumption>.Empty,
        Facts,
        VirList<string>.Empty);

    /// <summary>
    /// A function that uses every M6 node, type, operator and assumption kind, with a dependency whose member keys are
    /// added to its deps (M6).
    /// </summary>
    public static VirUnit Effectful()
    {
        var x = new ParamExpr(VirType.Nullable(VirType.Int32), 0);
        var payment = new ParamExpr(VirType.Nullable(Payment), 1);
        var i = L(0);
        var amount = new LocalExpr(VirType.Decimal, 2);
        var stmts = new List<VirStmt>
        {
            new RequiresStmt(new NotExpr(new IsNullExpr(payment))),
            new EnsuresStmt(5, "r", new CompareExpr(CompareOp.Ge, CompareKind.Int, new LocalExpr(VirType.Int32, 5), LitExpr.Int32(0))),
            new DeclStmt(0, "i", new CoalesceExpr(VirType.Int32, x, new ThrowExpr(VirType.Int32, "T:System.ArgumentNullException"))),
            new DeclStmt(1, "v", new UnwrapExpr(VirType.Int32, UnwrapKind.Value, x)),
            new DeclStmt(2, "amount", new BinaryExpr(
                VirType.Decimal, BinaryOp.Add, VirOverflow.Checked, DecimalLitExpr.Of(Tiny), DecimalLitExpr.Of(-1.50m))),
            new DeclStmt(3, "p", new UnwrapExpr(Payment, UnwrapKind.NonNull, payment)),
            new DeclStmt(4, "none", new NullExpr(VirType.Nullable(Payment))),
            new AssertStmt(
                new CompareExpr(CompareOp.Le, CompareKind.Decimal, amount, DecimalLitExpr.Of(79228162514264337593543950335m)),
                VirList.Of(new TacticNode("omega", VirList<VirTacticArg>.Empty))),
            new AssertStmt(LitExpr.Bool(true), VirList<TacticNode>.Empty),
            new EvalStmt(new AwaitExpr(VirType.Unit, new ExternalCallExpr(VirType.Task(VirType.Unit), 0, SaveKey, VirList.Of<VirExpr>(amount)))),
            new AssignStmt(0, new BinaryExpr(VirType.Int32, BinaryOp.Div, VirOverflow.Wrap, i, LitExpr.Int32(2))),
            new AssignStmt(0, new BinaryExpr(VirType.Int32, BinaryOp.Rem, VirOverflow.Checked, i, L(1))),
            new AssignStmt(0, new ConvertExpr(VirType.Int64, VirType.Int32, VirOverflow.Checked, new LocalExpr(VirType.Int64, 6))),
            new IfStmt(
                new IsNullExpr(new AwaitExpr(VirType.Nullable(VirType.Int32), new ExternalCallExpr(
                    VirType.Task(VirType.Nullable(VirType.Int32)), 0, GetKey, VirList.Of<VirExpr>(i)))),
                new ThrowStmt("T:System.InvalidOperationException"),
                null),
            new ReturnStmt(new ModelledCallExpr(VirType.Int32, "M:System.Math.Max(System.Int32,System.Int32)", VirList.Of<VirExpr>(i, LitExpr.Int32(0)))),
        };
        return VirUnit.Function(
            ProcessKey,
            VirList.Of(new VirParam("x", VirType.Nullable(VirType.Int32)), new VirParam("payment", VirType.Nullable(Payment))),
            VirType.Task(VirType.Int32),
            new BlockStmt(new VirList<VirStmt>(stmts)),
            VirList.Of(
                new VirAssumption(VirAssumptionKind.NonNull, "store"),
                new VirAssumption(VirAssumptionKind.ExternalContract, GetKey),
                new VirAssumption(VirAssumptionKind.CalleeContract, PayoutKey),
                new VirAssumption(VirAssumptionKind.MayThrow, "T:System.InvalidOperationException"),
                new VirAssumption(VirAssumptionKind.CallerPrecondition, ProcessKey)),
            Facts,
            VirList.Of(PaymentKey),
            dependencies: VirList.Of(new VirDependency("store", StoreKey, VirList.Of(SaveKey, GetKey))));
    }

    public static IEnumerable<VirUnit> All() =>
    [
        Payout(), Capped(), Everything(), ExpressionBodied(), ImpliesTheorem(),
        RecordType(), EnumType(), ClosedEnumType(), ClosedClassType(), Escapes(), Sum(), Quantified(),
        GetContract(), SaveContract(), Effectful(), Guard(),
    ];

    public const string GuardKey = "M:Payments.Service.Guard(System.Int32)";

    /// <summary>
    /// A function with <c>Spec.NoThrow</c> (#182) between its <c>Requires</c> and <c>Ensures</c>, whose explicit throw the
    /// <c>Requires</c> rules out.
    /// </summary>
    public static VirUnit Guard() => VirUnit.Function(
        GuardKey,
        VirList.Of(new VirParam("b", VirType.Int32)),
        VirType.Int32,
        new BlockStmt(VirList.Of<VirStmt>(
            new RequiresStmt(new CompareExpr(CompareOp.Ne, CompareKind.Int, P(0), LitExpr.Int32(0))),
            new NoThrowStmt(),
            new EnsuresStmt(0, "r", new CompareExpr(CompareOp.Eq, CompareKind.Int, new LocalExpr(VirType.Int32, 0), P(0))),
            new IfStmt(new CompareExpr(CompareOp.Eq, CompareKind.Int, P(0), LitExpr.Int32(0)), new ThrowStmt("T:System.ArgumentException"), null),
            new ReturnStmt(P(0)))),
        VirList<VirAssumption>.Empty,
        Facts,
        VirList<string>.Empty);
}
