using Warrant.Cic;
using Warrant.Lean4Export;

namespace Warrant.Kernel.Tests;

/// <summary>
/// No term with a metavariable passes the kernel (KTD1), and a passed deadline rejects like running
/// out of fuel (KTD2). Each rejection is paired with a positive control that differs only in the hole,
/// so a kernel rejecting everything cannot pass.
/// </summary>
public class MVarRejectionTests(InitMediumFixture initMedium) : IClassFixture<InitMediumFixture>
{
    private static readonly EquatableArray<Name> NoParams = EquatableArray<Name>.Empty;
    private static readonly Expr Nat = Expr.Const(Name.Parse("Nat"));
    private static readonly Expr True = Expr.Const(Name.Parse("True"));
    private static readonly Expr TrueIntro = Expr.Const(Name.Parse("True.intro"));
    private static readonly Name U = Name.Parse("u");
    private static readonly Level LevelMVar = Level.MVar(new LMVarId(Name.Parse("_uniq.u")));
    private static readonly MVarExpr M = Expr.MVar(new MVarId(Name.Parse("_uniq.m")));

    private static Name N(string s) => Name.Parse(s);

    private void Admit(KernelDeclaration d, KernelLimits? limits = null) =>
        KernelThread.Run(() => Kernel.Add(Fork(initMedium.Env), d, limits));

    private static KernelEnvironment Fork(KernelEnvironment env)
    {
        var child = new KernelEnvironment();
        foreach (var c in env.Constants)
        {
            child.AddCore(c);
        }
        if (env.IsQuotInitialized)
        {
            child.MarkQuotInitialized();
        }
        return child;
    }

    private void RejectsWithMVars(KernelDeclaration d, string name)
    {
        var ex = Assert.ThrowsAny<KernelException>(() => Admit(d));
        Assert.IsNotType<KernelResourceException>(ex);
        Assert.Equal($"declaration has metavariables '{name}'", ex.Message);
    }

    private static DefinitionDecl Def(string name, EquatableArray<Name> lparams, Expr type, Expr value) =>
        new(new DefinitionInfo(N(name), lparams, type, value, ReducibilityHints.Regular(1), DefinitionSafety.Safe, [N(name)]));

    private static TheoremDecl Thm(string name, EquatableArray<Name> lparams, Expr type, Expr proof) =>
        new(new TheoremInfo(N(name), lparams, type, proof, [N(name)]));

    [Fact]
    public void DefinitionWhoseValueHasAnExprMVar()
    {
        Admit(Def("test.five", NoParams, Nat, Expr.NatLit(5)));
        RejectsWithMVars(Def("test.hole", NoParams, Nat, M), "test.hole");
        RejectsWithMVars(Def("test.holeInside", NoParams, Nat, Expr.App(Expr.Const(N("Nat.succ")), M)), "test.holeInside");
    }

    [Fact]
    public void TheoremWithALevelMVarOnlyInABinderDomain()
    {
        // ∀ (α : Sort l), True, proved by fun (α : Sort l) => True.intro. With l a level metavariable,
        // the hole sits only in a binder's domain, where the universe check does not see it.
        static TheoremDecl Make(string name, EquatableArray<Name> lparams, Level l) =>
            Thm(name, lparams, Expr.Forall(N("α"), Expr.Sort(l), True), Expr.Lam(N("α"), Expr.Sort(l), TrueIntro));

        Admit(Make("test.sortParam", [U], Level.Param(U)));
        RejectsWithMVars(Make("test.sortMVar", NoParams, LevelMVar), "test.sortMVar");
    }

    [Fact]
    public void ConstantReferenceWithALevelMVar()
    {
        // (fun (_ : PUnit.{l}) => True.intro) PUnit.unit.{l} : True
        static TheoremDecl Make(string name, EquatableArray<Name> lparams, Level l) =>
            Thm(name, lparams, True, Expr.App(
                Expr.Lam(N("x"), Expr.Const(N("PUnit"), l), TrueIntro),
                Expr.Const(N("PUnit.unit"), l)));

        Admit(Make("test.constParam", [U], Level.Param(U)));
        RejectsWithMVars(Make("test.constMVar", NoParams, LevelMVar), "test.constMVar");
    }

    [Fact]
    public void InductiveConstructorWithAnMVar()
    {
        static InductiveDecl Make(string name, Expr argType) =>
            new(NoParams, 0, [new InductiveType(N(name), Expr.Type, [new InductiveConstructor(N(name + ".mk"), Expr.Forall(N("a"), argType, Expr.Const(N(name))))])], false);

        Admit(Make("test.IOk", Nat));
        RejectsWithMVars(Make("test.IHole", M), "test.IHole.mk");
        RejectsWithMVars(Make("test.ILevel", Expr.Const(N("PUnit"), LevelMVar)), "test.ILevel.mk");
    }

    [Fact]
    public void TypeCheckerThrowsAKernelExceptionOnAnMVar()
    {
        T Run<T>(Func<TypeChecker, T> f) => KernelThread.Run(() => f(new TypeChecker(initMedium.Env)));

        var infer = Assert.ThrowsAny<KernelException>(() => Run(tc => tc.Infer(M)));
        Assert.Equal("kernel type checker does not support meta variables", infer.Message);
        var check = Assert.ThrowsAny<KernelException>(() => Run(tc => tc.Check(Expr.App(Expr.Const(N("Nat.succ")), M))));
        Assert.Equal("kernel type checker does not support meta variables", check.Message);
        Assert.ThrowsAny<KernelException>(() => Run(tc => tc.Whnf(M)));
        Assert.ThrowsAny<KernelException>(() => Run(tc => tc.WhnfCore(M)));
        Assert.ThrowsAny<KernelException>(() => Run(tc => tc.IsDefEq(M, Expr.MVar(new MVarId(N("_uniq.n"))))));
    }

    [Fact]
    public void InstantiateAndAbstractPassMVarsThrough()
    {
        var x = Expr.FVar(new FVarId(N("_t.x")));
        var f = Expr.Const(N("f"));

        // fun y => f ?m #0 #1, with #0 := x (under the binder, #1 is the loose one).
        var body = Expr.Lam(N("y"), Nat, Expr.App(f, M, Expr.BVar(0), Expr.BVar(1)));
        var inst = ExprOps.Instantiate(body, x);
        Assert.Equal(Expr.Lam(N("y"), Nat, Expr.App(f, M, Expr.BVar(0), x)), inst);
        Assert.True(inst.HasExprMVar);
        Assert.Same(M, ExprOps.Instantiate(M, x));

        var abs = ExprOps.Abstract(Expr.App(f, M, x), [x]);
        Assert.Equal(Expr.App(f, M, Expr.BVar(0)), abs);
        Assert.True(abs.HasExprMVar);
        Assert.False(abs.HasFVar);

        var sort = Expr.Sort(Level.Max(LevelMVar, Level.Param(U)));
        var lifted = ExprOps.InstantiateLevelParams(sort, [U], [Level.One]);
        Assert.Equal(Expr.Sort(Level.Max(LevelMVar, Level.One)), lifted);
        Assert.True(lifted.HasLevelMVar);
    }

    [Fact]
    public void LevelOpsTreatALevelMVarAsAnAtom()
    {
        var other = Level.MVar(new LMVarId(N("_uniq.v")));
        Assert.Equal(LevelMVar, LevelOps.Normalize(Level.Max(LevelMVar, LevelMVar)));
        Assert.True(LevelOps.IsEquivalent(Level.Max(LevelMVar, other), Level.Max(other, LevelMVar)));
        Assert.True(LevelOps.IsGeq(Level.Succ(LevelMVar), LevelMVar));
        Assert.False(LevelOps.IsGeq(LevelMVar, other));
        Assert.False(LevelOps.IsNotZero(LevelMVar));
        Assert.False(LevelOps.NormalizesToZero(LevelMVar));
        Assert.Same(LevelMVar, LevelOps.Instantiate(LevelMVar, [U], [Level.One]));
        Assert.Null(LevelOps.GetUndefinedParam(Level.Max(LevelMVar, Level.Param(U)), [U]));
    }

    [Fact]
    public void NdjsonWriterRefusesMVars()
    {
        static ConstantDeclaration Axiom(Expr type) => new(new AxiomInfo(N("test.ax"), NoParams, type, false));

        using var writer = new Lean4ExportWriter(new MemoryStream());
        var expr = Assert.Throws<ArgumentException>(() => writer.Write(Axiom(Expr.Forall(N("a"), M, Nat))));
        Assert.Contains("metavariable", expr.Message, StringComparison.Ordinal);
        var level = Assert.Throws<ArgumentException>(() => writer.Write(Axiom(Expr.Sort(Level.Succ(LevelMVar)))));
        Assert.Contains("metavariable", level.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void APassedDeadlineRejectsLikeExhaustedFuel()
    {
        var addComm = (TheoremInfo)initMedium.Env.Get(N("Nat.add_comm"));
        TheoremDecl Copy(string name) => Thm(name, NoParams, addComm.Type, addComm.Proof);

        var past = KernelLimits.Interactive with { Deadline = DateTimeOffset.UtcNow.AddMinutes(-1) };
        var ex = Assert.Throws<KernelResourceException>(() => Admit(Copy("test.late"), past));
        Assert.Contains("deadline", ex.Message, StringComparison.Ordinal);

        Admit(Copy("test.noDeadline"));
        Admit(Copy("test.futureDeadline"), KernelLimits.Interactive with { Deadline = DateTimeOffset.UtcNow.AddHours(1) });
    }

    [Fact]
    public void AFutureDeadlineDoesNotChangeFuel()
    {
        var addComm = (TheoremInfo)initMedium.Env.Get(N("Nat.add_comm"));
        long FuelFor(KernelLimits limits) => KernelThread.Run(() =>
        {
            var tc = new TypeChecker(initMedium.Env, limits: limits);
            tc.IsDefEq(tc.Check(addComm.Proof, NoParams), addComm.Type);
            return tc.FuelUsed;
        });

        Assert.Equal(
            FuelFor(KernelLimits.Interactive),
            FuelFor(KernelLimits.Interactive with { Deadline = DateTimeOffset.UtcNow.AddHours(1) }));
    }
}
