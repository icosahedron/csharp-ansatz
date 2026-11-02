using Warrant.Cic;

namespace Warrant.Kernel.Tests;

/// <summary>
/// The kernel must reject bad declarations. Each negative case is paired with a positive control so
/// that a kernel rejecting everything cannot pass.
/// </summary>
public class SoundnessTests(InitMediumFixture initMedium) : IClassFixture<InitMediumFixture>
{
    private static readonly EquatableArray<Name> NoParams = EquatableArray<Name>.Empty;
    private static readonly Expr Nat = Expr.Const(Name.Parse("Nat"));

    private static Expr C(string name, params Level[] levels) => Expr.Const(Name.Parse(name), levels);

    private static Name N(string s) => Name.Parse(s);

    /// <summary>Admits into a throwaway fork of the shared init-medium environment.</summary>
    private void Admit(KernelDeclaration d) =>
        KernelThread.Run(() => Kernel.Add(Fork(initMedium.Env), d));

    private static KernelEnvironment Fork(KernelEnvironment env)
    {
        // A child environment, so tests never modify the shared one.
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

    private void Rejects(KernelDeclaration d, string expectedMessagePart)
    {
        var ex = Assert.ThrowsAny<KernelException>(() => Admit(d));
        Assert.IsNotType<KernelResourceException>(ex);
        Assert.Contains(expectedMessagePart, ex.Message, StringComparison.Ordinal);
    }

    private TheoremInfo Theorem(string name) => (TheoremInfo)initMedium.Env.Get(N(name));

    [Fact]
    public void TheoremWithTheWrongProof()
    {
        var addComm = Theorem("Nat.add_comm");
        var zeroAdd = Theorem("Nat.zero_add");
        Admit(new TheoremDecl(new TheoremInfo(N("test.good"), NoParams, addComm.Type, C("Nat.add_comm"), [N("test.good")])));
        Rejects(new TheoremDecl(new TheoremInfo(N("test.bad"), NoParams, addComm.Type, zeroAdd.Proof, [N("test.bad")])), "type mismatch");
    }

    [Fact]
    public void TheoremMustStateAProposition() =>
        Rejects(new TheoremDecl(new TheoremInfo(N("test.notProp"), NoParams, Nat, Expr.NatLit(0), [N("test.notProp")])), "not a proposition");

    [Fact]
    public void DefinitionValueMustHaveTheDeclaredType()
    {
        Admit(new DefinitionDecl(new DefinitionInfo(N("test.five"), NoParams, Nat, Expr.NatLit(5), ReducibilityHints.Regular(1), DefinitionSafety.Safe, [N("test.five")])));
        Rejects(new DefinitionDecl(new DefinitionInfo(N("test.wrong"), NoParams, Nat, C("Bool.true"), ReducibilityHints.Regular(1), DefinitionSafety.Safe, [N("test.wrong")])), "type mismatch");
    }

    [Fact]
    public void UndefinedUniverseParameter()
    {
        var u = N("u");
        Admit(new AxiomDecl(new AxiomInfo(N("test.ax"), [u], Expr.Sort(Level.Param(u)), false)));
        Rejects(new AxiomDecl(new AxiomInfo(N("test.ax2"), NoParams, Expr.Sort(Level.Param(u)), false)), "undefined universe level parameter 'u'");
        Rejects(new AxiomDecl(new AxiomInfo(N("test.ax3"), [u, u], Expr.Sort(Level.Param(u)), false)), "duplicate universe level parameter");
    }

    [Fact]
    public void NamesAndTermsMustBeWellFormed()
    {
        Rejects(new AxiomDecl(new AxiomInfo(N("Nat.add_comm"), NoParams, Expr.Prop, false)), "already been declared");
        Rejects(new AxiomDecl(new AxiomInfo(N("test.fvar"), NoParams, Expr.FVar(new FVarId(N("x"))), false)), "free variables");
        Rejects(new AxiomDecl(new AxiomInfo(N("test.unknown"), NoParams, C("Does.not.exist"), false)), "unknown constant");
        Rejects(new AxiomDecl(new AxiomInfo(N("test.notType"), NoParams, Expr.NatLit(3), false)), "type expected");
    }

    [Fact]
    public void SafeMutualDefinitionsAreRejected()
    {
        var f = new DefinitionInfo(N("test.f"), NoParams, Nat, Expr.NatLit(0), ReducibilityHints.Opaque, DefinitionSafety.Safe, [N("test.f")]);
        Rejects(new MutualDefinitionDecl([f]), "not tagged as unsafe/partial");
    }

    // ------------------------------------------------------------------ inductive types

    private static InductiveDecl Ind(string name, Expr type, params (string Name, Func<Expr, Expr> Type)[] ctors)
    {
        var self = C(name);
        return new InductiveDecl(NoParams, 0,
            [new InductiveType(N(name), type, ctors.Select(c => new InductiveConstructor(N(c.Name), c.Type(self))).ToEquatableArray())],
            false);
    }

    private static Expr Arrow(Expr a, Expr b) => Expr.Forall(N("a"), a, b);

    [Fact]
    public void WellFormedInductiveIsAcceptedWithAGeneratedRecursor()
    {
        var env = Fork(initMedium.Env);
        KernelThread.Run(() => Kernel.Add(env, Ind("test.Tree", Expr.Type,
            ("test.Tree.leaf", t => t),
            ("test.Tree.node", t => Arrow(t, Arrow(t, t))))));
        var rec = Assert.IsType<RecursorInfo>(env.Find(N("test.Tree.rec")));
        Assert.Equal(2, rec.Rules.Count);
        Assert.Equal(1, rec.NumMotives);
        Assert.Equal(2, rec.NumMinors);
        Assert.False(rec.K);
        Assert.True(((InductiveInfo)env.Get(N("test.Tree"))).IsRec);
    }

    [Fact]
    public void NonPositiveOccurrence() =>
        Rejects(Ind("test.Bad", Expr.Type, ("test.Bad.mk", t => Arrow(Arrow(t, Nat), t))), "non positive occurrence");

    [Fact]
    public void FieldUniverseTooBig() =>
        Rejects(Ind("test.Big", Expr.Type, ("test.Big.mk", t => Arrow(Expr.Type, t))), "too big");

    [Fact]
    public void ConstructorMustReturnTheType() =>
        Rejects(Ind("test.W", Expr.Type, ("test.W.mk", _ => Nat)), "invalid return type");

    // ------------------------------------------------------------------ tampered exports

    private CheckResult CheckTampered(Name target, Func<Declaration, Declaration> tamper)
    {
        var env = initMedium.EnvBefore(target);
        var tampered = tamper(initMedium.DeclarationOf(target));
        return KernelThread.Run(() => new ExportChecker(env).Check(tampered))!;
    }

    [Fact]
    public void UntamperedDeclarationsPass()
    {
        foreach (var n in new[] { "Eq", "Nat", "Quot" })
        {
            var r = CheckTampered(N(n), d => d);
            Assert.True(r.Accepted, $"{n}: {r.Error}");
        }
    }

    [Fact]
    public void RecursorWithTheWrongKFlag()
    {
        var r = CheckTampered(N("Eq"), d =>
        {
            var ind = (InductiveDeclaration)d;
            return ind with { Recursors = ind.Recursors.Select(x => x with { K = !x.K }).ToEquatableArray() };
        });
        Assert.False(r.Accepted);
        Assert.Contains("Eq.rec", r.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void RecursorWithSwappedComputationRules()
    {
        var r = CheckTampered(N("Nat"), d =>
        {
            var ind = (InductiveDeclaration)d;
            var rec = ind.Recursors[0];
            var rules = rec.Rules;
            var swapped = new[] { rules[0] with { Rhs = rules[1].Rhs }, rules[1] with { Rhs = rules[0].Rhs } };
            return ind with { Recursors = [rec with { Rules = swapped }] };
        });
        Assert.False(r.Accepted);
        Assert.Contains("Nat.rec", r.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void MissingRecursorAndWrongFieldCount()
    {
        var missing = CheckTampered(N("Nat"), d => (InductiveDeclaration)d with { Recursors = EquatableArray<RecursorInfo>.Empty });
        Assert.False(missing.Accepted);
        Assert.Contains("missing from the export", missing.Error, StringComparison.Ordinal);

        var fields = CheckTampered(N("Nat"), d =>
        {
            var ind = (InductiveDeclaration)d;
            return ind with { Constructors = ind.Constructors.Select(c => c with { NumFields = c.NumFields + 1 }).ToEquatableArray() };
        });
        Assert.False(fields.Accepted);
    }

    [Fact]
    public void TamperedQuotientConstant()
    {
        var r = CheckTampered(N("Quot"), d =>
        {
            var q = (QuotInfo)((ConstantDeclaration)d).Constant;
            return new ConstantDeclaration(q with { Type = Expr.Forall(N("x"), Expr.Prop, q.Type) });
        });
        Assert.False(r.Accepted);
        Assert.Contains("quotient", r.Error, StringComparison.Ordinal);
    }
}
