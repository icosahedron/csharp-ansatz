using Warrant.Cic;

namespace Warrant.Kernel.Tests;

/// <summary>Type inference, reduction and definitional equality against the real Init environment.</summary>
public class TypeCheckerTests(InitMediumFixture initMedium) : IClassFixture<InitMediumFixture>
{
    private static Expr C(string name, params Level[] levels) => Expr.Const(Name.Parse(name), levels);

    private static Expr N(int n) => Expr.NatLit(n);

    private T Run<T>(Func<TypeChecker, T> f) => KernelThread.Run(() => f(new TypeChecker(initMedium.Env)));

    [Fact]
    public void NatLiteralArithmeticReduces()
    {
        Assert.Equal(N(5), Run(tc => tc.Whnf(Expr.App(C("Nat.add"), N(2), N(3)))));
        Assert.Equal(N(6), Run(tc => tc.Whnf(Expr.App(C("Nat.mul"), N(2), N(3)))));
        Assert.Equal(N(0), Run(tc => tc.Whnf(Expr.App(C("Nat.sub"), N(2), N(3)))));
        Assert.Equal(N(2), Run(tc => tc.Whnf(Expr.App(C("Nat.div"), N(7), N(3)))));
        Assert.Equal(C("Bool.true"), Run(tc => tc.Whnf(Expr.App(C("Nat.ble"), N(3), N(5)))));
        Assert.Equal(C("Bool.false"), Run(tc => tc.Whnf(Expr.App(C("Nat.beq"), N(3), N(5)))));
    }

    [Fact]
    public void DefinitionalEquality()
    {
        Assert.True(Run(tc => tc.IsDefEq(Expr.App(C("Nat.add"), N(2), N(3)), N(5))));
        Assert.True(Run(tc => tc.IsDefEq(Expr.App(C("Nat.succ"), N(4)), N(5))));
        Assert.False(Run(tc => tc.IsDefEq(N(5), N(6))));
        // Universe-polymorphic unfolding: id.{1} Nat 3 ≡ 3.
        Assert.True(Run(tc => tc.IsDefEq(Expr.App(C("id", Level.One), C("Nat"), N(3)), N(3))));
        // Eta: fun x => Nat.succ x ≡ Nat.succ.
        var eta = Expr.Lam(Name.Parse("x"), C("Nat"), Expr.App(C("Nat.succ"), Expr.BVar(0)));
        Assert.True(Run(tc => tc.IsDefEq(eta, C("Nat.succ"))));
    }

    [Fact]
    public void ProofIrrelevance()
    {
        // Nat.le_refl 0 and Nat.zero_le 0 are different proofs of 0 ≤ 0.
        var p1 = Expr.App(C("Nat.le_refl"), N(0));
        var p2 = Expr.App(C("Nat.zero_le"), N(0));
        Assert.True(Run(tc => tc.IsDefEq(tc.Infer(p1), tc.Infer(p2))));
        Assert.True(Run(tc => tc.IsDefEq(p1, p2)));
    }

    [Fact]
    public void StringLiteralsExpandToCharacterLists()
    {
        var charType = C("Char");
        var nil = Expr.App(C("List.nil", Level.Zero), charType);
        var cons = Expr.App(C("List.cons", Level.Zero), charType);
        Expr Ch(int c) => Expr.App(C("Char.ofNat"), N(c));
        var explicitForm = Expr.App(C("String.ofList"), Expr.App(cons, Ch('h'), Expr.App(cons, Ch('é'), nil)));
        Assert.True(Run(tc => tc.IsDefEq(Expr.StrLit("hé"), explicitForm)));
        Assert.False(Run(tc => tc.IsDefEq(Expr.StrLit("he"), explicitForm)));
    }

    [Fact]
    public void InferAndCheck()
    {
        var addComm = initMedium.Env.Get(Name.Parse("Nat.add_comm"));
        Assert.True(Run(tc => tc.Infer(C("Nat.add_comm")).AlphaEquals(addComm.Type)));
        Assert.Equal(Expr.Sort(Level.One), Run(tc => tc.Check(C("Nat"))));
        Assert.True(Run(tc => tc.IsProp(addComm.Type)));
        Assert.False(Run(tc => tc.IsProp(C("Nat"))));
        // Nat.succ applied to a type is ill-typed.
        Assert.Throws<KernelException>(() => Run(tc => tc.Check(Expr.App(C("Nat.succ"), C("Nat")))));
        Assert.Throws<KernelException>(() => Run(tc => tc.Check(C("NoSuchConstant"))));
        Assert.Throws<KernelException>(() => Run(tc => tc.Check(C("List"))));  // missing universe argument
    }

    [Fact]
    public void LooseBoundVariablesAreRejected() =>
        Assert.Throws<KernelException>(() => Run(tc => tc.Infer(Expr.BVar(0))));

    [Fact]
    public void FuelLimitsWork()
    {
        var big = Expr.App(C("Nat.add_comm"), N(1), N(2));
        var ex = Assert.Throws<KernelResourceException>(() =>
            KernelThread.Run(() => new TypeChecker(initMedium.Env, limits: new KernelLimits(3, 1 << 20)).Check(big)));
        Assert.Contains("fuel", ex.Message, StringComparison.Ordinal);
    }
}
