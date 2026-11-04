using System.Numerics;
using Warrant.Cic;
using Warrant.Kernel;
using Warrant.Meta.Omega;
using static Warrant.Meta.Tests.InitTerms;
using static Warrant.Meta.Tests.MetaTestSupport;

namespace Warrant.Meta.Tests;

/// <summary>Terms over <c>Int</c> and <c>Nat</c> as Lean elaborates them, for the <c>omega</c> tests.</summary>
internal static class IntTerms
{
    public static Expr IntT { get; } = C("Int");

    public static Expr Lit(BigInteger i) => OmegaExprs.IntLit(i);

    public static Expr NLit(BigInteger n) => NatLit(n);

    /// <summary><c>@HOp.hOp type type type (@instHOp type inst) a b</c>.</summary>
    private static Expr Op(string op, string instH, string inst, Expr type, Expr a, Expr b) =>
        Expr.App(C(op, Level.Zero, Level.Zero, Level.Zero), type, type, type, Expr.App(C(instH, Level.Zero), type, C(inst)), a, b);

    public static Expr Add(Expr a, Expr b) => Op("HAdd.hAdd", "instHAdd", "Int.instAdd", IntT, a, b);

    public static Expr Sub(Expr a, Expr b) => Op("HSub.hSub", "instHSub", "Int.instSub", IntT, a, b);

    public static Expr Mul(Expr a, Expr b) => Op("HMul.hMul", "instHMul", "Int.instMul", IntT, a, b);

    public static Expr Div(Expr a, Expr b) => Op("HDiv.hDiv", "instHDiv", "Int.instDiv", IntT, a, b);

    public static Expr Mod(Expr a, Expr b) => Op("HMod.hMod", "instHMod", "Int.instMod", IntT, a, b);

    public static Expr NAdd(Expr a, Expr b) => Op("HAdd.hAdd", "instHAdd", "instAddNat", Nat, a, b);

    public static Expr NSub(Expr a, Expr b) => Op("HSub.hSub", "instHSub", "instSubNat", Nat, a, b);

    public static Expr Le(Expr a, Expr b) => Expr.App(C("LE.le", Level.Zero), IntT, C("Int.instLEInt"), a, b);

    public static Expr Lt(Expr a, Expr b) => Expr.App(C("LT.lt", Level.Zero), IntT, C("Int.instLTInt"), a, b);

    public static Expr Gt(Expr a, Expr b) => Expr.App(C("GT.gt", Level.Zero), IntT, C("Int.instLTInt"), a, b);

    public static Expr Ge(Expr a, Expr b) => Expr.App(C("GE.ge", Level.Zero), IntT, C("Int.instLEInt"), a, b);

    public static Expr Eq(Expr type, Expr a, Expr b) => Expr.App(C("Eq", Level.One), type, a, b);

    public static Expr NLe(Expr a, Expr b) => Expr.App(C("LE.le", Level.Zero), Nat, C("instLENat"), a, b);

    public static Expr NLt(Expr a, Expr b) => Expr.App(C("LT.lt", Level.Zero), Nat, C("instLTNat"), a, b);

    public static Expr Cast(Expr n) => Expr.App(C("Nat.cast", Level.Zero), IntT, C("instNatCastInt"), n);

    public static Expr ToNat(Expr x) => Expr.App(C("Int.toNat"), x);

    /// <summary><c>if a ≤ b then t else e</c> at <c>Int</c>, with <c>Int.decLe</c>.</summary>
    public static Expr IteLe(Expr a, Expr b, Expr t, Expr e) =>
        Expr.App(C("ite", Level.One), IntT, Le(a, b), Expr.App(C("Int.decLe"), a, b), t, e);

    /// <summary><c>a → b</c>, where both are written over the same bound variables.</summary>
    public static Expr Arrow(Expr a, Expr b) => Expr.Forall(N("h"), a, ExprOps.LiftLooseBVars(b, 0, 1));

    /// <summary><c>∀ (x₁ … xₙ : type), body</c>, with <paramref name="body"/> given the bound variables in order.</summary>
    public static Expr ForallN(Expr type, string[] names, Func<Expr[], Expr> body)
    {
        var vars = names.Select((_, i) => Expr.BVar(names.Length - 1 - i)).ToArray<Expr>();
        var result = body(vars);
        for (int i = names.Length - 1; i >= 0; i--)
        {
            result = Expr.Forall(N(names[i]), type, result);
        }
        return result;
    }
}

/// <summary>
/// The <c>omega</c> port (plan U18, KTD12; docs/m5a/06 "The port") on <c>Int</c> and <c>Nat</c> goals built from the
/// bundle's constants. Every proof is checked by the kernel; failures are compared with Lean 4.35.0's messages for the
/// same goals.
/// </summary>
public sealed class OmegaTests(AttributeSidecarFixture fixture) : IClassFixture<AttributeSidecarFixture>
{
    private static readonly Expr IntT = IntTerms.IntT;

    /// <summary>
    /// Runs <c>omega</c> on the statement and has the kernel admit the proof, which must cite each of
    /// <paramref name="cites"/>, the steps the test is about.
    /// </summary>
    private void Proves(Expr statement, params string[] cites)
    {
        var m = fixture.NewMeta();
        var goal = m.MkFreshExprSyntheticOpaqueMVar(statement);
        m.Omega(goal.Id);
        var proof = m.InstantiateMVars(goal);
        Assert.False(proof.HasExprMVar || proof.HasLevelMVar || proof.HasFVar, $"proof is not ground: {proof}");
        foreach (var name in cites)
        {
            Assert.True(ExprOps.Find(proof, (e, _) => e is ConstExpr c && c.Name == N(name)) is not null, $"the proof does not cite {name}");
        }
        KernelThread.Run(() => Kernel.Kernel.Add(fixture.Bundle.Fork(), new TheoremDecl(new TheoremInfo(N("t"), [], statement, proof, [N("t")]))));
    }

    /// <summary>Runs <c>omega</c> on a statement it cannot prove and returns the message.</summary>
    private string Fails(Expr statement)
    {
        var m = fixture.NewMeta();
        var goal = m.MkFreshExprSyntheticOpaqueMVar(statement);
        var ex = Assert.Throws<TacticException>(() => m.Omega(goal.Id));
        Assert.Equal("omega", ex.Tactic);
        return ex.Message;
    }

    [Fact]
    public void EveryConstantOmegaEmitsIsInTheBundle()
    {
        Assert.All(OmegaNames.All, n => Assert.NotNull(fixture.Env.Find(n)));
    }

    [Fact]
    public void LinearFactsOverIntAndNat()
    {
        // ∀ x y : Int, x < y → y > x
        Proves(IntTerms.ForallN(IntT, ["x", "y"], v => IntTerms.Arrow(IntTerms.Lt(v[0], v[1]), IntTerms.Gt(v[1], v[0]))));
        // ∀ x y : Int, x + 1 ≤ y → x < y ∧ 2 * x < 2 * y
        Proves(IntTerms.ForallN(IntT, ["x", "y"], v => IntTerms.Arrow(
            IntTerms.Le(IntTerms.Add(v[0], IntTerms.Lit(1)), v[1]),
            Expr.App(C("And"), IntTerms.Lt(v[0], v[1]), IntTerms.Lt(IntTerms.Mul(IntTerms.Lit(2), v[0]), IntTerms.Mul(IntTerms.Lit(2), v[1]))))));
        // ∀ x y : Nat, x + 2 ≤ y → x < y - 1
        Proves(IntTerms.ForallN(Nat, ["x", "y"], v => IntTerms.Arrow(
            IntTerms.NLe(IntTerms.NAdd(v[0], IntTerms.NLit(2)), v[1]), IntTerms.NLt(v[0], IntTerms.NSub(v[1], IntTerms.NLit(1))))));
    }

    [Fact]
    public void ThreeVariablesEliminatedExactlyByFourierMotzkin()
    {
        // ∀ x y z : Int, x + y ≤ 10 → y - z ≥ 3 → z ≥ 2 → x ≤ 5: every coefficient is ±1, so each elimination is exact.
        Proves(IntTerms.ForallN(IntT, ["x", "y", "z"], v => IntTerms.Arrow(
            IntTerms.Le(IntTerms.Add(v[0], v[1]), IntTerms.Lit(10)),
            IntTerms.Arrow(IntTerms.Ge(IntTerms.Sub(v[1], v[2]), IntTerms.Lit(3)),
                IntTerms.Arrow(IntTerms.Ge(v[2], IntTerms.Lit(2)), IntTerms.Le(v[0], IntTerms.Lit(5)))))), "Lean.Omega.combo_sat'");
    }

    [Fact]
    public void HardEqualityIsSolvedThroughBalancedMod()
    {
        // ∀ x y : Int, 3 * x + 5 * y = 1 → 0 ≤ x → 0 ≤ y → False: no coefficient is ±1, so omega introduces a bmod variable.
        Proves(IntTerms.ForallN(IntT, ["x", "y"], v => IntTerms.Arrow(
            IntTerms.Eq(IntT, IntTerms.Add(IntTerms.Mul(IntTerms.Lit(3), v[0]), IntTerms.Mul(IntTerms.Lit(5), v[1])), IntTerms.Lit(1)),
            IntTerms.Arrow(IntTerms.Le(IntTerms.Lit(0), v[0]), IntTerms.Arrow(IntTerms.Le(IntTerms.Lit(0), v[1]), C("False"))))), "Lean.Omega.bmod_sat");
    }

    [Fact]
    public void DivisionAndRemainderByLiterals()
    {
        // ∀ x : Int, x % 4 < 4
        Proves(IntTerms.ForallN(IntT, ["x"], v => IntTerms.Lt(IntTerms.Mod(v[0], IntTerms.Lit(4)), IntTerms.Lit(4))), "Int.emod_def");
        // ∀ x : Int, 2 * (x / 2) ≤ x
        Proves(IntTerms.ForallN(IntT, ["x"], v => IntTerms.Le(IntTerms.Mul(IntTerms.Lit(2), IntTerms.Div(v[0], IntTerms.Lit(2))), v[0])));
        // ∀ x : Int, x / 3 ≥ 1 → x ≥ 3
        Proves(IntTerms.ForallN(IntT, ["x"], v => IntTerms.Arrow(
            IntTerms.Ge(IntTerms.Div(v[0], IntTerms.Lit(3)), IntTerms.Lit(1)), IntTerms.Ge(v[0], IntTerms.Lit(3)))));
    }

    [Fact]
    public void AnIfThenElseAtomIsSplit()
    {
        // ∀ x : Int, (if x ≤ 0 then 0 else x) ≥ 0
        Proves(IntTerms.ForallN(IntT, ["x"], v => IntTerms.Ge(IntTerms.IteLe(v[0], IntTerms.Lit(0), IntTerms.Lit(0), v[0]), IntTerms.Lit(0))),
            "Lean.Omega.ite_disjunction", "Or.elim");
    }

    [Fact]
    public void IntToNatBecomesAMaximum()
    {
        // ∀ x : Int, 0 ≤ x → ((x.toNat : Nat) : Int) = x
        Proves(IntTerms.ForallN(IntT, ["x"], v => IntTerms.Arrow(
            IntTerms.Le(IntTerms.Lit(0), v[0]), IntTerms.Eq(IntT, IntTerms.Cast(IntTerms.ToNat(v[0])), v[0]))), "Int.toNat_eq_max");
        // The decrease shape: ∀ n : Int, ¬ n ≤ 0 → (n - 1).toNat < n.toNat
        Proves(IntTerms.ForallN(IntT, ["n"], v => IntTerms.Arrow(
            Expr.App(C("Not"), IntTerms.Le(v[0], IntTerms.Lit(0))),
            IntTerms.NLt(IntTerms.ToNat(IntTerms.Sub(v[0], IntTerms.Lit(1))), IntTerms.ToNat(v[0])))));
    }

    [Fact]
    public void AnInt32ToIntAtomBringsItsRange()
    {
        // ∀ x : Int32, x.toInt < 2 ^ 31, the statement of Int32.toInt_lt, from the atom's range facts alone.
        Proves(fixture.Env.Find(N("Int32.toInt_lt"))!.Type, "Int32.toInt_lt");
        // ∀ x y : Int32, x.toInt + y.toInt < 4294967296, and the Int64 rule.
        Proves(IntTerms.ForallN(Int32T, ["x", "y"], v => IntTerms.Lt(
            IntTerms.Add(Expr.App(C("Int32.toInt"), v[0]), Expr.App(C("Int32.toInt"), v[1])), IntTerms.Lit(BigInteger.Pow(2, 32)))));
        Proves(IntTerms.ForallN(C("Int64"), ["x"], v => IntTerms.Ge(Expr.App(C("Int64.toInt"), v[0]), IntTerms.Lit(-BigInteger.Pow(2, 63)))));
    }

    [Fact]
    public void AFalseGoalFailsWithLeansMessage()
    {
        // Lean 4.35.0 on `example (x y : Nat) (h : x ≤ y) : y < x := by omega`.
        var nat = Fails(IntTerms.ForallN(Nat, ["x", "y"], v => IntTerms.Arrow(IntTerms.NLe(v[0], v[1]), IntTerms.NLt(v[1], v[0]))));
        Assert.Equal(
            "omega could not prove the goal:\na possible counterexample may satisfy the constraints\n  b ≥ 0\n  a ≥ 0\n  a - b ≥ 0\nwhere\n a := ↑y\n b := ↑x",
            nat);

        // Lean 4.35.0 on `example : ∀ (x : Int), x % 4 = x := by omega`.
        var mod = Fails(IntTerms.ForallN(IntT, ["x"], v => IntTerms.Eq(IntT, IntTerms.Mod(v[0], IntTerms.Lit(4)), v[0])));
        Assert.Equal(
            "omega could not prove the goal:\na possible counterexample may satisfy the constraints\n  b ≥ 1\n  0 ≤ a - 4*b ≤ 3\nwhere\n a := x\n b := x / 4",
            mod);

        // Lean 4.35.0 on `example (x y : Int) (h : x < y) : x + 1 < y := by omega`: the equality y = x + 1 eliminates everything.
        var empty = Fails(IntTerms.ForallN(IntT, ["x", "y"], v => IntTerms.Arrow(IntTerms.Lt(v[0], v[1]), IntTerms.Lt(IntTerms.Add(v[0], IntTerms.Lit(1)), v[1]))));
        Assert.Equal(
            "omega could not prove the goal:\nNo usable constraints found. You may need to unfold definitions so `omega` can see linear arithmetic facts about `Nat` and `Int`, which may also involve multiplication, division, and modular remainder by constants.",
            empty);
    }
}
