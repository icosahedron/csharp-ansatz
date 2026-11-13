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
        Proves(IntTerms.ForallN(IntT, ["x", "y"], v => IntTerms.Arrow(IntTerms.Lt(v[0], v[1]), IntTerms.Gt(v[1], v[0]))));
        Proves(IntTerms.ForallN(IntT, ["x", "y"], v => IntTerms.Arrow(
            IntTerms.Le(IntTerms.Add(v[0], IntTerms.Lit(1)), v[1]),
            Expr.App(C("And"), IntTerms.Lt(v[0], v[1]), IntTerms.Lt(IntTerms.Mul(IntTerms.Lit(2), v[0]), IntTerms.Mul(IntTerms.Lit(2), v[1]))))));
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
        Proves(IntTerms.ForallN(IntT, ["x"], v => IntTerms.Lt(IntTerms.Mod(v[0], IntTerms.Lit(4)), IntTerms.Lit(4))), "Int.emod_def");
        Proves(IntTerms.ForallN(IntT, ["x"], v => IntTerms.Le(IntTerms.Mul(IntTerms.Lit(2), IntTerms.Div(v[0], IntTerms.Lit(2))), v[0])));
        Proves(IntTerms.ForallN(IntT, ["x"], v => IntTerms.Arrow(
            IntTerms.Ge(IntTerms.Div(v[0], IntTerms.Lit(3)), IntTerms.Lit(1)), IntTerms.Ge(v[0], IntTerms.Lit(3)))));
    }

    [Fact]
    public void AnIfThenElseAtomIsSplit()
    {
        Proves(IntTerms.ForallN(IntT, ["x"], v => IntTerms.Ge(IntTerms.IteLe(v[0], IntTerms.Lit(0), IntTerms.Lit(0), v[0]), IntTerms.Lit(0))),
            "Lean.Omega.ite_disjunction", "Or.elim");
    }

    [Fact]
    public void IntToNatBecomesAMaximum()
    {
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

    /// <summary>Runs <c>Tactic.Omega()</c> (<see cref="MetaM.OmegaTactic"/>) on the statement and has the kernel admit the proof.</summary>
    private void PrepProves(Expr statement)
    {
        var m = fixture.NewMeta();
        var goal = m.MkFreshExprSyntheticOpaqueMVar(statement);
        m.OmegaTactic(goal.Id);
        var proof = m.InstantiateMVars(goal);
        Assert.False(proof.HasExprMVar || proof.HasLevelMVar || proof.HasFVar, $"proof is not ground: {proof}");
        KernelThread.Run(() => Kernel.Kernel.Add(fixture.Bundle.Fork(), new TheoremDecl(new TheoremInfo(N("t"), [], statement, proof, [N("t")]))));
    }

    /// <summary>The C# integer types as M4 translates them: <c>int</c> as <c>Int32</c>, <c>long</c> as <c>Int64</c>.</summary>
    public static TheoryData<string> CSharpIntegers => new() { "Int32", "Int64" };

    private static Expr Lit(string t, BigInteger n) =>
        Expr.App(C("OfNat.ofNat", Level.Zero), C(t), Expr.NatLit(n), Expr.App(C(t + ".instOfNat"), Expr.NatLit(n)));

    private static Expr Op(string t, string op, string instH, string inst, Expr a, Expr b) =>
        Expr.App(C(op, Level.Zero, Level.Zero, Level.Zero), C(t), C(t), C(t), Expr.App(C(instH, Level.Zero), C(t), C(inst + t)), a, b);

    private static Expr Add(string t, Expr a, Expr b) => Op(t, "HAdd.hAdd", "instHAdd", "instAdd", a, b);

    private static Expr Cmp(string t, string rel, string inst, Expr a, Expr b) => Expr.App(C(rel, Level.Zero), C(t), C(inst + t), a, b);

    [Theory]
    [MemberData(nameof(CSharpIntegers))]
    public void ZeroIsNeutral(string t)
    {
        // ∀ y, y + 0 = y: ← toInt_inj, toInt_add, the literal lemma and bmod_def turn it into Int arithmetic.
        PrepProves(IntTerms.ForallN(C(t), ["y"], v => IntTerms.Eq(C(t), Add(t, v[0], Lit(t, 0)), v[0])));
    }

    [Theory]
    [MemberData(nameof(CSharpIntegers))]
    public void IncrementBelowTheMaximumIsLarger(string t)
    {
        // ∀ x, x < maxValue → x + 1 > x, the goal of LargerBelowMax after Unfold.
        PrepProves(IntTerms.ForallN(C(t), ["x"], v => IntTerms.Arrow(
            Cmp(t, "LT.lt", "instLT", v[0], C(t + ".maxValue")),
            Cmp(t, "GT.gt", "instLT", Add(t, v[0], Lit(t, 1)), v[0]))));
    }

    [Theory]
    [MemberData(nameof(CSharpIntegers))]
    public void TheDecreaseShapeIsProved(string t)
    {
        // ∀ n, ¬ n ≤ 0 → (n - 1).toInt.toNat < n.toInt.toNat, Sum's decrease obligation (docs/m5a/06).
        Expr ToNat(Expr x) => IntTerms.ToNat(Expr.App(C(t + ".toInt"), x));
        PrepProves(IntTerms.ForallN(C(t), ["n"], v => IntTerms.Arrow(
            Expr.App(C("Not"), Cmp(t, "LE.le", "instLE", v[0], Lit(t, 0))),
            IntTerms.NLt(ToNat(Op(t, "HSub.hSub", "instHSub", "instSub", v[0], Lit(t, 1))), ToNat(v[0])))));
    }

    private static Expr Neg(string t, Expr a) => Expr.App(C("Neg.neg", Level.Zero), C(t), C(t + ".instNeg"), a);

    private static Expr Div(string t, Expr a, Expr b) => Op(t, "HDiv.hDiv", "instHDiv", "instDiv", a, b);

    private static Expr Mod(string t, Expr a, Expr b) => Op(t, "HMod.hMod", "instHMod", "instMod", a, b);

    /// <summary>A literal of <paramref name="t"/> as M4 translates it: <c>-(n : t)</c> when negative.</summary>
    private static Expr SLit(string t, BigInteger n) => n.Sign < 0 ? Neg(t, Lit(t, -n)) : Lit(t, n);

    /// <summary><c>t.minValue</c>'s magnitude: 2^31 or 2^63.</summary>
    private static BigInteger MinMagnitude(string t) => BigInteger.Pow(2, t == "Int32" ? 31 : 63);

    [Theory]
    [MemberData(nameof(CSharpIntegers))]
    public void TheFoldedMinValueLiteralIsANumeral(string t)
    {
        // #41: ∀ x, -2147483648 < x → 0 ≤ if x < 0 then -x else x, the goal of AbsIsNonNegativeAboveMin after Unfold and
        // Simp. The compiler folds int.MinValue to the literal -(2147483648 : Int32), which omega must read as -2^31.
        var zero = Lit(t, 0);
        PrepProves(IntTerms.ForallN(C(t), ["x"], v => IntTerms.Arrow(
            Cmp(t, "LT.lt", "instLT", SLit(t, -MinMagnitude(t)), v[0]),
            Cmp(t, "LE.le", "instLE", zero, Expr.App(C("ite", Level.One), C(t), Cmp(t, "LT.lt", "instLT", v[0], zero),
                Expr.App(C(t + ".decLt"), v[0], zero), Neg(t, v[0]), v[0])))));
    }

    [Theory]
    [MemberData(nameof(CSharpIntegers))]
    public void HalfOfANonNegativeValueIsAtMostTheValue(string t)
    {
        // ∀ x, 0 ≤ x → x / 2 ≤ x, over Lean's truncating Int32 (Int64) division.
        PrepProves(IntTerms.ForallN(C(t), ["x"], v => IntTerms.Arrow(
            Cmp(t, "LE.le", "instLE", Lit(t, 0), v[0]), Cmp(t, "LE.le", "instLE", Div(t, v[0], Lit(t, 2)), v[0]))));
    }

    [Theory]
    [MemberData(nameof(CSharpIntegers))]
    public void ARemainderByThreeIsBetweenMinusTwoAndTwo(string t)
    {
        // ∀ x, -2 ≤ x % 3 ∧ x % 3 ≤ 2: the remainder takes the dividend's sign.
        PrepProves(IntTerms.ForallN(C(t), ["x"], v => Expr.App(C("And"),
            Cmp(t, "LE.le", "instLE", SLit(t, -2), Mod(t, v[0], Lit(t, 3))),
            Cmp(t, "LE.le", "instLE", Mod(t, v[0], Lit(t, 3)), Lit(t, 2)))));
    }

    [Theory]
    [MemberData(nameof(CSharpIntegers))]
    public void DivisionTruncatesTowardZero(string t)
    {
        // ∀ x, x = -7 → x / 2 = -3 ∧ x % 2 = -1: C#'s -7 / 2 and -7 % 2, with a negative dividend.
        PrepProves(IntTerms.ForallN(C(t), ["x"], v => IntTerms.Arrow(
            IntTerms.Eq(C(t), v[0], SLit(t, -7)),
            Expr.App(C("And"),
                IntTerms.Eq(C(t), Div(t, v[0], Lit(t, 2)), SLit(t, -3)),
                IntTerms.Eq(C(t), Mod(t, v[0], Lit(t, 2)), SLit(t, -1))))));
    }

    [Theory]
    [MemberData(nameof(CSharpIntegers))]
    public void DividingByMinusOneNegatesOnlyAboveTheMinimum(string t)
    {
        // (x / -1).toInt = -x.toInt is false at x = minValue, where Lean's division wraps; with x ≠ minValue it holds.
        Expr Claim(Expr x) => IntTerms.Eq(IntT, Expr.App(C(t + ".toInt"), Div(t, x, SLit(t, -1))),
            Expr.App(C("Neg.neg", Level.Zero), IntT, C("Int.instNegInt"), Expr.App(C(t + ".toInt"), x)));
        var m = fixture.NewMeta();
        var goal = m.MkFreshExprSyntheticOpaqueMVar(IntTerms.ForallN(C(t), ["x"], v => Claim(v[0])));
        var ex = Assert.Throws<TacticException>(() => m.OmegaTactic(goal.Id));
        // In the failing case x = minValue the equalities eliminate every atom, so omega reports no usable constraints.
        Assert.StartsWith("omega could not prove the goal:\n", ex.Message, StringComparison.Ordinal);
        PrepProves(IntTerms.ForallN(C(t), ["x"], v => IntTerms.Arrow(
            Expr.App(C("Not"), IntTerms.Eq(C(t), v[0], C(t + ".minValue"))), Claim(v[0]))));
    }

    [Theory]
    [MemberData(nameof(CSharpIntegers))]
    public void IncrementFailsAgainstTheGoalAsGiven(string t)
    {
        // ∀ x, x + 1 > x is false at maxValue: omega's constraints, reported against the goal before the prep step.
        var m = fixture.NewMeta();
        var goal = m.MkFreshExprSyntheticOpaqueMVar(IntTerms.ForallN(C(t), ["x"], v => Cmp(t, "GT.gt", "instLT", Add(t, v[0], Lit(t, 1)), v[0])));
        var ex = Assert.Throws<TacticException>(() => m.OmegaTactic(goal.Id));
        Assert.Equal("omega", ex.Tactic);
        Assert.Equal(goal.Id, ex.Goal);
        Assert.StartsWith("omega could not prove the goal:\na possible counterexample may satisfy the constraints\n", ex.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ANestedProductIsBoundedThroughItsExactValueNotItsWrapAround()
    {
        // #244: -1000 < a < 1000 → (a * 3).toInt - 5 is in int's range. Through the wrap-around alone (toInt_mul's
        // Int.bmod) omega's real shadow, Lean's omega having no dark or grey shadow, leaves a possible counterexample; the
        // product's exact value (a * 3).toInt = a.toInt * 3, which the obligations after it assume once its own holds,
        // closes it. Since #237 Tactic.Omega() finds that exact value itself when omega alone fails: it proves
        // a.toInt * 3 in range under the bounds and rewrites with Warrant.Int32.toInt_mul_of_range.
        const string t = "Int32";
        Expr ToInt(Expr x) => Expr.App(C(t + ".toInt"), x);
        Expr Product(Expr a) => Op(t, "HMul.hMul", "instHMul", "instMul", a, Lit(t, 3));
        var lo = Expr.App(C("Neg.neg", Level.Zero), IntT, C("Int.instNegInt"), IntTerms.Lit(2147483648));
        var hi = IntTerms.Lit(2147483647);
        Expr Claim(Expr a, bool exact)
        {
            var x = IntTerms.Sub(ToInt(Product(a)), IntTerms.Cast(NatLit(5)));
            var overflow = IntTerms.Arrow(Expr.App(C("Or"), IntTerms.Lt(x, lo), IntTerms.Lt(hi, x)), C("False"));
            var bounded = Expr.App(C("And"), Cmp(t, "LT.lt", "instLT", a, Lit(t, 1000)), Cmp(t, "LT.lt", "instLT", SLit(t, -1000), a));
            return IntTerms.Arrow(bounded, exact
                ? IntTerms.Arrow(IntTerms.Eq(IntT, ToInt(Product(a)), IntTerms.Mul(ToInt(a), IntTerms.Lit(3))), overflow)
                : overflow);
        }
        PrepProves(IntTerms.ForallN(C(t), ["a"], v => Claim(v[0], exact: false)));
        PrepProves(IntTerms.ForallN(C(t), ["a"], v => Claim(v[0], exact: true)));
    }

    [Fact]
    public void AProductOfTwoBoundedTermsIsBoundedByTheProductStep()
    {
        // #257: x * y is an atom to omega; from -5 ≤ x ≤ 10 and 0 ≤ y ≤ 7 the step adds Warrant.Int.mul_*'s linear
        // bounds, which give -35 ≤ x * y ≤ 70. A tighter bound on either side is not proved.
        static Expr Neg(BigInteger n) => Expr.App(C("Neg.neg", Level.Zero), IntT, C("Int.instNegInt"), IntTerms.Lit(n));
        static Expr Claim(Expr x, Expr y, BigInteger below, BigInteger above)
        {
            var bounds = Expr.App(C("And"), Expr.App(C("And"), IntTerms.Le(Neg(5), x), IntTerms.Le(x, IntTerms.Lit(10))),
                Expr.App(C("And"), IntTerms.Le(IntTerms.Lit(0), y), IntTerms.Le(y, IntTerms.Lit(7))));
            var product = IntTerms.Mul(x, y);
            return IntTerms.Arrow(bounds, Expr.App(C("And"), IntTerms.Le(Neg(below), product), IntTerms.Le(product, IntTerms.Lit(above))));
        }
        PrepProves(IntTerms.ForallN(IntT, ["x", "y"], v => Claim(v[0], v[1], 35, 70)));
        foreach (var (below, above) in new (BigInteger, BigInteger)[] { (34, 70), (35, 69) })
        {
            var m = fixture.NewMeta();
            var goal = m.MkFreshExprSyntheticOpaqueMVar(IntTerms.ForallN(IntT, ["x", "y"], v => Claim(v[0], v[1], below, above)));
            Assert.Throws<TacticException>(() => m.OmegaTactic(goal.Id));
        }
    }
}
