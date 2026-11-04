using System.Numerics;
using FsCheck;
using FsCheck.Fluent;
using Warrant.Cic;
using Warrant.Kernel;
using Warrant.Meta.Omega;
using static Warrant.Meta.Tests.MetaTestSupport;

namespace Warrant.Meta.Tests;

/// <summary>
/// The C# arithmetic of the <c>omega</c> port against the kernel's evaluation of Init's <c>Lean.Omega</c> definitions
/// (plan U18, KTD12). An <c>omega</c> proof states each derived constraint as a literal, and the kernel checks it by
/// recomputing <c>tidy</c>, <c>combo</c>, <c>combine</c> and <c>bmod_coeffs</c> on the previous literals; so for random
/// literal inputs, the kernel must accept <c>rfl : f inputs = (the C# result)</c>.
/// </summary>
public sealed class OmegaArithmeticProperties(SemanticsBundleFixture bundle) : IClassFixture<SemanticsBundleFixture>
{
    private const int Cases = 100;

    private static readonly Expr ConstraintT = Expr.Const(N("Lean.Omega.Constraint"));
    private static readonly Expr CoeffsT = Expr.Const(N("Lean.Omega.Coeffs"));

    private static Gen<(TA, TB)> Zip<TA, TB>(Gen<TA> a, Gen<TB> b) => a.SelectMany(x => b.Select(y => (x, y)));

    private static Gen<(TA, TB, TC)> Zip<TA, TB, TC>(Gen<TA> a, Gen<TB> b, Gen<TC> c) =>
        a.SelectMany(x => b.SelectMany(y => c.Select(z => (x, y, z))));

    private static Gen<BigInteger> SmallInt(int bound) => Gen.Choose(-bound, bound).Select(i => (BigInteger)i);

    private static readonly Gen<BigInteger?> Bound = Gen.Frequency(
        (1, Gen.Constant<BigInteger?>(null)),
        (4, SmallInt(30).Select(i => (BigInteger?)i)));

    private static readonly Gen<Constraint> Constraints = Bound.SelectMany(l => Bound.Select(u => new Constraint(l, u)));

    // Entries from a few small values, so gcds above 1, zeros and ±1 are all common.
    private static readonly Gen<Coeffs> CoeffsGen = Gen.Choose(0, 5).SelectMany(n =>
        Gen.Elements<BigInteger>(-12, -6, -4, -3, -2, -1, 0, 0, 1, 2, 3, 4, 6, 9, 12).ArrayOf(n).Select(Coeffs.Of));

    /// <summary>Whether the kernel accepts <c>rfl : lhs = rhs</c> at <paramref name="type"/>.</summary>
    private bool KernelAgrees(Expr type, Expr lhs, Expr rhs)
    {
        var statement = Expr.App(Expr.Const(N("Eq"), Level.One), type, lhs, rhs);
        var proof = Expr.App(Expr.Const(N("Eq.refl"), Level.One), type, lhs);
        try
        {
            KernelThread.Run(() => Kernel.Kernel.Add(bundle.Fork(), new TheoremDecl(new TheoremInfo(N("t"), [], statement, proof, [N("t")]))));
            return true;
        }
        catch (KernelException)
        {
            return false;
        }
    }

    private static Expr App(string f, params Expr[] args) => Expr.App(Expr.Const(N(f)), args);

    [Fact]
    public void TidyAgreesWithInit() =>
        Pbt.Check(Prop.ForAll(Constraints.ToArbitrary(), CoeffsGen.ToArbitrary(), (s, x) =>
        {
            var (s1, x1) = Tidy.TidyPair(s, x);
            var (sE, xE) = (OmegaExprs.ToExpr(s), OmegaExprs.ToExpr(x));
            return KernelAgrees(ConstraintT, App("Lean.Omega.tidyConstraint", sE, xE), OmegaExprs.ToExpr(s1))
                && KernelAgrees(CoeffsT, App("Lean.Omega.tidyCoeffs", sE, xE), OmegaExprs.ToExpr(x1));
        }), Cases);

    [Fact]
    public void NormalizeAndPositivizeAgreeWithInit() =>
        Pbt.Check(Prop.ForAll(Constraints.ToArbitrary(), CoeffsGen.ToArbitrary(), (s, x) =>
        {
            var (sE, xE) = (OmegaExprs.ToExpr(s), OmegaExprs.ToExpr(x));
            var (ns, nx) = Tidy.Normalize(s, x);
            var (ps, px) = Tidy.Positivize(s, x);
            return KernelAgrees(ConstraintT, App("Lean.Omega.normalizeConstraint", sE, xE), OmegaExprs.ToExpr(ns))
                && KernelAgrees(CoeffsT, App("Lean.Omega.normalizeCoeffs", sE, xE), OmegaExprs.ToExpr(nx))
                && KernelAgrees(ConstraintT, App("Lean.Omega.positivizeConstraint", sE, xE), OmegaExprs.ToExpr(ps))
                && KernelAgrees(CoeffsT, App("Lean.Omega.positivizeCoeffs", sE, xE), OmegaExprs.ToExpr(px));
        }), Cases);

    [Fact]
    public void ComboAndCombineAgreeWithInit()
    {
        var inputs = Zip(Zip(Constraints, Constraints), Zip(CoeffsGen, CoeffsGen), Zip(SmallInt(5), SmallInt(5)));
        Pbt.Check(Prop.ForAll(inputs.ToArbitrary(), input =>
        {
            var ((s, t), (x, y), (a, b)) = input;
            var (aE, bE) = (OmegaExprs.IntLit(a), OmegaExprs.IntLit(b));
            var (sE, tE) = (OmegaExprs.ToExpr(s), OmegaExprs.ToExpr(t));
            return KernelAgrees(CoeffsT, App("Lean.Omega.Coeffs.combo", aE, OmegaExprs.ToExpr(x), bE, OmegaExprs.ToExpr(y)), OmegaExprs.ToExpr(Coeffs.Combo(a, x, b, y)))
                && KernelAgrees(ConstraintT, App("Lean.Omega.Constraint.combo", aE, sE, bE, tE), OmegaExprs.ToExpr(Constraint.Combo(a, s, b, t)))
                && KernelAgrees(ConstraintT, App("Lean.Omega.Constraint.combine", sE, tE), OmegaExprs.ToExpr(s.Combine(t)));
        }), Cases);
    }

    [Fact]
    public void BmodCoeffsAgreesWithInit()
    {
        var inputs = Zip(Gen.Choose(0, 10), Gen.Choose(0, 6), CoeffsGen);
        Pbt.Check(Prop.ForAll(inputs.ToArbitrary(), input =>
        {
            var (m, i, x) = input;
            return KernelAgrees(CoeffsT, App("Lean.Omega.bmod_coeffs", OmegaExprs.NatLit(m), OmegaExprs.NatLit(i), OmegaExprs.ToExpr(x)),
                OmegaExprs.ToExpr(Tidy.BmodCoeffs(m, i, x)));
        }), Cases);
    }

    [Fact]
    public void TheKernelRejectsAWrongResult()
    {
        // The check above can fail: a combine whose upper bound is off by one, or a list one zero too long, is rejected.
        var s = new Constraint(1, 9);
        var t = new Constraint(null, 5);
        var lhs = App("Lean.Omega.Constraint.combine", OmegaExprs.ToExpr(s), OmegaExprs.ToExpr(t));
        Assert.True(KernelAgrees(ConstraintT, lhs, OmegaExprs.ToExpr(new Constraint(1, 5))));
        Assert.False(KernelAgrees(ConstraintT, lhs, OmegaExprs.ToExpr(new Constraint(1, 4))));
        var x = Coeffs.Of(2, 4);
        var combo = App("Lean.Omega.Coeffs.combo", OmegaExprs.IntLit(1), OmegaExprs.ToExpr(x), OmegaExprs.IntLit(1), OmegaExprs.ToExpr(Coeffs.Of(1)));
        Assert.True(KernelAgrees(CoeffsT, combo, OmegaExprs.ToExpr(Coeffs.Of(3, 4))));
        Assert.False(KernelAgrees(CoeffsT, combo, OmegaExprs.ToExpr(Coeffs.Of(3, 4, 0))));
    }
}
