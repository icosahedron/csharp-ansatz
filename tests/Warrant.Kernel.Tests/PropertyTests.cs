using System.Numerics;
using FsCheck;
using FsCheck.Fluent;
using Warrant.Cic;
using Warrant.Lean4Export;

namespace Warrant.Kernel.Tests;

/// <summary>
/// Property-based tests: each property compares the kernel against an independent meaning
/// (evaluation of levels, BigInteger arithmetic, the typing rules of a small generated language)
/// on random inputs. FsCheck prints a replay seed and a shrunk counterexample on failure.
/// </summary>
public class PropertyTests(InitMediumFixture initMedium) : IClassFixture<InitMediumFixture>
{
    private static readonly Config Runs = Config.QuickThrowOnFailure.WithMaxTest(300);

    /// <summary>Builds a recursive generator only when it is sampled (eager construction is exponential).</summary>
    private static Gen<T> Defer<T>(Func<Gen<T>> make) => Gen.Constant(0).SelectMany(_ => make());

    private static Gen<(TA, TB)> Zip<TA, TB>(Gen<TA> a, Gen<TB> b) =>
        a.SelectMany(x => b.Select(y => (x, y)));

    private static Gen<(TA, TB, TC)> Zip<TA, TB, TC>(Gen<TA> a, Gen<TB> b, Gen<TC> c) =>
        a.SelectMany(x => b.SelectMany(y => c.Select(z => (x, y, z))));

    // ================================================================== universe levels

    private static readonly Name[] ParamNames = [Name.Parse("u"), Name.Parse("v"), Name.Parse("w")];

    private static Gen<Level> LevelGen(int size) =>
        size <= 0
            ? Gen.OneOf(Gen.Constant(Level.Zero), Gen.Elements(ParamNames).Select(Level.Param))
            : Gen.Frequency(
                (2, LevelGen(0)),
                (2, Defer(() => LevelGen(size - 1).Select(Level.Succ))),
                (2, Defer(() => Zip(LevelGen(size / 2), LevelGen(size / 2)).Select(p => Level.Max(p.Item1, p.Item2)))),
                (2, Defer(() => Zip(LevelGen(size / 2), LevelGen(size / 2)).Select(p => Level.IMax(p.Item1, p.Item2)))));

    private static readonly Arbitrary<Level> Levels = Gen.Sized(s => LevelGen(Math.Min(s, 8))).ToArbitrary();

    private static readonly Arbitrary<(Level, Level)> LevelPairs = Zip(Levels.Generator, Levels.Generator).ToArbitrary();

    /// <summary>All assignments of 0..3 to u, v, w.</summary>
    private static readonly int[][] Assignments =
        [.. from a in Enumerable.Range(0, 4) from b in Enumerable.Range(0, 4) from c in Enumerable.Range(0, 4) select new[] { a, b, c }];

    /// <summary>The value of a level under an assignment of its parameters (the semantics the algebra must respect).</summary>
    private static int Eval(Level l, int[] sigma) => l.Kind switch
    {
        LevelKind.Zero => 0,
        LevelKind.Succ => Eval(l.Lhs!, sigma) + 1,
        LevelKind.Max => Math.Max(Eval(l.Lhs!, sigma), Eval(l.Rhs!, sigma)),
        LevelKind.IMax => Eval(l.Rhs!, sigma) == 0 ? 0 : Math.Max(Eval(l.Lhs!, sigma), Eval(l.Rhs!, sigma)),
        _ => sigma[Array.IndexOf(ParamNames, l.ParamName)],
    };

    [Fact]
    public void NormalizationPreservesMeaning() =>
        Prop.ForAll(Levels, l => Assignments.All(s => Eval(LevelOps.Normalize(l), s) == Eval(l, s))).Check(Runs);

    [Fact]
    public void EquivalenceIsSound() =>
        Prop.ForAll(LevelPairs, p =>
            !LevelOps.IsEquivalent(p.Item1, p.Item2) || Assignments.All(s => Eval(p.Item1, s) == Eval(p.Item2, s))).Check(Runs);

    [Fact]
    public void GeqIsSound() =>
        Prop.ForAll(LevelPairs, p =>
            !LevelOps.IsGeq(p.Item1, p.Item2) || Assignments.All(s => Eval(p.Item1, s) >= Eval(p.Item2, s))).Check(Runs);

    [Fact]
    public void EquivalenceIsReflexiveAndSymmetric() =>
        Prop.ForAll(LevelPairs, p =>
            LevelOps.IsEquivalent(p.Item1, p.Item1)
            && LevelOps.IsEquivalent(p.Item1, p.Item2) == LevelOps.IsEquivalent(p.Item2, p.Item1)).Check(Runs);

    /// <summary>
    /// Found by property testing: Lean's level normalization is not idempotent (its <c>imax</c> case
    /// rebuilds an unsorted <c>max</c>), so <c>IsEquivalent(l, Normalize(l))</c> can be false although
    /// both always have the same value. This is incompleteness, not unsoundness, and Warrant
    /// matches Lean's C++ exactly here; the test pins that behaviour.
    /// </summary>
    [Fact]
    public void NormalizationIsNotIdempotentExactlyAsInLean()
    {
        Level P(string n) => Level.Param(Name.Parse(n));
        // imax (w+1) (max u (v+1)): the second argument is never zero, so normalization turns the
        // imax into a max, but without flattening or sorting it.
        var a = Level.IMax(Level.Succ(P("w")), Level.Max(P("u"), Level.Succ(P("v"))));
        var once = LevelOps.Normalize(a);
        var twice = LevelOps.Normalize(once);
        Assert.Equal(LevelKind.Max, once.Kind);
        Assert.NotEqual(once, twice);
        Assert.False(LevelOps.IsEquivalent(a, once));
        Assert.All(Assignments, s => Assert.Equal(Eval(a, s), Eval(once, s)));
    }

    [Fact]
    public void SmartConstructorsAndInstantiationRespectMeaning()
    {
        var triples = Zip(Levels.Generator, Levels.Generator, Levels.Generator).ToArbitrary();
        Prop.ForAll(triples, t =>
        {
            var (a, b, c) = t;
            var names = new EquatableArray<Name>([.. ParamNames]);
            var inst = LevelOps.Instantiate(a, names, [b, c, Level.One]);
            return Assignments.All(s =>
                Eval(LevelOps.MkMax(a, b), s) == Math.Max(Eval(a, s), Eval(b, s))
                && Eval(LevelOps.MkIMax(a, b), s) == (Eval(b, s) == 0 ? 0 : Math.Max(Eval(a, s), Eval(b, s)))
                && Eval(inst, s) == Eval(a, [Eval(b, s), Eval(c, s), 1]));
        }).Check(Runs);
    }

    // ================================================================== expression operations

    private static readonly Expr[] FVars = [.. Enumerable.Range(1, 3).Select(i => (Expr)Expr.FVar(new FVarId(Name.Parse($"_prop.{i}"))))];
    private static readonly Expr[] Consts = [Expr.Const(Name.Parse("f")), Expr.Const(Name.Parse("g")), Expr.Prop, Expr.Type];
    private static readonly Name[] BinderNames = [Name.Parse("x"), Name.Parse("y")];

    /// <summary>Random terms with loose bound variables (up to <paramref name="depth"/> + 1) and free variables.</summary>
    private static Gen<Expr> ExprGen(int size, int depth) =>
        size <= 0
            ? Gen.OneOf(
                Gen.Choose(0, depth + 1).Select(i => (Expr)Expr.BVar(i)),
                Gen.Elements(FVars),
                Gen.Elements(Consts),
                Gen.Choose(0, 99).Select(n => (Expr)Expr.NatLit(n)))
            : Gen.Frequency(
                (2, ExprGen(0, depth)),
                (3, Defer(() => Zip(ExprGen(size / 2, depth), ExprGen(size / 2, depth)).Select(p => (Expr)Expr.App(p.Item1, p.Item2)))),
                (2, Defer(() => Zip(Gen.Elements(BinderNames), ExprGen(size / 2, depth), ExprGen(size / 2, depth + 1))
                    .Select(t => (Expr)Expr.Lam(t.Item1, t.Item2, t.Item3)))),
                (2, Defer(() => Zip(Gen.Elements(BinderNames), ExprGen(size / 2, depth), ExprGen(size / 2, depth + 1))
                    .Select(t => (Expr)Expr.Forall(t.Item1, t.Item2, t.Item3, BinderInfo.Implicit)))),
                (1, Defer(() => Zip(ExprGen(size / 3, depth), ExprGen(size / 3, depth), ExprGen(size / 3, depth + 1))
                    .Select(t => (Expr)Expr.Let(BinderNames[0], t.Item1, t.Item2, t.Item3)))),
                (1, Defer(() => ExprGen(size - 1, depth).Select(e => (Expr)Expr.Proj(Name.Parse("Prod"), 0, e)))));

    private static readonly Arbitrary<Expr> Exprs = Gen.Sized(s => ExprGen(Math.Min(s, 30), 0)).ToArbitrary();

    [Fact]
    public void AbstractAndInstantiateAreInverse()
    {
        var closedUnderBinders = Exprs.Generator.Where(e => !e.HasLooseBVars).ToArbitrary();
        Prop.ForAll(closedUnderBinders, e => ExprOps.InstantiateRev(ExprOps.Abstract(e, FVars), FVars).Equals(e)).Check(Runs);
    }

    [Fact]
    public void LiftAndLowerAreInverse()
    {
        var cases = Zip(Exprs.Generator, Gen.Choose(0, 3), Gen.Choose(1, 3)).ToArbitrary();
        Prop.ForAll(cases, t =>
        {
            var (e, s, d) = t;
            var lifted = ExprOps.LiftLooseBVars(e, s, d);
            return ExprOps.LowerLooseBVars(lifted, s + d, d).Equals(e)
                && lifted.LooseBVarRange == (e.LooseBVarRange > s ? e.LooseBVarRange + d : e.LooseBVarRange);
        }).Check(Runs);
    }

    [Fact]
    public void InstantiatingAClosedValueRemovesTheVariable() =>
        Prop.ForAll(Exprs, e =>
        {
            var r = ExprOps.Instantiate(e, Expr.Const(Name.Parse("c")));
            return r.LooseBVarRange == Math.Max(0, e.LooseBVarRange - 1) && !ExprOps.HasLooseBVar(e, 0) == ExprOps.Instantiate(e, Expr.Prop).Equals(ExprOps.LowerLooseBVars(e, 1, 1));
        }).Check(Runs);

    [Fact]
    public void EqualityHashAndAlphaEqualityAgree()
    {
        var pairs = Zip(Exprs.Generator, Exprs.Generator).ToArbitrary();
        Prop.ForAll(pairs, p =>
        {
            var (a, b) = p;
            var renamed = ExprOps.Replace(a, (e, _) => e is LamExpr l ? Expr.Lam(Name.Parse("renamed"), l.BinderType, ExprOps.Replace(l.Body, (_, _) => null)) : null);
            return (!a.Equals(b) || a.AlphaEquals(b))
                && (!a.AlphaEquals(b) || a.GetHashCode() == b.GetHashCode())
                && a.AlphaEquals(renamed) && a.GetHashCode() == renamed.GetHashCode();
        }).Check(Runs);
    }

    [Fact]
    public void RandomTermsSurviveTheExportRoundTrip()
    {
        var closed = Exprs.Generator.Where(e => !e.HasLooseBVars && !e.HasFVar).ToArbitrary();
        Prop.ForAll(closed, e =>
        {
            var decl = new ConstantDeclaration(new AxiomInfo(Name.Parse("ax"), [], e, false));
            using var ms = new MemoryStream();
            using (var w = new Lean4ExportWriter(ms, leaveOpen: true))
            {
                w.Write(decl);
            }
            using var r = new Lean4ExportReader(new MemoryStream(ms.ToArray()));
            return r.ReadDeclarations().Single().Equals(decl);
        }).Check(Runs);
    }

    // ================================================================== Nat arithmetic

    private static readonly Expr NatConst = Expr.Const(Name.Parse("Nat"));

    private static Expr C(string name, params Level[] levels) => Expr.Const(Name.Parse(name), levels);

    private static readonly (string Name, Func<BigInteger, BigInteger, BigInteger> Op)[] NatOps =
    [
        ("Nat.add", (a, b) => a + b),
        ("Nat.mul", (a, b) => a * b),
        ("Nat.sub", (a, b) => a > b ? a - b : 0),
        ("Nat.div", (a, b) => b.IsZero ? 0 : a / b),
        ("Nat.mod", (a, b) => b.IsZero ? a : a % b),
        ("Nat.max", BigInteger.Max),
        ("Nat.min", BigInteger.Min),
    ];

    /// <summary>A closed Nat expression and its value.</summary>
    private static Gen<(Expr Term, BigInteger Value)> NatGen(int size) =>
        size <= 0
            ? Gen.OneOf(
                Gen.Choose(0, 12).Select(n => ((Expr)Expr.NatLit(n), (BigInteger)n)),
                Gen.Constant((C("Nat.zero"), BigInteger.Zero)))
            : Gen.Frequency(
                (2, NatGen(0)),
                (2, Defer(() => NatGen(size - 1).Select(x => ((Expr)Expr.App(C("Nat.succ"), x.Term), x.Value + 1)))),
                (4, Defer(() => Zip(Gen.Elements(NatOps), NatGen(size / 2), NatGen(size / 2))
                    .Select(t => (Expr.App(C(t.Item1.Name), t.Item2.Term, t.Item3.Term), t.Item1.Op(t.Item2.Value, t.Item3.Value))))));

    private static readonly Arbitrary<(Expr Term, BigInteger Value)> NatExprs = Gen.Sized(s => NatGen(Math.Min(s, 12))).ToArbitrary();

    [Fact]
    public void NatExpressionsReduceToTheirValue() =>
        Prop.ForAll(NatExprs, x => KernelThread.Run(() =>
        {
            var tc = new TypeChecker(initMedium.Env);
            var whnf = tc.Whnf(x.Term);
            // `Nat.zero` is a constructor, so it is already in weak head normal form.
            bool isValue = whnf.Equals(Expr.NatLit(x.Value)) || (x.Value.IsZero && whnf.Equals(C("Nat.zero")));
            return isValue && tc.IsDefEq(x.Term, Expr.NatLit(x.Value)) && tc.Infer(x.Term).AlphaEquals(NatConst);
        })).Check(Runs);

    [Fact]
    public void DefinitionalEqualityOfNatsIsSymmetricAndMatchesValues()
    {
        var pairs = Zip(NatExprs.Generator, NatExprs.Generator).ToArbitrary();
        Prop.ForAll(pairs, p => KernelThread.Run(() =>
        {
            var (a, b) = p;
            var ab = new TypeChecker(initMedium.Env).IsDefEq(a.Term, b.Term);
            var ba = new TypeChecker(initMedium.Env).IsDefEq(b.Term, a.Term);
            return ab == ba && ab == (a.Value == b.Value);
        })).Check(Runs);
    }

    // ================================================================== typed terms

    private enum Ty
    {
        Nat,
        Bool,
        ListNat,
        PairNatBool,
    }

    private static readonly Level L0 = Level.Zero;
    private static readonly Level L1 = Level.One;
    private static readonly Expr BoolConst = C("Bool");
    private static readonly Expr ListNat = Expr.App(C("List", L0), NatConst);
    private static readonly Expr PairNatBool = Expr.App(C("Prod", L0, L0), NatConst, BoolConst);

    private static Expr TypeOf(Ty t) => t switch
    {
        Ty.Nat => NatConst,
        Ty.Bool => BoolConst,
        Ty.ListNat => ListNat,
        _ => PairNatBool,
    };

    /// <summary>
    /// A well-typed term of type <paramref name="ty"/> in a context of bound variables
    /// (<paramref name="ctx"/>[0] is #0), built only by the typing rules.
    /// </summary>
    private static Gen<Expr> TypedGen(Ty ty, int size, Ty[] ctx)
    {
        var vars = Enumerable.Range(0, ctx.Length).Where(i => ctx[i] == ty).Select(i => (Expr)Expr.BVar(i)).ToArray();
        var leaves = new List<Gen<Expr>>();
        if (vars.Length > 0)
        {
            leaves.Add(Gen.Elements(vars));
        }
        leaves.Add(ty switch
        {
            Ty.Nat => Gen.Choose(0, 9).Select(n => (Expr)Expr.NatLit(n)),
            Ty.Bool => Gen.Elements(C("Bool.true"), C("Bool.false")),
            Ty.ListNat => Gen.Constant((Expr)Expr.App(C("List.nil", L0), NatConst)),
            _ => Zip(Gen.Choose(0, 9), Gen.Elements(C("Bool.true"), C("Bool.false")))
                .Select(p => Expr.App(C("Prod.mk", L0, L0), NatConst, BoolConst, Expr.NatLit(p.Item1), p.Item2)),
        });
        var leaf = Gen.OneOf(leaves);
        if (size <= 0)
        {
            return leaf;
        }
        Gen<Expr> Sub(Ty t, int s, Ty[]? c = null) => TypedGenLazy(t, s, c ?? ctx);
        int h = size / 2;
        // (fun x : σ => body) arg — exercises beta reduction and binders.
        var beta = Gen.Elements(Ty.Nat, Ty.Bool).SelectMany(sigma =>
            Zip(Sub(ty, h, [sigma, .. ctx]), Sub(sigma, h)).Select(p =>
                (Expr)Expr.App(Expr.Lam(Name.Parse("x"), TypeOf(sigma), p.Item1), p.Item2)));
        var cond = Zip(Sub(Ty.Bool, h), Sub(ty, h), Sub(ty, h)).Select(t =>
            (Expr)Expr.App(C("cond", L1), TypeOf(ty), t.Item1, t.Item2, t.Item3));
        var specific = ty switch
        {
            Ty.Nat => Gen.OneOf(
                Zip(Gen.Elements("Nat.add", "Nat.mul", "Nat.sub", "Nat.max"), Sub(Ty.Nat, h), Sub(Ty.Nat, h))
                    .Select(t => (Expr)Expr.App(C(t.Item1), t.Item2, t.Item3)),
                Sub(Ty.Nat, size - 1).Select(e => (Expr)Expr.App(C("Nat.succ"), e)),
                Sub(Ty.ListNat, size - 1).Select(l => (Expr)Expr.App(C("List.length", L0), NatConst, l)),
                Sub(Ty.PairNatBool, size - 1).Select(p => (Expr)Expr.App(C("Prod.fst", L0, L0), NatConst, BoolConst, p))),
            Ty.Bool => Gen.OneOf(
                Zip(Gen.Elements("Bool.and", "Bool.or"), Sub(Ty.Bool, h), Sub(Ty.Bool, h)).Select(t => (Expr)Expr.App(C(t.Item1), t.Item2, t.Item3)),
                Sub(Ty.Bool, size - 1).Select(b => (Expr)Expr.App(C("Bool.not"), b)),
                Zip(Gen.Elements("Nat.beq", "Nat.ble"), Sub(Ty.Nat, h), Sub(Ty.Nat, h)).Select(t => (Expr)Expr.App(C(t.Item1), t.Item2, t.Item3)),
                Sub(Ty.PairNatBool, size - 1).Select(p => (Expr)Expr.App(C("Prod.snd", L0, L0), NatConst, BoolConst, p))),
            Ty.ListNat => Gen.OneOf(
                Zip(Sub(Ty.Nat, h), Sub(Ty.ListNat, h)).Select(p => (Expr)Expr.App(C("List.cons", L0), NatConst, p.Item1, p.Item2)),
                Zip(Sub(Ty.ListNat, h), Sub(Ty.ListNat, h)).Select(p => (Expr)Expr.App(C("List.append", L0), NatConst, p.Item1, p.Item2)),
                Sub(Ty.ListNat, size - 1).Select(l => (Expr)Expr.App(C("List.reverse", L0), NatConst, l)),
                Zip(Sub(Ty.Nat, h, [Ty.Nat, .. ctx]), Sub(Ty.ListNat, h)).Select(p =>
                    (Expr)Expr.App(C("List.map", L0, L0), NatConst, NatConst, Expr.Lam(Name.Parse("n"), NatConst, p.Item1), p.Item2))),
            _ => Zip(Sub(Ty.Nat, h), Sub(Ty.Bool, h)).Select(p => (Expr)Expr.App(C("Prod.mk", L0, L0), NatConst, BoolConst, p.Item1, p.Item2)),
        };
        return Gen.Frequency((2, leaf), (4, specific), (1, beta), (1, cond));
    }

    private static Gen<Expr> TypedGenLazy(Ty ty, int size, Ty[] ctx) => size <= 0 ? TypedGen(ty, 0, ctx) : Defer(() => TypedGen(ty, size, ctx));

    private static readonly Arbitrary<(Ty Ty, Expr Term)> TypedTerms =
        Gen.Elements(Ty.Nat, Ty.Bool, Ty.ListNat, Ty.PairNatBool)
            .SelectMany(ty => Gen.Sized(s => TypedGen(ty, Math.Min(s, 10), [])).Select(e => (ty, e)))
            .ToArbitrary();

    [Fact]
    public void GeneratedWellTypedTermsAreAcceptedWithTheirType() =>
        Prop.ForAll(TypedTerms, t => KernelThread.Run(() =>
        {
            var tc = new TypeChecker(initMedium.Env);
            return tc.IsDefEq(tc.Check(t.Term, []), TypeOf(t.Ty));
        })).Check(Runs);

    [Fact]
    public void ReductionPreservesTypes() =>
        Prop.ForAll(TypedTerms, t => KernelThread.Run(() =>
        {
            var tc = new TypeChecker(initMedium.Env);
            var reduced = tc.Whnf(t.Term);
            return tc.IsDefEq(tc.Infer(reduced), TypeOf(t.Ty)) && tc.IsDefEq(reduced, t.Term);
        })).Check(Runs);

    [Fact]
    public void IllTypedApplicationsAreRejected() =>
        Prop.ForAll(TypedTerms, t => KernelThread.Run(() =>
        {
            // Applying Nat.succ to a term of any other type must fail to check.
            if (t.Ty == Ty.Nat)
            {
                return true;
            }
            try
            {
                new TypeChecker(initMedium.Env).Check(Expr.App(C("Nat.succ"), t.Term), []);
                return false;
            }
            catch (KernelException)
            {
                return true;
            }
        })).Check(Runs);
}
