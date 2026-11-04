using System.Collections.Immutable;
using System.Globalization;
using System.Numerics;
using System.Text;
using Warrant.Cic;
using Warrant.Kernel;
using Warrant.Meta.Omega;
using static Warrant.Meta.Omega.OmegaExprs;

namespace Warrant.Meta.Omega
{
    /// <summary>A linear combination, the proof that it evaluates at the atoms to the term, and the new facts.</summary>
    internal readonly record struct Linear(LinearCombo Lc, Proof Prf, ImmutableList<Expr> Facts);

    /// <summary>
    /// A partially processed <c>omega</c> context (Lean's <c>MetaProblem</c>, Lean/Elab/Tactic/Omega/Frontend.lean 59): the
    /// linear problem so far, the facts not yet processed, the disjunctions to split if nothing else works, and the facts
    /// already processed.
    /// </summary>
    internal sealed record MetaProblem
    {
        public Problem Problem { get; init; } = new();

        public ImmutableList<Expr> Facts { get; init; } = [];

        public ImmutableList<Expr> Disjunctions { get; init; } = [];

        public ImmutableHashSet<Expr> ProcessedFacts { get; init; } = [];
    }

    /// <summary>
    /// The <c>omega</c> frontend (Lean/Elab/Tactic/Omega/Frontend.lean): turns hypotheses into linear constraints over
    /// atoms, runs the solver, splits disjunctions, and builds the proof of <c>False</c>. Lean's configuration is fixed at
    /// its defaults (<c>splitDisjunctions</c>, <c>splitNatSub</c>, <c>splitNatAbs</c> and <c>splitMinMax</c> on). The
    /// <c>Fin</c>, <c>Prod</c>, <c>BitVec</c> and shift cases are left out: those terms become atoms.
    /// </summary>
    internal sealed partial class OmegaM
    {
        private MetaM M => Meta;

        // -------------------------------------------------------------- asLinearCombo

        /// <summary><c>mkEvalRflProof</c>: <c>rfl : e = lc.eval atoms</c>.</summary>
        private Proof MkEvalRflProof(Expr e, LinearCombo lc) => () =>
            OmegaAppBuilder.MkEqReflWithExpectedType(M, e, Expr.App(Expr.Const(OmegaNames.LinearComboEval), ToExpr(lc), AtomsCoeffs()));

        /// <summary><c>mkCoordinateEvalAtomsEq</c>: for the <c>n</c>-th atom <c>e</c>, <c>e = (coordinate n).eval atoms</c>.</summary>
        private Proof MkCoordinateEvalAtomsEq(Expr e, int n) => () =>
        {
            if (n < 10)
            {
                var tail = IntList(Atoms.Skip(n + 1));
                var args = Atoms.Take(n + 1).Append(tail).ToArray();
                return OmegaAppBuilder.MkEqSymm(M, Expr.App(Expr.Const(OmegaNames.CoordinateEval(n)), args));
            }
            var atoms = AtomsCoeffs();
            var nExpr = NatLit(n);
            var eq = OmegaAppBuilder.MkEqReflWithExpectedType(M, e, Expr.App(Expr.Const(OmegaNames.CoeffsGet), atoms, nExpr));
            return OmegaAppBuilder.MkEqTrans(M, eq,
                OmegaAppBuilder.MkEqSymm(M, Expr.App(Expr.Const(OmegaNames.LinearComboCoordinateEval), nExpr, atoms)));
        };

        /// <summary><c>mkAtomLinearCombo</c>.</summary>
        private Linear MkAtomLinearCombo(Expr e)
        {
            var (n, facts) = Lookup(e);
            return new(LinearCombo.Coordinate(n), MkCoordinateEvalAtomsEq(e, n), facts ?? []);
        }

        /// <summary><c>asLinearCombo</c> (Frontend.lean 105): with the cache of visited terms.</summary>
        public Linear AsLinearCombo(Expr e)
        {
            if (TryGetCached(e, out var hit))
            {
                return new(hit.Lc, hit.Prf, []);
            }
            var r = AsLinearComboImpl(e);
            Cache(e, r.Lc, r.Prf);
            return r;
        }

        /// <summary>
        /// <c>asLinearComboImpl</c> (Frontend.lean 131): a linear combination of atoms equal to <paramref name="e"/>, pushing
        /// coercions inward and unfolding <c>%</c>, <c>min</c> and <c>max</c>.
        /// </summary>
        private Linear AsLinearComboImpl(Expr e)
        {
            M.Budget.Tick();
            if (GroundInt(e) is { } i)
            {
                var lc = LinearCombo.Constant(i);
                return new(lc, MkEvalRflProof(e, lc), []);
            }
            if (e is FVarExpr fv)
            {
                return M.FindLocalDecl(fv.Id)?.GetValue() is { } v
                    ? Rewrite(OmegaAppBuilder.MkEqReflWithExpectedType(M, e, v))
                    : MkAtomLinearCombo(e);
            }
            if (AppOf(e, OmegaNames.HAdd, 6) is { } add)
            {
                return Binary(add[4], add[5], OmegaNames.IntAddCongr, OmegaNames.LinearComboAddEval, (l1, l2) => l1 + l2);
            }
            if (AppOf(e, OmegaNames.HSub, 6) is { } sub)
            {
                return Binary(sub[4], sub[5], OmegaNames.IntSubCongr, OmegaNames.LinearComboSubEval, (l1, l2) => l1 - l2);
            }
            if (AppOf(e, OmegaNames.NegNeg, 3) is { } neg)
            {
                var (l, prf, facts) = AsLinearCombo(neg[2]);
                Proof prf1 = () => OmegaAppBuilder.MkEqTrans(M,
                    OmegaAppBuilder.MkAppM(M, OmegaNames.IntNegCongr, prf()),
                    OmegaAppBuilder.MkEqSymm(M, Expr.App(Expr.Const(OmegaNames.LinearComboNegEval), ToExpr(l), AtomsCoeffs())));
                return new(-l, prf1, facts);
            }
            if (AppOf(e, OmegaNames.HMul, 6) is { } mul)
            {
                // If the product is not linear, revert the state, so the factors' facts are still reported when they are
                // visited elsewhere.
                var r = CommitWhen<Linear?>(() =>
                {
                    var (xl, xprf, xfacts) = AsLinearCombo(mul[4]);
                    var (yl, yprf, yfacts) = AsLinearCombo(mul[5]);
                    if (!xl.Coeffs.IsZero && !yl.Coeffs.IsZero)
                    {
                        return (null, false);
                    }
                    Proof prf = () =>
                    {
                        var isZero = Expr.App(Expr.Const(OmegaNames.Or),
                            Expr.App(Expr.Const(OmegaNames.CoeffsIsZero), ToExpr(xl.Coeffs)),
                            Expr.App(Expr.Const(OmegaNames.CoeffsIsZero), ToExpr(yl.Coeffs)));
                        var h = OmegaAppBuilder.MkDecideProof(M, isZero);
                        var mulEval = Expr.App(Expr.Const(OmegaNames.LinearComboMulEval), ToExpr(xl), ToExpr(yl), AtomsCoeffs(), h);
                        return OmegaAppBuilder.MkEqTrans(M,
                            OmegaAppBuilder.MkAppM(M, OmegaNames.IntMulCongr, xprf(), yprf()),
                            OmegaAppBuilder.MkEqSymm(M, mulEval));
                    };
                    return (new Linear(LinearCombo.Mul(xl, yl), prf, xfacts.AddRange(yfacts)), true);
                });
                return r ?? MkAtomLinearCombo(e);
            }
            if (AppOf(e, OmegaNames.HMod, 6) is { } mod)
            {
                if (GroundNat(mod[5]) is { } k)
                {
                    var kExpr = IntLit(k);
                    return Rewrite(Expr.App(Expr.Const(OmegaNames.IntEmodDef), mod[4], kExpr));
                }
                return MkAtomLinearCombo(e);
            }
            if (AppOf(e, OmegaNames.HDiv, 6) is { } div)
            {
                var x = div[4];
                switch (GroundInt(div[5]))
                {
                    case { IsZero: true }:
                        return Rewrite(Expr.App(Expr.Const(OmegaNames.IntEdivZero), x));
                    case { } d:
                        return d.Sign < 0
                            ? Rewrite(Expr.App(Expr.Const(OmegaNames.IntEdivNeg), x, IntLit(-d)))
                            : MkAtomLinearCombo(IntDiv(x, IntLit(d)));
                    default:
                        return MkAtomLinearCombo(e);
                }
            }
            if (AppOf(e, OmegaNames.Min, 4) is { } min)
            {
                return Rewrite(Expr.App(Expr.Const(OmegaNames.IntMinDef), min[2], min[3]));
            }
            if (AppOf(e, OmegaNames.Max, 4) is { } max)
            {
                return Rewrite(Expr.App(Expr.Const(OmegaNames.IntMaxDef), max[2], max[3]));
            }
            if (AppOf(e, OmegaNames.HPow, 6) is { } pow)
            {
                return Succ(pow[5]) is { } k1 && GroundInt(pow[4]) is not null
                    ? Rewrite(Expr.App(Expr.Const(OmegaNames.IntPowSucc), pow[4], k1))
                    : MkAtomLinearCombo(e);
            }
            if (AppOf(e, OmegaNames.NatCast, 3) is { } cast)
            {
                return cast[0] == IntType ? HandleNatCast(e, cast[1], cast[2]) : MkAtomLinearCombo(e);
            }
            if (AppOf(e, OmegaNames.IntNegSucc, 1) is { } negSucc)
            {
                return Rewrite(Expr.App(Expr.Const(OmegaNames.IntNegSuccEq), negSucc[0]));
            }
            return MkAtomLinearCombo(e);
        }

        /// <summary>The <c>+</c> and <c>-</c> cases: the congruence of the two proofs, then the evaluation lemma.</summary>
        private Linear Binary(Expr e1, Expr e2, Name congr, Name evalLemma, Func<LinearCombo, LinearCombo, LinearCombo> op)
        {
            var (l1, prf1, facts1) = AsLinearCombo(e1);
            var (l2, prf2, facts2) = AsLinearCombo(e2);
            Proof prf = () => OmegaAppBuilder.MkEqTrans(M,
                OmegaAppBuilder.MkAppM(M, congr, prf1(), prf2()),
                OmegaAppBuilder.MkEqSymm(M, Expr.App(Expr.Const(evalLemma), ToExpr(l1), ToExpr(l2), AtomsCoeffs())));
            return new(op(l1, l2), prf, facts1.AddRange(facts2));
        }

        /// <summary><c>succ?</c>: <c>n + 1</c> or <c>n.succ</c>.</summary>
        private static Expr? Succ(Expr e)
        {
            if (AppOf(e, OmegaNames.NatSucc, 1) is { } s)
            {
                return s[0];
            }
            return AppOf(e, OmegaNames.HAdd, 6) is { } add && add[5] == NatLit(1) ? add[4] : null;
        }

        /// <summary>
        /// <c>rewrite</c>: <paramref name="rw"/> proves <c>lhs = rhs</c>, where <c>lhs</c> is the term being translated; the
        /// linear combination of <c>rhs</c>, with the proof through <paramref name="rw"/>.
        /// </summary>
        private Linear Rewrite(Expr rw)
        {
            var type = M.InstantiateMVars(M.InferType(rw));
            if (AppOf(type, OmegaNames.Eq, 3) is not { } eq)
            {
                throw new MetaException("Invalid rewrite rule in 'asLinearCombo'");
            }
            var (lc, prf, facts) = AsLinearCombo(eq[2]);
            return new(lc, () => OmegaAppBuilder.MkEqTrans(M, rw, prf()), facts);
        }

        /// <summary><c>handleNatCast</c> (Frontend.lean 255): pushes <c>((n : Nat) : Int)</c> inward.</summary>
        private Linear HandleNatCast(Expr e, Expr i, Expr n)
        {
            if (n is FVarExpr fv)
            {
                return M.FindLocalDecl(fv.Id)?.GetValue() is { } v
                    ? Rewrite(OmegaAppBuilder.MkEqReflWithExpectedType(M, e, Expr.App(Expr.Const(OmegaNames.NatCast, Level.Zero), IntType, i, v)))
                    : MkAtomLinearCombo(e);
            }
            if (AppOf(n, OmegaNames.NatSucc, 1) is { } succ)
            {
                return Rewrite(Expr.App(Expr.Const(OmegaNames.IntNatCastSucc), succ[0]));
            }
            if (AppOf(n, OmegaNames.HAdd, 6) is { } add)
            {
                return Rewrite(Expr.App(Expr.Const(OmegaNames.IntNatCastAdd), add[4], add[5]));
            }
            if (AppOf(n, OmegaNames.HMul, 6) is { } mul)
            {
                var (lc, prf, facts) = Rewrite(Expr.App(Expr.Const(OmegaNames.IntNatCastMul), mul[4], mul[5]));
                // The product is non-negative.
                return new(lc, prf, Insert(facts, Expr.App(Expr.Const(OmegaNames.IntOfNatMulNonneg), mul[4], mul[5])));
            }
            if (AppOf(n, OmegaNames.HDiv, 6) is { } div)
            {
                return Rewrite(Expr.App(Expr.Const(OmegaNames.IntNatCastEdiv), div[4], div[5]));
            }
            if (AppOf(n, OmegaNames.OfNat, 3) is { } lit)
            {
                return Rewrite(Expr.App(Expr.Const(OmegaNames.IntNatCastOfNat), lit[1]));
            }
            if (AppOf(n, OmegaNames.HMod, 6) is { } mod)
            {
                return Rewrite(Expr.App(Expr.Const(OmegaNames.IntNatCastEmod), mod[4], mod[5]));
            }
            if (AppOf(n, OmegaNames.HSub, 6) is { } sub && AppOf(sub[4], OmegaNames.HSub, 6) is { } inner)
            {
                return Rewrite(Expr.App(Expr.Const(OmegaNames.IntOfNatSubSub), inner[4], inner[5], sub[5]));
            }
            if (AppOf(n, OmegaNames.HPow, 6) is { } pow)
            {
                return GroundNat(pow[4]) is not null
                    ? Rewrite(Expr.App(Expr.Const(OmegaNames.IntOfNatPow), pow[4], pow[5]))
                    : MkAtomLinearCombo(e);
            }
            if (AppOf(n, OmegaNames.Min, 4) is { } min)
            {
                return Rewrite(Expr.App(Expr.Const(OmegaNames.IntOfNatMin), min[2], min[3]));
            }
            if (AppOf(n, OmegaNames.Max, 4) is { } max)
            {
                return Rewrite(Expr.App(Expr.Const(OmegaNames.IntOfNatMax), max[2], max[3]));
            }
            if (AppOf(n, OmegaNames.IntToNat, 1) is { } toNat)
            {
                return Rewrite(Expr.App(Expr.Const(OmegaNames.IntToNatEqMax), toNat[0]));
            }
            if (AppOf(n, OmegaNames.IntNatAbs, 1) is { } natAbs)
            {
                return Rewrite(Expr.App(Expr.Const(OmegaNames.IntOfNatNatAbs), natAbs[0]));
            }
            return MkAtomLinearCombo(e);
        }

        // -------------------------------------------------------------- facts

        /// <summary><c>MetaProblem.addIntEquality</c> (Frontend.lean 346): adds <c>x = 0</c>, given <c>h</c>.</summary>
        private MetaProblem AddIntEquality(MetaProblem p, Expr h, Expr x)
        {
            var (lc, prf, facts) = AsLinearCombo(x);
            var newFacts = facts.Where(f => !p.ProcessedFacts.Contains(f));
            var problem = p.Problem.AddEquality(this, lc.Const, lc.Coeffs,
                () => OmegaAppBuilder.MkEqTrans(M, OmegaAppBuilder.MkEqSymm(M, prf()), h));
            return p with { Facts = p.Facts.InsertRange(0, newFacts), Problem = problem.SolveEqualities(this) };
        }

        /// <summary><c>MetaProblem.addIntInequality</c> (Frontend.lean 361): adds <c>0 ≤ y</c>, given <c>h</c>.</summary>
        private MetaProblem AddIntInequality(MetaProblem p, Expr h, Expr y)
        {
            var (lc, prf, facts) = AsLinearCombo(y);
            var newFacts = facts.Where(f => !p.ProcessedFacts.Contains(f));
            var problem = p.Problem.AddInequality(this, lc.Const, lc.Coeffs,
                () => OmegaAppBuilder.MkAppM(M, OmegaNames.LeOfLeOfEq, h, prf()));
            return p with { Facts = p.Facts.InsertRange(0, newFacts), Problem = problem.SolveEqualities(this) };
        }

        /// <summary><c>pushNot</c> (Frontend.lean 372): from <c>h : ¬ P</c>, a more useful fact.</summary>
        private Expr? PushNot(Expr h, Expr p)
        {
            p = M.WhnfR(p);
            if (p is ForallExpr pi)
            {
                return !pi.Body.HasLooseBVars && M.IsProp(pi.BinderType) && M.IsProp(pi.Body)
                    ? Expr.App(Expr.Const(OmegaNames.DecidableAndNotOfNotImp), pi.BinderType, pi.Body, PropDecidable(pi.BinderType), h)
                    : null;
            }
            if (p is not AppExpr)
            {
                return null;
            }
            if (AppOf(p, OmegaNames.LT, 4) is { } lt)
            {
                return ByType(lt[0], OmegaNames.NatLeOfNotLt, OmegaNames.IntLeOfNotLt, lt[2], lt[3], h);
            }
            if (AppOf(p, OmegaNames.LE, 4) is { } le)
            {
                return ByType(le[0], OmegaNames.NatLtOfNotLe, OmegaNames.IntLtOfNotLe, le[2], le[3], h);
            }
            if (AppOf(p, OmegaNames.Eq, 3) is { } eq)
            {
                return ByType(eq[0], OmegaNames.NatLtOrGtOfNe, OmegaNames.IntLtOrGtOfNe, eq[1], eq[2], h);
            }
            if (AppOf(p, OmegaNames.Dvd, 4) is { } dvd)
            {
                // For Int this introduces a disjunction that could be avoided by checking k ≠ 0.
                return ByType(dvd[0], OmegaNames.NatEmodPosOfNotDvd, OmegaNames.IntEmodPosOfNotDvd, dvd[2], dvd[3], h);
            }
            if (AppOf(p, OmegaNames.Not, 1) is { } not)
            {
                return Expr.App(Expr.Const(OmegaNames.DecidableOfNotNot), not[0], PropDecidable(not[0]), h);
            }
            if (AppOf(p, OmegaNames.And, 2) is { } and)
            {
                return Expr.App(Expr.Const(OmegaNames.DecidableOrNotNotOfNotAnd), and[0], and[1], PropDecidable(and[0]), PropDecidable(and[1]), h);
            }
            if (AppOf(p, OmegaNames.Or, 2) is { } or)
            {
                return Expr.App(Expr.Const(OmegaNames.AndNotNotOfNotOr), or[0], or[1], h);
            }
            if (AppOf(p, OmegaNames.Iff, 2) is { } iff)
            {
                return Expr.App(Expr.Const(OmegaNames.DecidableAndNotOrNotAndOfNotIff), iff[0], iff[1], PropDecidable(iff[0]), PropDecidable(iff[1]), h);
            }
            return null;
        }

        /// <summary>The lemma for <c>Nat</c> or for <c>Int</c>, applied to <c>x y h</c>; null at any other type.</summary>
        private static Expr? ByType(Expr type, Name natLemma, Name intLemma, Expr x, Expr y, Expr h) =>
            type == NatType ? Expr.App(Expr.Const(natLemma), x, y, h)
            : type == IntType ? Expr.App(Expr.Const(intLemma), x, y, h)
            : null;

        /// <summary>
        /// <c>MetaProblem.addFact</c> (Frontend.lean 425): extracts the linear facts in <paramref name="h"/>'s type, and
        /// how many it found.
        /// </summary>
        private (MetaProblem, int) AddFact(MetaProblem p, Expr h)
        {
            M.Budget.Tick();
            if (!p.Problem.Possible)
            {
                return (p, 0);
            }
            var t = M.InstantiateMVars(M.WhnfR(M.InferType(h)));
            if (t is ForallExpr pi)
            {
                return !pi.Body.HasLooseBVars && M.IsProp(pi.BinderType) && M.IsProp(pi.Body)
                    ? AddFact(p, Expr.App(Expr.Const(OmegaNames.DecidableNotOrOfImp), pi.BinderType, pi.Body, PropDecidable(pi.BinderType), h))
                    : (p, 0);
            }
            if (t is not AppExpr)
            {
                return (p, 0);
            }
            if (AppOf(t, OmegaNames.Eq, 3) is { } eq)
            {
                var (type, x, y) = (eq[0], eq[1], eq[2]);
                if (type == IntType)
                {
                    return Int(y) is { IsZero: true }
                        ? (AddIntEquality(p, h, x), 1)
                        : AddFact(p, Expr.App(Expr.Const(OmegaNames.IntSubEqZeroOfEq), x, y, h));
                }
                return type == NatType ? AddFact(p, Expr.App(Expr.Const(OmegaNames.IntOfNatCongr), x, y, h)) : (p, 0);
            }
            if (AppOf(t, OmegaNames.LE, 4) is { } le)
            {
                var (type, x, y) = (le[0], le[2], le[3]);
                if (type == IntType)
                {
                    return Int(x) is { IsZero: true }
                        ? (AddIntInequality(p, h, y), 1)
                        : AddFact(p, Expr.App(Expr.Const(OmegaNames.IntSubNonnegOfLe), y, x, h));
                }
                return type == NatType ? AddFact(p, Expr.App(Expr.Const(OmegaNames.IntOfNatLeOfLe), x, y, h)) : (p, 0);
            }
            if (AppOf(t, OmegaNames.LT, 4) is { } lt)
            {
                return ByType(lt[0], OmegaNames.IntOfNatLtOfLt, OmegaNames.IntAddOneLeOfLt, lt[2], lt[3], h) is { } h1 ? AddFact(p, h1) : (p, 0);
            }
            if (AppOf(t, OmegaNames.GT, 4) is { } gt)
            {
                return ByType(gt[0], OmegaNames.NatLtOfGt, OmegaNames.IntLtOfGt, gt[2], gt[3], h) is { } h1 ? AddFact(p, h1) : (p, 0);
            }
            if (AppOf(t, OmegaNames.GE, 4) is { } ge)
            {
                return ByType(ge[0], OmegaNames.NatLeOfGe, OmegaNames.IntLeOfGe, ge[2], ge[3], h) is { } h1 ? AddFact(p, h1) : (p, 0);
            }
            if (AppOf(t, OmegaNames.Ne, 3) is { } ne)
            {
                return ByType(ne[0], OmegaNames.NatLtOrGtOfNe, OmegaNames.IntLtOrGtOfNe, ne[1], ne[2], h) is { } h1 ? AddFact(p, h1) : (p, 0);
            }
            if (AppOf(t, OmegaNames.Dvd, 4) is { } dvd)
            {
                return ByType(dvd[0], OmegaNames.NatModEqZeroOfDvd, OmegaNames.IntEmodEqZeroOfDvd, dvd[2], dvd[3], h) is { } h1 ? AddFact(p, h1) : (p, 0);
            }
            if (AppOf(t, OmegaNames.Not, 1) is { } not)
            {
                return PushNot(h, not[0]) is { } h1 ? AddFact(p, h1) : (p, 0);
            }
            if (AppOf(t, OmegaNames.And, 2) is { } and)
            {
                var (p1, n1) = AddFact(p, Expr.App(Expr.Const(OmegaNames.AndLeft), and[0], and[1], h));
                var (p2, n2) = AddFact(p1, Expr.App(Expr.Const(OmegaNames.AndRight), and[0], and[1], h));
                return (p2, n1 + n2);
            }
            if (AppOf(t, OmegaNames.Exists, 2) is { } ex)
            {
                return AddFact(p, Expr.App(Expr.Const(OmegaNames.ExistsChooseSpec, M.GetLevel(ex[0])), ex[0], ex[1], h));
            }
            if (AppOf(t, OmegaNames.Subtype, 2) is { } st)
            {
                return AddFact(p, Expr.App(Expr.Const(OmegaNames.SubtypeProperty, M.GetLevel(st[0])), st[0], st[1], h));
            }
            if (AppOf(t, OmegaNames.Iff, 2) is { } iff)
            {
                return AddFact(p, Expr.App(Expr.Const(OmegaNames.DecidableAndOrNotAndNotOfIff), iff[0], iff[1], PropDecidable(iff[1]), h));
            }
            if (AppOf(t, OmegaNames.Or, 2) is not null)
            {
                return (p with { Disjunctions = Insert(p.Disjunctions, h) }, 1);
            }
            return (p, 0);
        }

        /// <summary><c>processFacts</c> (Frontend.lean 515): processes every pending fact, and counts the new ones.</summary>
        private (MetaProblem, int) ProcessFacts(MetaProblem p)
        {
            int total = 0;
            while (!p.Facts.IsEmpty)
            {
                var h = p.Facts[0];
                var rest = p.Facts.RemoveAt(0);
                if (p.ProcessedFacts.Contains(h))
                {
                    p = p with { Facts = rest };
                    continue;
                }
                var (p1, n) = AddFact(p with { Facts = rest, ProcessedFacts = p.ProcessedFacts.Add(h) }, h);
                p = p1;
                total += n;
            }
            return (p, total);
        }

        // -------------------------------------------------------------- the failure message

        /// <summary><c>formatErrorMessage</c> (Frontend.lean 533).</summary>
        private string FormatErrorMessage(Problem p)
        {
            if (!p.Possible)
            {
                return "it is trivially solvable";
            }
            if (p.IsEmpty)
            {
                return "No usable constraints found. You may need to unfold definitions so `omega` can see linear arithmetic facts about `Nat` and `Int`, which may also involve multiplication, division, and modular remainder by constants.";
            }
            var atoms = Atoms;
            var mask = new bool[atoms.Count];
            foreach (var c in p.Order)
            {
                for (int i = 0; i < c.Length; i++)
                {
                    if (!c.Values[i].IsZero)
                    {
                        mask[i] = true;
                    }
                }
            }
            var names = VarNames(mask);
            var sb = new StringBuilder("a possible counterexample may satisfy the constraints\n");
            sb.Append(string.Join("\n", p.Order.Order().Select(c => "  " + PrettyConstraint(PrettyCoeffs(names, c), p.Constraints[c].Constraint))));
            sb.Append("\nwhere\n");
            sb.Append(string.Join("\n", Enumerable.Range(0, atoms.Count).Where(i => mask[i]).Select(i => $" {names[i]} := {M.Pp(atoms[i])}")));
            return sb.ToString();
        }

        /// <summary><c>varNameOf</c>: <c>a</c> … <c>z</c>, then <c>a_1</c> ….</summary>
        private static string VarNameOf(int i) =>
            ((char)('a' + (i % 26))).ToString() + (i < 26 ? "" : "_" + (i / 26).ToString(CultureInfo.InvariantCulture));

        /// <summary><c>varNames</c>: names for the mentioned atoms that no constant or hypothesis already has.</summary>
        private string[] VarNames(bool[] mask)
        {
            var names = new string[mask.Length];
            int next = 0;
            for (int i = 0; i < mask.Length; i++)
            {
                if (!mask[i])
                {
                    names[i] = "(masked)";
                    continue;
                }
                while (InScope(VarNameOf(next)))
                {
                    next++;
                }
                names[i] = VarNameOf(next++);
            }
            return names;
        }

        private bool InScope(string s)
        {
            var n = Name.From(s);
            return M.Env.Find(n) is not null || M.LCtx.FindFromUserName(n) is not null;
        }

        private static string PrettyConstraint(string e, Constraint c) => (c.Lower, c.Upper) switch
        {
            (null, null) => $"{e} is unconstrained",
            (null, { } y) => $"{e} ≤ {y}",
            ({ } x, null) => $"{e} ≥ {x}",
            ({ } x, { } y) => y < x ? "∅" : $"{x} ≤ {e} ≤ {y}",
        };

        private static string PrettyCoeffs(string[] names, Coeffs coeffs)
        {
            var sb = new StringBuilder();
            int j = 0;
            for (int i = 0; i < coeffs.Length; i++)
            {
                var c = coeffs.Values[i];
                if (c.IsZero)
                {
                    continue;
                }
                sb.Append(j > 0 ? (c.Sign > 0 ? " + " : " - ") : (c.Sign > 0 ? "" : "- "));
                var abs = BigInteger.Abs(c);
                sb.Append(abs.IsOne ? names[i] : $"{abs.ToString(CultureInfo.InvariantCulture)}*{names[i]}");
                j++;
            }
            return sb.ToString();
        }

        // -------------------------------------------------------------- the algorithm

        /// <summary>
        /// <c>splitDisjunction</c> (Frontend.lean 620): splits the first disjunction whose left side brings a new fact, and
        /// proves <c>False</c> in both branches by <c>Or.elim</c>.
        /// </summary>
        private Expr SplitDisjunction(MetaProblem m, MVarId goal)
        {
            while (true)
            {
                if (m.Disjunctions.IsEmpty)
                {
                    throw new TacticException("omega", goal, "omega could not prove the goal:\n" + FormatErrorMessage(m.Problem));
                }
                var h = m.Disjunctions[0];
                var t = m.Disjunctions.RemoveAt(0);
                var hType = M.WhnfD(M.InferType(h));
                if (AppOf(hType, OmegaNames.Or, 2) is not { } or)
                {
                    throw new MetaException($"Unexpected disjunction {M.Pp(hType)}");
                }
                var (type1, type2) = (or[0], or[1]);
                var p1 = WithoutModifyingState(() => M.WithLocalDeclD(Name.From("h₁"), type1, h1 =>
                {
                    var (m1, n) = ProcessFacts(m with { Facts = [h1], Disjunctions = t });
                    return n > 0 ? M.MkLambdaFVars([h1], OmegaImpl(m1, goal)) : null;
                }));
                if (p1 is null)
                {
                    // No new facts found.
                    m = m with { Disjunctions = t };
                    continue;
                }
                return M.WithLocalDeclD(Name.From("h₂"), type2, h2 =>
                {
                    var p2 = M.MkLambdaFVars([h2], OmegaImpl(m with { Facts = [h2], Disjunctions = t }, goal));
                    return Expr.App(Expr.Const(OmegaNames.OrElim), type1, type2, False, h, p1, p2);
                });
            }
        }

        /// <summary><c>omegaImpl</c> (Frontend.lean 649): processes the facts, eliminates, and splits if that is not enough.</summary>
        public Expr OmegaImpl(MetaProblem m, MVarId goal)
        {
            (m, _) = ProcessFacts(m);
            var p = m.Problem;
            var p1 = p.Possible ? p.Elimination(this) : p;
            if (p1.Possible)
            {
                return SplitDisjunction(m, goal);
            }
            return M.InstantiateMVars(p1.ProveFalse!());
        }
    }
}

namespace Warrant.Meta
{
    public sealed partial class MetaM
    {
        /// <summary>
        /// The <c>omega</c> decision procedure on a goal (Lean's <c>omegaTactic</c>, Lean/Elab/Tactic/Omega/Frontend.lean
        /// 680, KTD12): turns the goal into <c>False</c> (<see cref="FalseOrByContra"/>), collects every hypothesis, and
        /// assigns the goal a proof of <c>False</c> from the linear facts over <c>Int</c> and <c>Nat</c> among them. Lean's
        /// <c>omega</c> tactic first tries <c>assumption</c>; that, and the omega-prep step, are <see cref="OmegaTactic"/>'s.
        /// </summary>
        /// <remarks>
        /// The proof is reflective: it restates the derivation with <c>Init/Omega</c>'s lemmas on literal lists, which the
        /// kernel recomputes. Lean hides it in an auxiliary theorem; Warrant puts it in the goal's assignment.
        /// </remarks>
        /// <param name="mvarId">The goal.</param>
        /// <exception cref="TacticException">
        /// <c>omega</c> found no contradiction: the message is Lean's, <c>omega could not prove the goal:</c> followed by
        /// the constraints a counterexample may satisfy, with the atoms printed by the goal printer.
        /// </exception>
        public void Omega(MVarId mvarId)
        {
            if (FalseOrByContra(mvarId) is not { } g)
            {
                return;
            }
            WithContext(g, () =>
            {
                var hyps = LCtx.Decls.Where(d => !d.IsImplementationDetail).Select(d => (Expr)d.ToExpr()).ToImmutableList();
                var proof = new OmegaM(this).OmegaImpl(new MetaProblem { Facts = hyps }, g);
                Assign(g, proof);
                return 0;
            });
        }
    }
}
