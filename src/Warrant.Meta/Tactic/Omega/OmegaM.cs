using System.Collections.Immutable;
using System.Numerics;
using Warrant.Cic;
using static Warrant.Meta.Omega.OmegaExprs;

namespace Warrant.Meta.Omega;

/// <summary>
/// A delayed proof (Lean's <c>OmegaM Expr</c> thunks): built only once a contradiction is found, when every atom is
/// known, so that each proof cites the same atom list.
/// </summary>
internal delegate Expr Proof();

/// <summary>
/// The <c>OmegaM</c> state (Lean/Elab/Tactic/Omega/OmegaM.lean): the atoms met so far, in order, and a cache of the
/// linear combinations of visited terms. Both are immutable, so saving and restoring the state is O(1).
/// </summary>
/// <remarks>
/// Lean identifies atoms up to instances-transparency definitional equality (<c>canon</c>); Warrant identifies them up
/// to syntactic equality after instantiating metavariables, which can only make two equal atoms distinct, never the
/// converse.
/// </remarks>
internal sealed partial class OmegaM
{
    private ImmutableList<Expr> _atoms = [];
    private ImmutableDictionary<Expr, int> _atomIndex = ImmutableDictionary<Expr, int>.Empty;
    private ImmutableDictionary<Expr, (LinearCombo Lc, Proof Prf)> _cache = ImmutableDictionary<Expr, (LinearCombo, Proof)>.Empty;

    // The Coeffs.ofList literal of the current atoms, rebuilt when the atom list changes. It is keyed by the list itself,
    // not its length: a restored state can hold as many atoms as the one it replaced, in another order.
    private (ImmutableList<Expr> Atoms, Expr Expr)? _atomsCoeffs;

    public OmegaM(MetaM meta)
    {
        Meta = meta;
    }

    /// <summary>The Meta computation.</summary>
    public MetaM Meta { get; }

    /// <summary>The atoms, by index (Lean's <c>atoms</c>).</summary>
    public ImmutableList<Expr> Atoms => _atoms;

    /// <summary><c>atomsList</c>: the list literal of the atoms.</summary>
    public Expr AtomsList() => IntList(_atoms);

    /// <summary><c>atomsCoeffs</c>: <c>Coeffs.ofList</c> of the atoms.</summary>
    public Expr AtomsCoeffs()
    {
        if (_atomsCoeffs is not { } cached || !ReferenceEquals(cached.Atoms, _atoms))
        {
            cached = (_atoms, Expr.App(Expr.Const(OmegaNames.CoeffsOfList), AtomsList()));
            _atomsCoeffs = cached;
        }
        return cached.Expr;
    }

    private sealed record State(ImmutableList<Expr> Atoms, ImmutableDictionary<Expr, int> Index, ImmutableDictionary<Expr, (LinearCombo, Proof)> Cache);

    private State Save() => new(_atoms, _atomIndex, _cache);

    private void Restore(State s) => (_atoms, _atomIndex, _cache) = (s.Atoms, s.Index, s.Cache);

    /// <summary><c>commitWhen</c>: runs <paramref name="t"/> and keeps its changes only when it says so.</summary>
    public T CommitWhen<T>(Func<(T Value, bool Commit)> t)
    {
        var saved = Save();
        var (value, commit) = t();
        if (!commit)
        {
            Restore(saved);
        }
        return value;
    }

    /// <summary><c>withoutModifyingState</c>.</summary>
    public T WithoutModifyingState<T>(Func<T> t)
    {
        var saved = Save();
        try
        {
            return t();
        }
        finally
        {
            Restore(saved);
        }
    }

    /// <summary><c>natCast?</c>: <c>Expr.nat?</c>, also through <c>Nat.cast</c>.</summary>
    public static BigInteger? NatCast(Expr n) => AppOf(n, OmegaNames.NatCast, 3) is { } a ? Nat(a[2]) : Nat(n);

    /// <summary><c>groundNat?</c> (OmegaM.lean 124): a closed <c>Nat</c> term over <c>+ * - / ^</c> and numerals.</summary>
    public static BigInteger? GroundNat(Expr e)
    {
        if (AppOf(e, OmegaNames.NatCast, 3) is { } cast)
        {
            return GroundNat(cast[2]);
        }
        if (Binary(e) is var (op, x, y))
        {
            if (GroundNat(x) is not { } a || GroundNat(y) is not { } b)
            {
                return null;
            }
            return op switch
            {
                "+" => a + b,
                "*" => a * b,
                "-" => LeanInt.NatSub(a, b),
                "/" => LeanInt.NatDiv(a, b),
                _ => LeanInt.Pow(a, b),
            };
        }
        return Nat(e);
    }

    /// <summary><c>groundInt?</c> (OmegaM.lean 142): a closed <c>Int</c> term over <c>+ * - / ^</c> and numerals.</summary>
    public static BigInteger? GroundInt(Expr e)
    {
        if (AppOf(e, OmegaNames.NatCast, 3) is { } cast)
        {
            return GroundNat(cast[2]);
        }
        if (Binary(e) is var (op, x, y))
        {
            if (op == "^")
            {
                return GroundInt(x) is { } b && GroundNat(y) is { } n ? LeanInt.Pow(b, n) : null;
            }
            if (GroundInt(x) is not { } a || GroundInt(y) is not { } c)
            {
                return null;
            }
            return op switch
            {
                "+" => a + c,
                "*" => a * c,
                "-" => a - c,
                _ => LeanInt.EDiv(a, c),
            };
        }
        return Int(e);
    }

    /// <summary>The heterogeneous operators <c>groundNat?</c> and <c>groundInt?</c> evaluate, with their operands.</summary>
    private static (string Op, Expr X, Expr Y)? Binary(Expr e)
    {
        if (e.GetAppFn() is not ConstExpr c || e.GetAppNumArgs() != 6)
        {
            return null;
        }
        string? op = c.Name == OmegaNames.HAdd ? "+"
            : c.Name == OmegaNames.HMul ? "*"
            : c.Name == OmegaNames.HSub ? "-"
            : c.Name == OmegaNames.HDiv ? "/"
            : c.Name == OmegaNames.HPow ? "^"
            : null;
        if (op is null)
        {
            return null;
        }
        var args = e.GetAppArgs();
        return (op, args[4], args[5]);
    }

    /// <summary>
    /// <c>analyzeAtom</c> (OmegaM.lean 166): the facts a new atom brings. Lean's <c>Fin.val</c> and <c>BitVec.toNat</c>
    /// cases are left out (Warrant's goals have neither); Warrant adds <c>Int32.toInt</c> and <c>Int64.toInt</c>, whose
    /// range facts <c>Int32.le_toInt</c> and <c>Int32.toInt_lt</c> play the part <c>BitVec.isLt</c> plays for
    /// <c>BitVec.toNat</c> (KTD12).
    /// </summary>
    private ImmutableList<Expr> AnalyzeAtom(Expr e)
    {
        if (AppOf(e, OmegaNames.NatCast, 3) is { } cast && cast[0] == IntType)
        {
            var inner = cast[2];
            ImmutableList<Expr> r = [Expr.App(Expr.Const(OmegaNames.IntNatCastNonneg), inner)];
            if (AppOf(inner, OmegaNames.HSub, 6) is { } sub)
            {
                // splitNatSub (on by default): ((a - b : Nat) : Int) gives a dichotomy.
                r = Insert(r, Expr.App(Expr.Const(OmegaNames.IntOfNatSubDichotomy), sub[4], sub[5]));
            }
            else if (AppOf(inner, OmegaNames.IntNatAbs, 1) is { } abs)
            {
                r = Insert(r, Expr.App(Expr.Const(OmegaNames.IntLeNatAbs), abs[0]));
                r = Insert(r, Expr.App(Expr.Const(OmegaNames.IntNegLeNatAbs), abs[0]));
            }
            return r;
        }
        if (AppOf(e, OmegaNames.HDiv, 6) is { } div)
        {
            var (x, k) = (div[4], div[5]);
            if (NatCast(k) is not { } kv || kv.IsZero)
            {
                return [];
            }
            var zero = IntLit(0);
            return
            [
                Expr.App(Expr.Const(OmegaNames.IntMulEdivSelfLe), x, k, OmegaAppBuilder.MkDecideProof(Meta, IntNe(k, zero))),
                Expr.App(Expr.Const(OmegaNames.IntLtMulEdivSelfAdd), x, k, OmegaAppBuilder.MkDecideProof(Meta, IntLt(zero, k))),
            ];
        }
        if (AppOf(e, OmegaNames.HMod, 6) is { } mod)
        {
            return AnalyzeMod(mod[4], mod[5]);
        }
        if (AppOf(e, OmegaNames.Min, 4) is { } min)
        {
            return
            [
                Expr.App(Expr.Const(OmegaNames.IntMinLeLeft), min[2], min[3]),
                Expr.App(Expr.Const(OmegaNames.IntMinLeRight), min[2], min[3]),
            ];
        }
        if (AppOf(e, OmegaNames.Max, 4) is { } max)
        {
            return
            [
                Expr.App(Expr.Const(OmegaNames.IntLeMaxLeft), max[2], max[3]),
                Expr.App(Expr.Const(OmegaNames.IntLeMaxRight), max[2], max[3]),
            ];
        }
        if (AppOf(e, OmegaNames.Ite, 5) is { } ite)
        {
            return ite[0] == IntType
                ? [Expr.App(Expr.Const(OmegaNames.IteDisjunction, Level.Zero), ite[0], ite[1], ite[2], ite[3], ite[4])]
                : [];
        }
        if (AppOf(e, OmegaNames.Int32ToInt, 1) is { } i32)
        {
            return [Expr.App(Expr.Const(OmegaNames.Int32LeToInt), i32[0]), Expr.App(Expr.Const(OmegaNames.Int32ToIntLt), i32[0])];
        }
        if (AppOf(e, OmegaNames.Int64ToInt, 1) is { } i64)
        {
            return [Expr.App(Expr.Const(OmegaNames.Int64LeToInt), i64[0]), Expr.App(Expr.Const(OmegaNames.Int64ToIntLt), i64[0])];
        }
        return [];
    }

    /// <summary><c>analyzeAtom</c>'s <c>x % k</c> case: the remainder's bounds when <c>k</c> is a positive power.</summary>
    private ImmutableList<Expr> AnalyzeMod(Expr x, Expr k)
    {
        var zero = IntLit(0);
        if (AppOf(k, OmegaNames.HPow, 6) is { } pow)
        {
            var (b, exp) = (pow[4], pow[5]);
            if (NatCast(b) is not { } bv || bv.IsZero)
            {
                return [];
            }
            var bPos = OmegaAppBuilder.MkDecideProof(Meta, IntLt(zero, b));
            var powPos = Expr.App(Expr.Const(OmegaNames.IntPosPowOfPos), b, exp, bPos);
            return
            [
                Expr.App(Expr.Const(OmegaNames.IntEmodNonneg), x, k, Expr.App(Expr.Const(OmegaNames.IntNeOfGt), k, zero, powPos)),
                Expr.App(Expr.Const(OmegaNames.IntEmodLtOfPos), x, k, powPos),
            ];
        }
        if (AppOf(k, OmegaNames.NatCast, 3) is { } cast && cast[0] == IntType)
        {
            var k1 = cast[2];
            if (AppOf(k1, OmegaNames.HPow, 6) is { } npow)
            {
                var (b, exp) = (npow[4], npow[5]);
                if (NatCast(b) is not { } bv || bv.IsZero)
                {
                    return [];
                }
                var bPos = OmegaAppBuilder.MkDecideProof(Meta, NatLt(NatLit(0), b));
                var powPos = Expr.App(Expr.Const(OmegaNames.NatPowPos), b, exp, bPos);
                var castPos = Expr.App(Expr.Const(OmegaNames.IntOfNatPosOfPos), k1, powPos);
                return
                [
                    Expr.App(Expr.Const(OmegaNames.IntEmodNonneg), x, k, Expr.App(Expr.Const(OmegaNames.IntNeOfGt), k, zero, castPos)),
                    Expr.App(Expr.Const(OmegaNames.IntEmodLtOfPos), x, k, castPos),
                ];
            }
            // Since coercions are pushed inside %, record that (x : Int) % (y : Int) is non-negative.
            return AppOf(x, OmegaNames.NatCast, 3) is { } xc && xc[0] == IntType
                ? [Expr.App(Expr.Const(OmegaNames.IntEmodOfNatNonneg), xc[2], k)]
                : [];
        }
        return [];
    }

    /// <summary>Lean's <c>List.insert</c>: prepends unless already present.</summary>
    internal static ImmutableList<Expr> Insert(ImmutableList<Expr> list, Expr e) => list.Contains(e) ? list : list.Insert(0, e);

    /// <summary>
    /// <c>lookup</c> (OmegaM.lean 247): the atom's index, recording it if new; for a new atom, the facts it brings
    /// (null for an atom seen before).
    /// </summary>
    public (int Index, ImmutableList<Expr>? Facts) Lookup(Expr e)
    {
        e = Meta.InstantiateMVars(e);
        if (_atomIndex.TryGetValue(e, out var i))
        {
            return (i, null);
        }
        var facts = AnalyzeAtom(e);
        i = _atoms.Count;
        _atoms = _atoms.Add(e);
        _atomIndex = _atomIndex.Add(e, i);
        return (i, facts);
    }

    /// <summary>The cached linear combination of <paramref name="e"/>, if visited.</summary>
    public bool TryGetCached(Expr e, out (LinearCombo Lc, Proof Prf) entry) => _cache.TryGetValue(e, out entry);

    /// <summary>Caches the linear combination of <paramref name="e"/>.</summary>
    public void Cache(Expr e, LinearCombo lc, Proof prf) => _cache = _cache.SetItem(e, (lc, prf));
}
