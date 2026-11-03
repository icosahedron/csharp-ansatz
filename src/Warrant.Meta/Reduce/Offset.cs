using System.Numerics;
using Warrant.Cic;

namespace Warrant.Meta;

// Nat offsets `e + k` and numerals in unification (a port of Lean 4.35.0's Lean/Meta/Offset.lean and
// the structural instance tests of Lean/Meta/NatInstTesters.lean).
public sealed partial class MetaM
{
    private static readonly Name OfNatName = Name.From("OfNat", "ofNat");
    private static readonly Name AddAdd = Name.From("Add", "add");
    private static readonly Name NatSubName = Name.From("Nat", "sub");
    private static readonly Name SubSub = Name.From("Sub", "sub");
    private static readonly Name HSubHSub = Name.From("HSub", "hSub");
    private static readonly Name MulMul = Name.From("Mul", "mul");
    private static readonly Name HMulHMul = Name.From("HMul", "hMul");
    private static readonly Name DivDiv = Name.From("Div", "div");
    private static readonly Name HDivHDiv = Name.From("HDiv", "hDiv");
    private static readonly Name ModMod = Name.From("Mod", "mod");
    private static readonly Name HModHMod = Name.From("HMod", "hMod");
    private static readonly Name NatPowPow = Name.From("NatPow", "pow");
    private static readonly Name PowPow = Name.From("Pow", "pow");
    private static readonly Name HPowHPow = Name.From("HPow", "hPow");

    // Lean's `match_expr`: the arguments of `e` if it is `name` applied to exactly `arity` arguments.
    private static Expr[]? MatchApp(Expr e, Name name, int arity) =>
        e.GetAppFn() is ConstExpr c && c.Name == name && e.GetAppNumArgs() == arity ? e.GetAppArgs() : null;

    private static bool IsConstApp(Expr e, string name, int arity, out Expr[] args)
    {
        args = MatchApp(e, Name.Parse(name), arity) ?? [];
        return args.Length == arity && e.GetAppFn() is ConstExpr;
    }

    // Lean's Structural.isInst*Nat: syntactic tests of the canonical Nat instances.
    private static bool IsInstOfNatNat(Expr e) => IsConstApp(e, "instOfNatNat", 1, out _);

    private static bool IsInstNamed(Expr e, string name) => e is ConstExpr c && c.Name == Name.Parse(name);

    private static bool IsInstH(Expr e, string hName, string inner, int arity = 2) =>
        IsConstApp(e, hName, arity, out var args) && IsInstNamed(args[^1], inner);

    private static bool IsInstPowNat(Expr e) => IsConstApp(e, "instPowNat", 2, out var args) && IsInstNamed(args[1], "instNatPowNat");

    private static bool IsInstHPowNat(Expr e) => IsConstApp(e, "instHPow", 3, out var args) && IsInstPowNat(args[2]);

    /// <summary>Evaluates a closed <c>Nat</c> expression built from numerals and the Nat operations (Lean's <c>evalNat</c>).</summary>
    internal static BigInteger? EvalNat(Expr e)
    {
        switch (e)
        {
            case NatLitExpr n:
                return n.Value;
            case MDataExpr m:
                return EvalNat(m.Expr);
            case ConstExpr c when c.Name == MetaNames.NatZero:
                return BigInteger.Zero;
            case AppExpr:
                return Visit(e);
            default:
                return null;
        }

        BigInteger? Visit(Expr e)
        {
            Expr[]? a;
            if ((a = MatchApp(e, OfNatName, 3)) is not null)
            {
                return IsInstOfNatNat(a[2]) ? EvalNat(a[1]) : null;
            }
            if ((a = MatchApp(e, MetaNames.NatSucc, 1)) is not null)
            {
                return EvalNat(a[0]) + 1;
            }
            if (Bin(MetaNames.NatAdd, AddAdd, MetaNames.HAddHAdd, "instAddNat", "instHAdd", (x, y) => x + y) is { } add)
            {
                return add[0];
            }
            if (Bin(NatSubName, SubSub, HSubHSub, "instSubNat", "instHSub", (x, y) => x > y ? x - y : BigInteger.Zero) is { } sub)
            {
                return sub[0];
            }
            if (Bin(MetaNames.NatMul, MulMul, HMulHMul, "instMulNat", "instHMul", (x, y) => x * y) is { } mul)
            {
                return mul[0];
            }
            if (Bin(MetaNames.NatDiv, DivDiv, HDivHDiv, "Nat.instDiv", "instHDiv", (x, y) => y.IsZero ? BigInteger.Zero : x / y) is { } div)
            {
                return div[0];
            }
            if (Bin(MetaNames.NatMod, ModMod, HModHMod, "Nat.instMod", "instHMod", (x, y) => y.IsZero ? x : x % y) is { } mod)
            {
                return mod[0];
            }
            if ((a = MatchApp(e, MetaNames.NatPow, 2)) is not null)
            {
                return EvalPow(a[0], a[1]);
            }
            if ((a = MatchApp(e, NatPowPow, 4)) is not null)
            {
                return IsInstNamed(a[1], "instNatPowNat") ? EvalPow(a[2], a[3]) : null;
            }
            if ((a = MatchApp(e, PowPow, 5)) is not null)
            {
                return IsInstPowNat(a[2]) ? EvalPow(a[3], a[4]) : null;
            }
            if ((a = MatchApp(e, HPowHPow, 6)) is not null)
            {
                return IsInstHPowNat(a[3]) ? EvalPow(a[4], a[5]) : null;
            }
            return null;

            // Some(result) when the shape matched (result may be none), null when it did not.
            BigInteger?[]? Bin(Name natOp, Name op, Name hOp, string inst, string hInst, Func<BigInteger, BigInteger, BigInteger> f)
            {
                Expr[]? b;
                Expr x, y;
                if ((b = MatchApp(e, natOp, 2)) is not null)
                {
                    (x, y) = (b[0], b[1]);
                }
                else if ((b = MatchApp(e, op, 4)) is not null)
                {
                    if (!IsInstNamed(b[1], inst))
                    {
                        return [null];
                    }
                    (x, y) = (b[2], b[3]);
                }
                else if ((b = MatchApp(e, hOp, 6)) is not null)
                {
                    if (!IsInstH(b[3], hInst, inst))
                    {
                        return [null];
                    }
                    (x, y) = (b[4], b[5]);
                }
                else
                {
                    return null;
                }
                return EvalNat(x) is { } vx && EvalNat(y) is { } vy ? [f(vx, vy)] : [null];
            }
        }

        BigInteger? EvalPow(Expr b, Expr n)
        {
            if (EvalNat(n) is not { } vn || vn > ExponentThreshold || EvalNat(b) is not { } vb)
            {
                return null;
            }
            return BigInteger.Pow(vb, (int)vn);
        }
    }

    /// <summary>Whether <paramref name="e"/> is definitionally equal to <paramref name="inst"/> at <c>instances</c>, assigning nothing (Lean's <c>matchesInstance</c>).</summary>
    private bool MatchesInstance(Expr e, Expr inst) =>
        WithNewMCtxDepth(() => WithTransparency(TransparencyMode.Instances, () => IsDefEq(e, inst)));

    private (Expr S, BigInteger K) GetOffset(Expr e) => IsOffset(e) ?? (e, BigInteger.Zero);

    /// <summary><c>(s, k)</c> with <paramref name="e"/> definitionally <c>s + k</c>, <c>k &gt; 0</c> (Lean's <c>isOffset?</c>).</summary>
    internal (Expr S, BigInteger K)? IsOffset(Expr e)
    {
        Expr[]? a;
        if ((a = MatchApp(e, MetaNames.NatSucc, 1)) is not null)
        {
            var (s, k) = GetOffset(a[0]);
            return (s, k + 1);
        }
        if ((a = MatchApp(e, MetaNames.NatAdd, 2)) is not null)
        {
            return Add(a[0], a[1]);
        }
        if ((a = MatchApp(e, AddAdd, 4)) is not null)
        {
            return MatchesInstance(a[1], MetaNames.MkInstAdd()) ? Add(a[2], a[3]) : null;
        }
        if ((a = MatchApp(e, MetaNames.HAddHAdd, 6)) is not null)
        {
            return MatchesInstance(a[3], MetaNames.MkInstHAdd()) ? Add(a[4], a[5]) : null;
        }
        return null;

        (Expr, BigInteger)? Add(Expr x, Expr y)
        {
            if (EvalNat(y) is not { } v)
            {
                return null;
            }
            var (s, k) = GetOffset(x);
            return (s, k + v);
        }
    }

    private static bool IsNatZero(Expr e) => EvalNat(e) is { } v && v.IsZero;

    private static Expr MkOffset(Expr e, BigInteger offset)
    {
        if (offset.IsZero)
        {
            return e;
        }
        return IsNatZero(e) ? MetaNames.MkNatLit(offset) : MetaNames.MkNatAdd(e, MetaNames.MkNatLit(offset));
    }

    /// <summary>Solves <c>s + k₁ =?= t + k₂</c> and numeral constraints on <c>Nat</c> (Lean's <c>isDefEqOffset</c>).</summary>
    private LBool IsDefEqOffset(Expr s, Expr t)
    {
        if (!Config.OffsetCnstrs)
        {
            return LBool.Undef;
        }
        if (IsOffset(s) is (var s1, var k1))
        {
            if (IsOffset(t) is (var t1, var k2))
            {
                if (k1 == k2)
                {
                    return DefEq(s1, t1);
                }
                return k1 < k2 ? DefEq(s1, MkOffset(t1, k2 - k1)) : DefEq(MkOffset(s1, k1 - k2), t1);
            }
            if (EvalNat(t) is { } v2)
            {
                return v2 >= k1 ? DefEq(s1, MetaNames.MkNatLit(v2 - k1)) : IfNatExpr(() => LBool.False);
            }
            return LBool.Undef;
        }
        if (EvalNat(s) is { } v1)
        {
            if (IsOffset(t) is (var t1, var k2))
            {
                return v1 >= k2 ? DefEq(MetaNames.MkNatLit(v1 - k2), t1) : IfNatExpr(() => LBool.False);
            }
            if (EvalNat(t) is { } v2)
            {
                return IfNatExpr(() => v1 == v2 ? LBool.True : LBool.False);
            }
        }
        return LBool.Undef;

        LBool IfNatExpr(Func<LBool> x)
        {
            var type = InferType(s);
            // withNewMCtxDepth: the test must not assign metavariables.
            return WithNewMCtxDepth(() => IsExprDefEqAux(type, MetaNames.NatConst)) ? x() : LBool.Undef;
        }

        LBool DefEq(Expr a, Expr b) => IfNatExpr(() => IsExprDefEqAux(a, b) ? LBool.True : LBool.False);
    }
}
