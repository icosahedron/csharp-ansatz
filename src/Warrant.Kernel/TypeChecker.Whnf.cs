using System.Numerics;
using Warrant.Cic;

namespace Warrant.Kernel;

public sealed partial class TypeChecker
{
    /// <summary>The weak head normal form of <paramref name="e"/> (all reductions, including unfolding definitions).</summary>
    public Expr Whnf(Expr e)
    {
        switch (e.Kind)
        {
            case ExprKind.BVar:
            case ExprKind.Sort:
            case ExprKind.Forall:
            case ExprKind.NatLit:
            case ExprKind.StrLit:
                return e;
            case ExprKind.MData:
                return Whnf(((MDataExpr)e).Expr);
            case ExprKind.MVar:
                throw MVarUnsupported();
            case ExprKind.FVar:
                if (!IsLetFVar(e))
                {
                    return e;
                }
                break;
        }
        if (_whnfCache.TryGetValue(e, out var cached))
        {
            return cached;
        }
        var t = e;
        while (true)
        {
            var t1 = WhnfCore(t);
            if (ReduceNative(t1) is { } v1)
            {
                _whnfCache[e] = v1;
                return v1;
            }
            if (ReduceNat(t1) is { } v2)
            {
                _whnfCache[e] = v2;
                return v2;
            }
            if (UnfoldDefinition(t1) is { } next)
            {
                t = next;
            }
            else
            {
                _whnfCache[e] = t1;
                return t1;
            }
        }
    }

    /// <summary>
    /// Weak head normalization without unfolding definitions or the <c>Nat</c> extensions.
    /// With <paramref name="cheapRec"/>/<paramref name="cheapProj"/>, recursor major premises and
    /// projected structures are themselves only reduced with <c>WhnfCore</c>.
    /// </summary>
    public Expr WhnfCore(Expr e, bool cheapRec = false, bool cheapProj = false)
    {
        Tick();
        switch (e.Kind)
        {
            case ExprKind.BVar:
            case ExprKind.Sort:
            case ExprKind.Forall:
            case ExprKind.Const:
            case ExprKind.Lam:
            case ExprKind.NatLit:
            case ExprKind.StrLit:
                return e;
            case ExprKind.MData:
                return WhnfCore(((MDataExpr)e).Expr, cheapRec, cheapProj);
            case ExprKind.MVar:
                throw MVarUnsupported();
            case ExprKind.FVar:
                if (!IsLetFVar(e))
                {
                    return e;
                }
                break;
        }
        if (_whnfCoreCache.TryGetValue(e, out var cached))
        {
            return cached;
        }
        Expr r;
        switch (e)
        {
            case FVarExpr f:
                return WhnfCore(LocalContext.Find(f.Id)!.Value!, cheapRec, cheapProj); // zeta
            case ProjExpr p:
                r = ReduceProj(p, cheapRec, cheapProj) is { } projected ? WhnfCore(projected, cheapRec, cheapProj) : e;
                break;
            case AppExpr:
            {
                var revArgs = new List<Expr>();
                var f0 = ExprOps.GetAppRevArgs(e, revArgs);
                var f = WhnfCore(f0, cheapRec, cheapProj);
                if (f is LamExpr lam)
                {
                    int m = 1;
                    int numArgs = revArgs.Count;
                    Expr body = lam.Body;
                    while (body is LamExpr inner && m < numArgs)
                    {
                        body = inner.Body;
                        m++;
                    }
                    var span = System.Runtime.InteropServices.CollectionsMarshal.AsSpan(revArgs);
                    r = WhnfCore(ExprOps.MkRevApp(ExprOps.Instantiate(body, span[(numArgs - m)..]), span[..(numArgs - m)]), cheapRec, cheapProj);
                }
                else if (ReferenceEquals(f, f0))
                {
                    if (ReduceRecursor(e, cheapRec, cheapProj) is { } red)
                    {
                        return WhnfCore(red, cheapRec, cheapProj); // iota and quotient reduction
                    }
                    return e;
                }
                else
                {
                    r = WhnfCore(ExprOps.MkRevApp(f, System.Runtime.InteropServices.CollectionsMarshal.AsSpan(revArgs)), cheapRec, cheapProj);
                }
                break;
            }
            case LetExpr l:
                r = WhnfCore(ExprOps.Instantiate(l.Body, l.Value), cheapRec, cheapProj);
                break;
            case MVarExpr:
                throw MVarUnsupported();
            default:
                throw new KernelException($"unexpected expression kind {e.Kind}");
        }
        if (!cheapRec && !cheapProj)
        {
            _whnfCoreCache[e] = r;
        }
        return r;
    }

    private bool IsLetFVar(Expr e) => LocalContext.Find(((FVarExpr)e).Id)?.Value is not null;

    // ------------------------------------------------------------------ delta

    /// <summary>The definition (or theorem) to unfold at the head of <paramref name="e"/>, if any.</summary>
    private ConstantInfo? IsDelta(Expr e)
    {
        if (e.GetAppFn() is ConstExpr c && Env.Find(c.Name) is { } info
            && info.Kind is ConstantKind.Definition or ConstantKind.Theorem
            && c.Levels.Count == info.LevelParams.Count)
        {
            return info;
        }
        return null;
    }

    private static ReducibilityHints HintsOf(ConstantInfo info) =>
        info is DefinitionInfo d ? d.Hints : ReducibilityHints.Opaque;

    private Expr? UnfoldDefinitionCore(Expr e)
    {
        if (e is ConstExpr c && IsDelta(e) is { } d)
        {
            if (c.Levels.Count > 0)
            {
                if (_unfoldCache.TryGetValue(e, out var cached))
                {
                    return cached;
                }
                var result = ExprOps.InstantiateValueLevelParams(d, c.Levels);
                _unfoldCache[e] = result;
                return result;
            }
            return ExprOps.InstantiateValueLevelParams(d, c.Levels);
        }
        return null;
    }

    /// <summary>Unfolds the constant at the head of <paramref name="e"/>, if it is a definition or theorem.</summary>
    public Expr? UnfoldDefinition(Expr e)
    {
        if (e is AppExpr)
        {
            if (UnfoldDefinitionCore(e.GetAppFn()) is { } f)
            {
                var revArgs = new List<Expr>();
                ExprOps.GetAppRevArgs(e, revArgs);
                return ExprOps.MkRevApp(f, System.Runtime.InteropServices.CollectionsMarshal.AsSpan(revArgs));
            }
            return null;
        }
        return UnfoldDefinitionCore(e);
    }

    /// <summary>
    /// <c>Lean.reduceBool</c>/<c>Lean.reduceNat</c> evaluate compiled code inside the kernel
    /// (used by <c>native_decide</c>). Warrant has no compiler and does not trust one, so these
    /// never reduce here and declarations that depend on them are rejected.
    /// </summary>
    private static Expr? ReduceNative(Expr e) => null;

    // ------------------------------------------------------------------ projections

    private Expr? ReduceProjCore(Expr c, Name structName, int idx)
    {
        if (c is StrLitExpr)
        {
            c = Whnf(StringLitToConstructor(c));
        }
        var mk = c.GetAppFn();
        if (mk is not ConstExpr mkConst || Env.Find(mkConst.Name) is not ConstructorInfo mkVal || mkVal.Inductive != structName)
        {
            return null;
        }
        var args = c.GetAppArgs();
        return mkVal.NumParams + idx < args.Length ? args[mkVal.NumParams + idx] : null;
    }

    private Expr? ReduceProj(ProjExpr e, bool cheapRec, bool cheapProj)
    {
        var c = cheapProj ? WhnfCore(e.Struct, cheapRec, cheapProj) : Whnf(e.Struct);
        return ReduceProjCore(c, e.TypeName, e.Index);
    }

    // ------------------------------------------------------------------ recursors and quotients

    private Expr? ReduceRecursor(Expr e, bool cheapRec, bool cheapProj)
    {
        if (Env.IsQuotInitialized && QuotReduceRec(e) is { } q)
        {
            return q;
        }
        return InductiveReduceRec(e, cheapRec, cheapProj);
    }

    private Expr? QuotReduceRec(Expr e)
    {
        if (e.GetAppFn() is not ConstExpr fn)
        {
            return null;
        }
        int mkPos, argPos;
        if (fn.Name == KernelNames.QuotLift)
        {
            mkPos = 5;
            argPos = 3;
        }
        else if (fn.Name == KernelNames.QuotInd)
        {
            mkPos = 4;
            argPos = 3;
        }
        else
        {
            return null;
        }
        var args = e.GetAppArgs();
        if (args.Length <= mkPos)
        {
            return null;
        }
        var mk = Whnf(args[mkPos]);
        if (mk.GetAppFn() is not ConstExpr mkFn || mkFn.Name != KernelNames.QuotMk || mk.GetAppNumArgs() != 3)
        {
            return null;
        }
        var r = Expr.App(args[argPos], ((AppExpr)mk).Arg);
        int elimArity = mkPos + 1;
        return args.Length > elimArity ? ExprOps.MkApp(r, args.AsSpan(elimArity)) : r;
    }

    private static int MajorIndex(RecursorInfo r) => r.NumParams + r.NumMotives + r.NumMinors + r.NumIndices;

    private static Name MajorInductive(RecursorInfo r)
    {
        var t = r.Type;
        int n = MajorIndex(r);
        for (int i = 0; i < n; i++)
        {
            t = ((ForallExpr)t).Body;
        }
        return ((ConstExpr)((ForallExpr)t).BinderType.GetAppFn()).Name;
    }

    private Expr? InductiveReduceRec(Expr e, bool cheapRec, bool cheapProj)
    {
        if (e.GetAppFn() is not ConstExpr recFn || Env.Find(recFn.Name) is not RecursorInfo recVal)
        {
            return null;
        }
        var recArgs = e.GetAppArgs();
        int majorIdx = MajorIndex(recVal);
        if (majorIdx >= recArgs.Length)
        {
            return null;
        }
        var major = recArgs[majorIdx];
        if (recVal.K)
        {
            major = ToCnstrWhenK(recVal, major);
        }
        major = cheapRec ? WhnfCore(major, cheapRec, cheapProj) : Whnf(major);
        if (major is NatLitExpr nat)
        {
            major = NatLitToConstructor(nat);
        }
        else if (major is StrLitExpr)
        {
            major = Whnf(StringLitToConstructor(major));
        }
        else
        {
            major = ToCnstrWhenStructure(MajorInductive(recVal), major);
        }
        var rule = GetRecRuleFor(recVal, major);
        if (rule is null)
        {
            return null;
        }
        var majorArgs = major.GetAppArgs();
        if (rule.NumFields > majorArgs.Length || recFn.Levels.Count != recVal.LevelParams.Count)
        {
            return null;
        }
        var rhs = ExprOps.InstantiateLevelParams(rule.Rhs, recVal.LevelParams, recFn.Levels);
        rhs = ExprOps.MkApp(rhs, recArgs.AsSpan(0, recVal.NumParams + recVal.NumMotives + recVal.NumMinors));
        // Nested inductives: the constructor may have more parameters than the recursor.
        int nparams = majorArgs.Length - rule.NumFields;
        rhs = ExprOps.MkApp(rhs, majorArgs.AsSpan(nparams, rule.NumFields));
        if (recArgs.Length > majorIdx + 1)
        {
            rhs = ExprOps.MkApp(rhs, recArgs.AsSpan(majorIdx + 1));
        }
        return rhs;
    }

    private static RecursorRule? GetRecRuleFor(RecursorInfo recVal, Expr major)
    {
        if (major.GetAppFn() is not ConstExpr fn)
        {
            return null;
        }
        foreach (var rule in recVal.Rules)
        {
            if (rule.Constructor == fn.Name)
            {
                return rule;
            }
        }
        return null;
    }

    /// <summary>For K-like recursors, replaces a proof of <c>I as</c> by the nullary constructor when its type matches.</summary>
    private Expr ToCnstrWhenK(RecursorInfo recVal, Expr e)
    {
        var appType = Whnf(Infer(e));
        if (appType.GetAppFn() is not ConstExpr typeI || typeI.Name != MajorInductive(recVal))
        {
            return e;
        }
        if (MkNullaryCnstr(appType, recVal.NumParams) is not { } newCnstrApp)
        {
            return e;
        }
        var newType = Infer(newCnstrApp);
        return IsDefEq(appType, newType) ? newCnstrApp : e;
    }

    private Expr? MkNullaryCnstr(Expr type, int numParams)
    {
        if (type.GetAppFn() is not ConstExpr d || FirstConstructor(d.Name) is not { } cnstrName)
        {
            return null;
        }
        var args = type.GetAppArgs();
        return ExprOps.MkApp(Expr.Const(cnstrName, d.Levels), args.AsSpan(0, Math.Min(numParams, args.Length)));
    }

    private Name? FirstConstructor(Name inductive) =>
        Env.Find(inductive) is InductiveInfo { Constructors.Count: > 0 } ind ? ind.Constructors[0] : null;

    /// <summary>Whether <paramref name="name"/> is an inductive type with one constructor, no indices, and no recursion.</summary>
    public bool IsNonRecStructure(Name name) =>
        Env.Find(name) is InductiveInfo { Constructors.Count: 1, NumIndices: 0, IsRec: false };

    private bool IsConstructorApp(Expr e) =>
        e.GetAppFn() is ConstExpr c && Env.Find(c.Name) is ConstructorInfo;

    /// <summary>Eta-expands a structure value: <c>e</c> becomes <c>S.mk e.1 … e.n</c>.</summary>
    private Expr ExpandEtaStruct(Expr eType, Expr e)
    {
        if (eType.GetAppFn() is not ConstExpr I || FirstConstructor(I.Name) is not { } ctorName)
        {
            return e;
        }
        var ctor = (ConstructorInfo)Env.Get(ctorName);
        var args = eType.GetAppArgs();
        var result = ExprOps.MkApp(Expr.Const(ctorName, I.Levels), args.AsSpan(0, Math.Min(ctor.NumParams, args.Length)));
        for (int i = 0; i < ctor.NumFields; i++)
        {
            result = Expr.App(result, Expr.Proj(I.Name, i, e));
        }
        return result;
    }

    private Expr ToCnstrWhenStructure(Name inductName, Expr e)
    {
        if (!IsNonRecStructure(inductName) || IsConstructorApp(e))
        {
            return e;
        }
        var eType = Whnf(Infer(e));
        if (eType.GetAppFn() is not ConstExpr c || c.Name != inductName)
        {
            return e;
        }
        if (IsProp(eType))
        {
            return e;
        }
        return ExpandEtaStruct(eType, e);
    }

    /// <summary><c>n</c> as <c>Nat.zero</c> or <c>Nat.succ (n-1)</c>.</summary>
    public static Expr NatLitToConstructor(NatLitExpr e) =>
        e.Value.IsZero ? NatZeroConst : Expr.App(NatSuccConst, Expr.NatLit(e.Value - 1));

    /// <summary><c>"abc"</c> as <c>String.ofList [Char.ofNat 97, …]</c>.</summary>
    public static Expr StringLitToConstructor(Expr e)
    {
        var s = ((StrLitExpr)e).Value;
        var charType = Expr.Const(KernelNames.CharType);
        var nil = Expr.App(Expr.Const(KernelNames.ListNil, Level.Zero), charType);
        var cons = Expr.App(Expr.Const(KernelNames.ListCons, Level.Zero), charType);
        var charOfNat = Expr.Const(KernelNames.CharOfNat);
        var runes = s.EnumerateRunes().ToList();
        Expr r = nil;
        for (int i = runes.Count - 1; i >= 0; i--)
        {
            r = Expr.App(Expr.App(cons, Expr.App(charOfNat, Expr.NatLit(runes[i].Value))), r);
        }
        return Expr.App(Expr.Const(KernelNames.StringOfList), r);
    }

    // ------------------------------------------------------------------ Nat literal extensions

    private static bool IsNatLitExt(Expr e) => e is NatLitExpr || (e is ConstExpr c && c.Name == KernelNames.NatZero && c.Levels.Count == 0);

    private static BigInteger NatValue(Expr e) => e is NatLitExpr n ? n.Value : BigInteger.Zero;

    private Expr? ReduceBinNat(Expr e, Func<BigInteger, BigInteger, BigInteger> f, bool checkSize = false)
    {
        var a1 = Whnf(((AppExpr)((AppExpr)e).Fn).Arg);
        if (!IsNatLitExt(a1))
        {
            return null;
        }
        var a2 = Whnf(((AppExpr)e).Arg);
        if (!IsNatLitExt(a2))
        {
            return null;
        }
        var r = f(NatValue(a1), NatValue(a2));
        if (checkSize)
        {
            CheckNatSize(r);
        }
        return Expr.NatLit(r);
    }

    private Expr? ReduceBinNatPred(Expr e, Func<BigInteger, BigInteger, bool> f)
    {
        var a1 = Whnf(((AppExpr)((AppExpr)e).Fn).Arg);
        if (!IsNatLitExt(a1))
        {
            return null;
        }
        var a2 = Whnf(((AppExpr)e).Arg);
        if (!IsNatLitExt(a2))
        {
            return null;
        }
        return f(NatValue(a1), NatValue(a2)) ? BoolTrueConst : BoolFalseConst;
    }

    private static int CountArg(BigInteger count, string op)
    {
        if (count > uint.MaxValue)
        {
            throw new KernelResourceException($"the kernel refused to evaluate `{op}` because its second argument does not fit in a 32-bit unsigned integer");
        }
        if (count > int.MaxValue)
        {
            throw new KernelResourceException($"the kernel refused to evaluate `{op}`: argument too large");
        }
        return (int)count;
    }

    private Expr? ReduceNat(Expr e)
    {
        int nargs = e.GetAppNumArgs();
        if (nargs == 1)
        {
            if (((AppExpr)e).Fn is ConstExpr f && f.Name == KernelNames.NatSucc && f.Levels.Count == 0)
            {
                var arg = Whnf(((AppExpr)e).Arg);
                if (!IsNatLitExt(arg))
                {
                    return null;
                }
                var v = NatValue(arg) + 1;
                CheckNatSize(v);
                return Expr.NatLit(v);
            }
            return null;
        }
        if (nargs != 2 || ((AppExpr)((AppExpr)e).Fn).Fn is not ConstExpr fn || fn.Levels.Count != 0)
        {
            return null;
        }
        var n = fn.Name;
        if (n == KernelNames.NatAdd)
        {
            return ReduceBinNat(e, (a, b) => a + b, checkSize: true);
        }
        if (n == KernelNames.NatSub)
        {
            return ReduceBinNat(e, (a, b) => a > b ? a - b : BigInteger.Zero, checkSize: true);
        }
        if (n == KernelNames.NatMul)
        {
            return ReduceBinNat(e, (a, b) => a * b, checkSize: true);
        }
        if (n == KernelNames.NatPow)
        {
            return ReduceBinNat(e, (b, x) =>
            {
                int k = CountArg(x, "Nat.pow");
                if (b > 1 && k != 0 && b.GetByteCount() > _limits.MaxNatBytes / k)
                {
                    throw new KernelResourceException("the kernel refused to evaluate `Nat.pow` because the result would exceed the maximum numeral size");
                }
                return BigInteger.Pow(b, k);
            });
        }
        if (n == KernelNames.NatGcd)
        {
            return ReduceBinNat(e, BigInteger.GreatestCommonDivisor);
        }
        if (n == KernelNames.NatMod)
        {
            return ReduceBinNat(e, (a, b) => b.IsZero ? a : a % b);
        }
        if (n == KernelNames.NatDiv)
        {
            return ReduceBinNat(e, (a, b) => b.IsZero ? BigInteger.Zero : a / b);
        }
        if (n == KernelNames.NatBeq)
        {
            return ReduceBinNatPred(e, (a, b) => a == b);
        }
        if (n == KernelNames.NatBle)
        {
            return ReduceBinNatPred(e, (a, b) => a <= b);
        }
        if (n == KernelNames.NatLand)
        {
            return ReduceBinNat(e, (a, b) => a & b);
        }
        if (n == KernelNames.NatLor)
        {
            return ReduceBinNat(e, (a, b) => a | b);
        }
        if (n == KernelNames.NatXor)
        {
            return ReduceBinNat(e, (a, b) => a ^ b);
        }
        if (n == KernelNames.NatShiftLeft)
        {
            return ReduceBinNat(e, (a, b) =>
            {
                if (a.IsZero)
                {
                    return a;
                }
                int k = CountArg(b, "Nat.shiftLeft");
                if (a.GetByteCount() + (k / 8) + 1 > _limits.MaxNatBytes)
                {
                    throw new KernelResourceException("the kernel refused a Nat numeral because its size exceeds the maximum");
                }
                return a << k;
            });
        }
        if (n == KernelNames.NatShiftRight)
        {
            return ReduceBinNat(e, (a, b) => b >= int.MaxValue ? BigInteger.Zero : a >> (int)b);
        }
        return null;
    }
}
