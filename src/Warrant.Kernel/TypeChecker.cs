using System.Numerics;
using System.Runtime.CompilerServices;
using Warrant.Cic;

namespace Warrant.Kernel;

/// <summary>Resource limits for a type checker.</summary>
/// <param name="Fuel">
/// The step budget: each call of the recursive core procedures (type inference, weak-head
/// normalization, definitional equality) costs one unit. Lean's kernel has no such limit; running
/// out here rejects the declaration conservatively.
/// </param>
/// <param name="MaxNatBytes">The largest natural-number literal (in bytes) the kernel will compute.</param>
public sealed record KernelLimits(long Fuel, long MaxNatBytes)
{
    /// <summary>Defaults for interactive use: 20M steps, 128 MB numerals (Lean's default size limit).</summary>
    public static KernelLimits Interactive { get; } = new(20_000_000, 128L * 1024 * 1024);

    /// <summary>Defaults for checking imported libraries: 100M steps.</summary>
    public static KernelLimits Corpus { get; } = new(100_000_000, 128L * 1024 * 1024);
}

/// <summary>
/// The Lean 4 type checker: type inference, weak-head normalization and definitional equality for
/// the Calculus of Inductive Constructions. A port of Lean 4's <c>src/kernel/type_checker.cpp</c>.
/// </summary>
/// <remarks>
/// A type checker is single-threaded and short-lived: create one per declaration. Its caches are
/// keyed by expressions up to binder annotations (<see cref="Expr.AlphaComparer"/>), as in Lean.
/// </remarks>
public sealed partial class TypeChecker
{
    private static readonly Expr DontCare = Expr.Const(Name.From("dontcare"));
    private static readonly Expr NatZeroConst = Expr.Const(KernelNames.NatZero);
    private static readonly Expr NatSuccConst = Expr.Const(KernelNames.NatSucc);
    private static readonly Expr BoolTrueConst = Expr.Const(KernelNames.BoolTrue);
    private static readonly Expr BoolFalseConst = Expr.Const(KernelNames.BoolFalse);
    private static readonly Expr NatType = Expr.Const(KernelNames.Nat);
    private static readonly Expr StringTypeConst = Expr.Const(KernelNames.StringType);

    private readonly NameGenerator _ngen = new(KernelNames.KernelFresh);
    private readonly DefinitionSafety _safety;
    private readonly KernelLimits _limits;
    private readonly Dictionary<Expr, Expr>[] _inferCache = [new(Expr.AlphaComparer), new(Expr.AlphaComparer)];
    private readonly Dictionary<Expr, Expr> _whnfCoreCache = new(Expr.AlphaComparer);
    private readonly Dictionary<Expr, Expr> _whnfCache = new(Expr.AlphaComparer);
    private readonly Dictionary<Expr, Expr> _unfoldCache = new(Expr.AlphaComparer);
    private readonly HashSet<(Expr, Expr)> _defEqSuccess = new(ExprPairComparer.Instance);
    private readonly HashSet<(Expr, Expr)> _defEqFailure = new(ExprPairComparer.Instance);
    private EquatableArray<Name>? _lparams;
    private bool _eagerReduce;
    private long _fuel;

    /// <summary>Creates a type checker over <paramref name="env"/>.</summary>
    /// <param name="env">The environment of admitted constants.</param>
    /// <param name="safety">
    /// <see cref="DefinitionSafety.Safe"/> rejects references to unsafe and partial constants;
    /// <see cref="DefinitionSafety.Partial"/> allows partial ones; <see cref="DefinitionSafety.Unsafe"/> allows both.
    /// </param>
    /// <param name="limits">Resource limits (default: <see cref="KernelLimits.Interactive"/>).</param>
    /// <param name="localContext">
    /// A local context whose free variables this checker may refer to (used while admitting inductive
    /// types). The checker records its own variables in a child context.
    /// </param>
    public TypeChecker(KernelEnvironment env, DefinitionSafety safety = DefinitionSafety.Safe, KernelLimits? limits = null, LocalContext? localContext = null)
    {
        Env = env ?? throw new ArgumentNullException(nameof(env));
        _safety = safety;
        _limits = limits ?? KernelLimits.Interactive;
        _fuel = _limits.Fuel;
        LocalContext = localContext is null ? new LocalContext() : new LocalContext(localContext);
    }

    /// <summary>The environment.</summary>
    public KernelEnvironment Env { get; }

    /// <summary>The local context of free variables.</summary>
    public LocalContext LocalContext { get; }

    /// <summary>Fuel consumed so far.</summary>
    public long FuelUsed => _limits.Fuel - _fuel;

    /// <summary>
    /// Infers the type of <paramref name="e"/> without checking it. If <paramref name="e"/> is type
    /// correct, the result is its type.
    /// </summary>
    public Expr Infer(Expr e) => InferTypeCore(e, inferOnly: true);

    /// <summary>
    /// Type-checks <paramref name="e"/> and returns its type; every universe parameter must be
    /// among <paramref name="levelParams"/>.
    /// </summary>
    /// <exception cref="KernelException">The expression is not type correct.</exception>
    public Expr Check(Expr e, EquatableArray<Name> levelParams)
    {
        var saved = _lparams;
        _lparams = levelParams;
        try
        {
            return InferTypeCore(e, inferOnly: false);
        }
        finally
        {
            _lparams = saved;
        }
    }

    /// <summary>Type-checks <paramref name="e"/>, ignoring undefined universe parameters.</summary>
    public Expr Check(Expr e)
    {
        var saved = _lparams;
        _lparams = null;
        try
        {
            return InferTypeCore(e, inferOnly: false);
        }
        finally
        {
            _lparams = saved;
        }
    }

    /// <summary>Whether <paramref name="e"/> is a proposition (its type is <c>Prop</c> up to level normalization).</summary>
    public bool IsProp(Expr e)
    {
        var s = (SortExpr)EnsureSort(Infer(e), e);
        return LevelOps.NormalizesToZero(s.Level);
    }

    /// <summary>Returns <paramref name="t"/> as a <c>Sort</c>, reducing it if necessary.</summary>
    /// <exception cref="KernelException">It does not reduce to a sort.</exception>
    public Expr EnsureSort(Expr t, Expr? source = null)
    {
        if (t is SortExpr)
        {
            return t;
        }
        var r = Whnf(t);
        return r is SortExpr ? r : throw new KernelException($"type expected: {source ?? t}");
    }

    /// <summary>Returns <paramref name="t"/> as a Pi type, reducing it if necessary.</summary>
    /// <exception cref="KernelException">It does not reduce to a Pi type.</exception>
    public Expr EnsurePi(Expr t, Expr? source = null)
    {
        if (t is ForallExpr)
        {
            return t;
        }
        var r = Whnf(t);
        return r is ForallExpr ? r : throw new KernelException($"function expected: {source ?? t}");
    }

    /// <summary>Infers the type of <paramref name="e"/> and returns it as a <c>Sort</c>.</summary>
    public Expr EnsureType(Expr e) => EnsureSort(Infer(e), e);

    // ------------------------------------------------------------------ inference

    private void Tick()
    {
        if (--_fuel < 0)
        {
            throw new KernelResourceException($"kernel fuel exhausted ({_limits.Fuel:N0} steps)");
        }
        RuntimeHelpers.EnsureSufficientExecutionStack();
    }

    private Expr InferTypeCore(Expr e, bool inferOnly)
    {
        if (e.HasLooseBVars)
        {
            throw new KernelException("type checker does not support loose bound variables, replace them with free variables before invoking it");
        }
        Tick();
        var cache = _inferCache[inferOnly ? 1 : 0];
        if (cache.TryGetValue(e, out var cached))
        {
            return cached;
        }
        Expr r = e switch
        {
            NatLitExpr n => InferNatLit(n),
            StrLitExpr => StringTypeConst,
            MDataExpr m => InferTypeCore(m.Expr, inferOnly),
            ProjExpr p => InferProj(p, inferOnly),
            FVarExpr f => InferFVar(f),
            SortExpr s => InferSort(s, inferOnly),
            ConstExpr c => InferConstant(c, inferOnly),
            LamExpr l => InferLambda(l, inferOnly),
            ForallExpr p => InferPi(p, inferOnly),
            AppExpr a => InferApp(a, inferOnly),
            LetExpr l => InferLet(l, inferOnly),
            _ => throw new KernelException($"unexpected expression kind {e.Kind}"),
        };
        cache[e] = r;
        return r;
    }

    private Expr InferNatLit(NatLitExpr n)
    {
        CheckNatSize(n.Value);
        return NatType;
    }

    private Expr InferSort(SortExpr s, bool inferOnly)
    {
        if (!inferOnly)
        {
            CheckLevel(s.Level);
        }
        return Expr.Sort(Level.Succ(s.Level));
    }

    private void CheckLevel(Level l)
    {
        if (_lparams is { } lps && LevelOps.GetUndefinedParam(l, lps) is { } undefined)
        {
            throw new KernelException($"invalid reference to undefined universe level parameter '{undefined}'");
        }
    }

    private Expr InferFVar(FVarExpr f) =>
        LocalContext.Find(f.Id)?.Type ?? throw new KernelException($"unknown free variable '{f.Id}'");

    private Expr InferConstant(ConstExpr c, bool inferOnly)
    {
        var info = Env.Find(c.Name) ?? throw new KernelException($"unknown constant '{c.Name}'");
        if (info.LevelParams.Count != c.Levels.Count)
        {
            throw new KernelException(
                $"incorrect number of universe levels parameters for '{c.Name}', #{info.LevelParams.Count} expected, #{c.Levels.Count} provided");
        }
        if (!inferOnly)
        {
            if (info.IsUnsafe && _safety != DefinitionSafety.Unsafe)
            {
                throw new KernelException($"invalid declaration, it uses unsafe declaration '{c.Name}'");
            }
            if (info is DefinitionInfo { Safety: DefinitionSafety.Partial } && _safety == DefinitionSafety.Safe)
            {
                throw new KernelException($"invalid declaration, safe declaration must not contain partial declaration '{c.Name}'");
            }
            foreach (var l in c.Levels)
            {
                CheckLevel(l);
            }
        }
        return ExprOps.InstantiateTypeLevelParams(info, c.Levels);
    }

    private Expr InferLambda(LamExpr lam, bool inferOnly)
    {
        var fvars = new List<Expr>();
        Expr e = lam;
        while (e is LamExpr l)
        {
            var d = ExprOps.InstantiateRev(l.BinderType, System.Runtime.InteropServices.CollectionsMarshal.AsSpan(fvars));
            if (!inferOnly)
            {
                EnsureSort(InferTypeCore(d, inferOnly), d);
            }
            fvars.Add(LocalContext.MkLocalDecl(_ngen, l.BinderName, d, l.BinderInfo));
            e = l.Body;
        }
        var r = InferTypeCore(ExprOps.InstantiateRev(e, System.Runtime.InteropServices.CollectionsMarshal.AsSpan(fvars)), inferOnly);
        r = ExprOps.CheapBetaReduce(r);
        return LocalContext.MkPi(fvars, r);
    }

    private Expr InferPi(ForallExpr pi, bool inferOnly)
    {
        var fvars = new List<Expr>();
        var us = new List<Level>();
        Expr e = pi;
        while (e is ForallExpr p)
        {
            var d = ExprOps.InstantiateRev(p.BinderType, System.Runtime.InteropServices.CollectionsMarshal.AsSpan(fvars));
            var t1 = (SortExpr)EnsureSort(InferTypeCore(d, inferOnly), d);
            us.Add(t1.Level);
            fvars.Add(LocalContext.MkLocalDecl(_ngen, p.BinderName, d, p.BinderInfo));
            e = p.Body;
        }
        e = ExprOps.InstantiateRev(e, System.Runtime.InteropServices.CollectionsMarshal.AsSpan(fvars));
        var s = (SortExpr)EnsureSort(InferTypeCore(e, inferOnly), e);
        var r = s.Level;
        for (int i = fvars.Count - 1; i >= 0; i--)
        {
            r = LevelOps.MkIMax(us[i], r);
        }
        return Expr.Sort(r);
    }

    private static bool IsEagerReduce(Expr e) =>
        e.GetAppFn() is ConstExpr c && c.Name == KernelNames.EagerReduce && e.GetAppNumArgs() == 2;

    private Expr InferApp(AppExpr e, bool inferOnly)
    {
        if (!inferOnly)
        {
            var fType = (ForallExpr)EnsurePi(InferTypeCore(e.Fn, inferOnly), e);
            var aType = InferTypeCore(e.Arg, inferOnly);
            var dType = fType.BinderType;
            bool ok;
            if (IsEagerReduce(e.Arg))
            {
                bool saved = _eagerReduce;
                _eagerReduce = true;
                try
                {
                    ok = IsDefEq(aType, dType);
                }
                finally
                {
                    _eagerReduce = saved;
                }
            }
            else
            {
                ok = IsDefEq(aType, dType);
            }
            if (!ok)
            {
                throw new KernelException($"application type mismatch: argument {e.Arg} has type {aType}, but is expected to have type {dType}");
            }
            return ExprOps.Instantiate(fType.Body, e.Arg);
        }
        else
        {
            var args = e.GetAppArgs();
            var f = e.GetAppFn();
            var fType = InferTypeCore(f, inferOnly: true);
            int j = 0;
            int nargs = args.Length;
            for (int i = 0; i < nargs; i++)
            {
                if (fType is ForallExpr p)
                {
                    fType = p.Body;
                }
                else
                {
                    fType = ExprOps.InstantiateRev(fType, args.AsSpan(j, i - j));
                    fType = ((ForallExpr)EnsurePi(fType, e)).Body;
                    j = i;
                }
            }
            return ExprOps.InstantiateRev(fType, args.AsSpan(j, nargs - j));
        }
    }

    private Expr InferLet(LetExpr let, bool inferOnly)
    {
        var fvars = new List<Expr>();
        Expr e = let;
        while (e is LetExpr l)
        {
            var span = System.Runtime.InteropServices.CollectionsMarshal.AsSpan(fvars);
            var type = ExprOps.InstantiateRev(l.BinderType, span);
            var val = ExprOps.InstantiateRev(l.Value, span);
            if (!inferOnly)
            {
                EnsureSort(InferTypeCore(type, inferOnly), type);
                var valType = InferTypeCore(val, inferOnly);
                if (!IsDefEq(valType, type))
                {
                    throw new KernelException($"type mismatch in let '{l.BinderName}': value has type {valType}, but is expected to have type {type}");
                }
            }
            fvars.Add(LocalContext.MkLetDecl(_ngen, l.BinderName, type, val));
            e = l.Body;
        }
        var r = InferTypeCore(ExprOps.InstantiateRev(e, System.Runtime.InteropServices.CollectionsMarshal.AsSpan(fvars)), inferOnly);
        r = ExprOps.CheapBetaReduce(r);
        return LocalContext.MkPi(fvars, r, removeDeadLet: true);
    }

    private Expr InferProj(ProjExpr e, bool inferOnly)
    {
        var type = Whnf(InferTypeCore(e.Struct, inferOnly));
        int idx = e.Index;
        var args = type.GetAppArgs();
        var I = type.GetAppFn();
        if (I is not ConstExpr iConst || iConst.Name != e.TypeName
            || Env.Find(iConst.Name) is not InductiveInfo iVal
            || iVal.Constructors.Count != 1 || args.Length != iVal.NumParams + iVal.NumIndices)
        {
            throw InvalidProj(e);
        }
        var cInfo = Env.Get(iVal.Constructors[0]);
        var r = ExprOps.InstantiateTypeLevelParams(cInfo, iConst.Levels);
        for (int i = 0; i < iVal.NumParams; i++)
        {
            r = Whnf(r);
            if (r is not ForallExpr p)
            {
                throw InvalidProj(e);
            }
            r = ExprOps.Instantiate(p.Body, args[i]);
        }
        bool isPropType = IsProp(type);
        for (int i = 0; i < idx; i++)
        {
            r = Whnf(r);
            if (r is not ForallExpr p)
            {
                throw InvalidProj(e);
            }
            if (p.Body.HasLooseBVars)
            {
                if (isPropType && !IsProp(p.BinderType))
                {
                    throw InvalidProj(e);
                }
                r = ExprOps.Instantiate(p.Body, Expr.Proj(iConst.Name, i, e.Struct));
            }
            else
            {
                r = p.Body;
            }
        }
        r = Whnf(r);
        if (r is not ForallExpr last)
        {
            throw InvalidProj(e);
        }
        r = last.BinderType;
        if (isPropType && !IsProp(r))
        {
            throw InvalidProj(e);
        }
        return r;
    }

    private static KernelException InvalidProj(ProjExpr e) => new($"invalid projection {e}");

    private void CheckNatSize(BigInteger n)
    {
        if (n.GetByteCount() > _limits.MaxNatBytes)
        {
            throw new KernelResourceException("the kernel refused a Nat numeral because its size exceeds the maximum");
        }
    }

    private sealed class ExprPairComparer : IEqualityComparer<(Expr, Expr)>
    {
        public static readonly ExprPairComparer Instance = new();

        public bool Equals((Expr, Expr) x, (Expr, Expr) y) => x.Item1.AlphaEquals(y.Item1) && x.Item2.AlphaEquals(y.Item2);

        public int GetHashCode((Expr, Expr) obj) => HashCode.Combine(obj.Item1.GetHashCode(), obj.Item2.GetHashCode());
    }
}
