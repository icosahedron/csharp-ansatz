using Warrant.Cic;
using Warrant.Kernel;

namespace Warrant.Meta;

/// <summary>Lean's <c>LBool</c>: a three-valued answer.</summary>
internal enum LBool
{
    False,
    True,
    Undef,
}

// Type inference (a port of Lean 4.35.0's Lean/Meta/InferType.lean). Inference does not check:
// it assumes its input is type correct, as Lean's does, and the kernel checks the final term.
public sealed partial class MetaM
{
    private readonly Dictionary<(ulong, Expr), Expr> _inferTypeCache = [];

    /// <summary>
    /// Instantiates the loose bound variables of <paramref name="e"/> with
    /// <c>args[start..stop)</c>, beta-reducing where a substituted lambda lands at the head of an
    /// application (Lean's <c>Expr.instantiateBetaRevRange</c>, InferType.lean 37).
    /// </summary>
    internal static Expr InstantiateBetaRevRange(Expr e, int start, int stop, IReadOnlyList<Expr> args)
    {
        if (!e.HasLooseBVars || stop <= start)
        {
            return e;
        }
        bool anyLambda = false;
        for (int i = start; i < stop; i++)
        {
            if (args[i].ConsumeMData() is LamExpr)
            {
                anyLambda = true;
                break;
            }
        }
        if (!anyLambda)
        {
            return e.InstantiateRevRange(start, stop, args);
        }
        var cache = new Dictionary<(Expr, int), Expr>(RefOffsetComparer.Instance);
        int n = stop - start;
        return Visit(e, 0);

        Expr VisitBVar(int vidx, int offset) =>
            vidx < offset + n ? ExprOps.LiftLooseBVars(args[stop - (vidx - offset) - 1], 0, offset) : Expr.BVar(vidx - n);

        Expr VisitWithoutBeta(Expr e, int offset)
        {
            if (offset >= e.LooseBVarRange)
            {
                return e;
            }
            if (e is AppExpr app)
            {
                if (cache.TryGetValue((e, offset), out var c))
                {
                    return c;
                }
                var r = VisitApp(app, offset);
                cache[(e, offset)] = r;
                return r;
            }
            return Visit(e, offset);
        }

        Expr VisitApp(AppExpr e, int offset) => e.UpdateApp(VisitWithoutBeta(e.Fn, offset), Visit(e.Arg, offset));

        Expr Visit(Expr e, int offset)
        {
            if (offset >= e.LooseBVarRange)
            {
                return e;
            }
            if (cache.TryGetValue((e, offset), out var c))
            {
                return c;
            }
            Expr r;
            switch (e)
            {
                case BindingExpr b:
                    r = b.UpdateBinding(Visit(b.BinderType, offset), Visit(b.Body, offset + 1));
                    break;
                case LetExpr l:
                    r = l.UpdateLet(Visit(l.BinderType, offset), Visit(l.Value, offset), Visit(l.Body, offset + 1));
                    break;
                case MDataExpr m:
                    r = m.UpdateMData(Visit(m.Expr, offset));
                    break;
                case ProjExpr p:
                    r = p.UpdateProj(Visit(p.Struct, offset));
                    break;
                case BVarExpr bv:
                    r = VisitBVar(bv.Index, offset);
                    break;
                case AppExpr app:
                    if (e.GetAppFn() is BVarExpr)
                    {
                        var head = Visit(e.GetAppFn(), offset);
                        var revArgs = e.GetAppRevArgs();
                        for (int i = 0; i < revArgs.Length; i++)
                        {
                            revArgs[i] = Visit(revArgs[i], offset);
                        }
                        r = head.BetaRev(revArgs);
                    }
                    else
                    {
                        r = VisitApp(app, offset);
                    }
                    break;
                default:
                    throw new InvalidOperationException("unreachable: no loose bound variables");
            }
            cache[(e, offset)] = r;
            return r;
        }
    }

    private sealed class RefOffsetComparer : IEqualityComparer<(Expr, int)>
    {
        public static readonly RefOffsetComparer Instance = new();

        public bool Equals((Expr, int) x, (Expr, int) y) => ReferenceEquals(x.Item1, y.Item1) && x.Item2 == y.Item2;

        public int GetHashCode((Expr, int) obj) => HashCode.Combine(System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(obj.Item1), obj.Item2);
    }

    private static MetaException FunctionExpected(Expr f) => new($"function expected {f}");

    private Expr InferAppType(Expr f, Expr[] args)
    {
        var fType = InferType(f);
        int j = 0;
        for (int i = 0; i < args.Length; i++)
        {
            if (fType is ForallExpr fa)
            {
                fType = fa.Body;
                continue;
            }
            if (Whnf(InstantiateBetaRevRange(fType, j, i, args)) is ForallExpr fb)
            {
                j = i;
                fType = fb.Body;
            }
            else
            {
                throw FunctionExpected(ExprExtensions.MkAppRange(f, 0, i + 1, args));
            }
        }
        return InstantiateBetaRevRange(fType, j, args.Length, args);
    }

    private Expr InferConstType(Name c, EquatableArray<Level> us)
    {
        var cinfo = GetConstInfo(c);
        if (cinfo.LevelParams.Count != us.Count)
        {
            throw new MetaException($"incorrect number of universe levels {Expr.Const(c, us)}");
        }
        return ExprOps.InstantiateTypeLevelParams(cinfo, us);
    }

    private Expr InferProjType(Name structName, int idx, Expr e)
    {
        var structType = Whnf(InferType(e));
        MetaException Failed() => new($"invalid projection {Expr.Proj(structName, idx, e)} from type {structType}");
        if (structType.GetAppFn() is not ConstExpr sc || Env.Find(sc.Name) is not InductiveInfo { Constructors.Count: 1 } structVal
            || Env.Find(structVal.Constructors[0]) is not ConstructorInfo ctorVal)
        {
            throw Failed();
        }
        if (structVal.Name != structName)
        {
            throw Failed();
        }
        var structTypeArgs = structType.GetAppArgs();
        if (structVal.NumParams + structVal.NumIndices != structTypeArgs.Length)
        {
            throw Failed();
        }
        var ctorType = InferAppType(Expr.Const(ctorVal.Name, sc.Levels), structTypeArgs[..structVal.NumParams]);
        for (int i = 0; i < idx; i++)
        {
            ctorType = Whnf(ctorType);
            if (ctorType is not ForallExpr f)
            {
                throw Failed();
            }
            ctorType = f.Body.HasLooseBVars ? ExprOps.Instantiate(f.Body, Expr.Proj(structName, i, e)) : f.Body;
        }
        ctorType = Whnf(ctorType);
        return ctorType is ForallExpr fd ? ExprOps.ConsumeTypeAnnotations(fd.BinderType) : throw Failed();
    }

    /// <summary>
    /// The universe <c>u</c> of a type <paramref name="type"/> <c>: Sort u</c> (Lean's
    /// <c>getLevel</c>). If its type is an assignable metavariable, it is assigned <c>Sort ?u</c>.
    /// </summary>
    /// <exception cref="MetaException">It is not a type.</exception>
    public Level GetLevel(Expr type)
    {
        var typeType = WhnfD(InferType(type));
        switch (typeType)
        {
            case SortExpr s:
                return s.Level;
            case MVarExpr mv:
                if (IsReadOnlyOrSyntheticOpaque(mv.Id))
                {
                    throw new MetaException($"type expected {type}");
                }
                var lvl = MkFreshLevelMVar();
                Assign(mv.Id, Expr.Sort(lvl));
                return lvl;
            default:
                throw new MetaException($"type expected {type}");
        }
    }

    private Expr InferForallType(Expr e) => ForallTelescope(e, (xs, body) =>
    {
        var lvl = GetLevel(body);
        for (int i = xs.Length - 1; i >= 0; i--)
        {
            var xTypeLvl = GetLevel(InferType(xs[i]));
            lvl = LevelOps.MkIMax(xTypeLvl, lvl);
        }
        return (Expr)Expr.Sort(LevelOps.Normalize(lvl));
    });

    private Expr InferLambdaType(Expr e) => LambdaLetTelescope(e, (xs, body) =>
        MkForallFVars(xs, InferType(body), generalizeNondepLet: false));

    private Expr InferMVarType(MVarId mvarId) =>
        MCtx.FindDecl(mvarId)?.Type ?? throw new MetaException($"unknown metavariable '?{mvarId}'");

    private Expr InferFVarType(FVarId fvarId) =>
        LCtx.Find(fvarId)?.Type ?? throw new MetaException($"unknown free variable '{fvarId}'");

    private Expr CheckInferTypeCache(Expr e, Func<Expr> infer)
    {
        if (e.HasExprMVar || e.HasLevelMVar)
        {
            return infer();
        }
        var key = (Config.Key, e);
        if (_inferTypeCache.TryGetValue(key, out var type))
        {
            return type;
        }
        type = infer();
        if (!type.HasExprMVar && !type.HasLevelMVar)
        {
            _inferTypeCache[key] = type;
        }
        return type;
    }

    /// <summary>
    /// The type of <paramref name="e"/>, which must be type correct (Lean's <c>inferType</c>). It
    /// runs at least at <c>default</c> transparency and does not check.
    /// </summary>
    /// <exception cref="MetaException">The type cannot be inferred.</exception>
    public Expr InferType(Expr e)
    {
        ArgumentNullException.ThrowIfNull(e);
        Budget.Tick();
        return WithInferTypeConfig(() => Infer(e));

        Expr Infer(Expr e) => e switch
        {
            ConstExpr { Levels.Count: 0 } c => InferConstType(c.Name, c.Levels),
            ConstExpr c => CheckInferTypeCache(e, () => InferConstType(c.Name, c.Levels)),
            ProjExpr p => CheckInferTypeCache(e, () => InferProjType(p.TypeName, p.Index, p.Struct)),
            AppExpr => CheckInferTypeCache(e, () => InferAppType(e.GetAppFn(), e.GetAppArgs())),
            MVarExpr mv => InferMVarType(mv.Id),
            FVarExpr fv => InferFVarType(fv.Id),
            BVarExpr bv => throw new MetaException($"unexpected bound variable #{bv.Index}"),
            MDataExpr m => Infer(m.Expr),
            NatLitExpr => MetaNames.NatConst,
            StrLitExpr => Expr.Const(KernelNames.StringType),
            SortExpr s => Expr.Sort(Level.Succ(s.Level)),
            ForallExpr => CheckInferTypeCache(e, () => InferForallType(e)),
            _ => CheckInferTypeCache(e, () => InferLambdaType(e)), // lambda and let
        };
    }

    private static bool IsAlwaysZero(Level l) => l.Kind switch
    {
        LevelKind.Zero => true,
        LevelKind.Max => IsAlwaysZero(l.Lhs!) && IsAlwaysZero(l.Rhs!),
        LevelKind.IMax => IsAlwaysZero(l.Rhs!),
        _ => false,
    };

    private LBool IsArrowProp(Expr type, int n)
    {
        while (true)
        {
            switch (type)
            {
                case SortExpr s when n == 0:
                    return IsAlwaysZero(this.InstantiateLevelMVars(s.Level)) ? LBool.True : LBool.False;
                case ForallExpr when n == 0:
                    return LBool.False;
                case ForallExpr f:
                    type = f.Body;
                    n--;
                    continue;
                case LetExpr l:
                    type = l.Body;
                    continue;
                case MDataExpr m:
                    type = m.Expr;
                    continue;
                default:
                    return LBool.Undef;
            }
        }
    }

    private LBool IsPropQuickApp(Expr f, int arity)
    {
        while (true)
        {
            switch (f)
            {
                case ConstExpr c:
                    return IsArrowProp(InferConstType(c.Name, c.Levels), arity);
                case FVarExpr fv:
                    return IsArrowProp(InferFVarType(fv.Id), arity);
                case MVarExpr mv:
                    return IsArrowProp(InferMVarType(mv.Id), arity);
                case AppExpr a:
                    f = a.Fn;
                    arity++;
                    continue;
                case MDataExpr m:
                    f = m.Expr;
                    continue;
                case LetExpr l:
                    f = l.Body;
                    continue;
                case LamExpr when arity == 0:
                    return LBool.False;
                case LamExpr lam:
                    f = lam.Body;
                    arity--;
                    continue;
                default:
                    return LBool.Undef;
            }
        }
    }

    /// <summary>Lean's <c>isPropQuick</c>: whether <paramref name="e"/> is a proposition, cheaply.</summary>
    internal LBool IsPropQuick(Expr e)
    {
        while (true)
        {
            switch (e)
            {
                case BVarExpr or ProjExpr:
                    return LBool.Undef;
                case NatLitExpr or StrLitExpr or SortExpr or LamExpr:
                    return LBool.False;
                case LetExpr l:
                    e = l.Body;
                    continue;
                case ForallExpr f:
                    e = f.Body;
                    continue;
                case MDataExpr m:
                    e = m.Expr;
                    continue;
                case ConstExpr c:
                    return IsArrowProp(InferConstType(c.Name, c.Levels), 0);
                case FVarExpr fv:
                    return IsArrowProp(InferFVarType(fv.Id), 0);
                case MVarExpr mv:
                    return IsArrowProp(InferMVarType(mv.Id), 0);
                case AppExpr a:
                    return IsPropQuickApp(a.Fn, 1);
                default:
                    return LBool.Undef;
            }
        }
    }

    /// <summary>
    /// Whether <paramref name="e"/> is a proposition (Lean's <c>isProp</c>); false when
    /// metavariables leave it undetermined.
    /// </summary>
    public bool IsProp(Expr e)
    {
        switch (IsPropQuick(e))
        {
            case LBool.True:
                return true;
            case LBool.False:
                return false;
        }
        return WhnfD(InferType(e)) is SortExpr s && IsAlwaysZero(this.InstantiateLevelMVars(s.Level));
    }

    // Lean's ArrowPropResult: false, true, undef, or `bvar idx` (encoded as idx >= 0).
    private readonly record struct ArrowPropResult(LBool Value, int BVar = -1);

    private ArrowPropResult IsArrowProposition1(Expr e, int n)
    {
        switch (e)
        {
            case ForallExpr f when n > 0:
                return ProcessResult(IsArrowProposition1(f.Body, n - 1), f.BinderType);
            case LetExpr l:
                return ProcessResult(IsArrowProposition1(l.Body, n), l.BinderType);
            case MDataExpr m:
                return IsArrowProposition1(m.Expr, n);
            case BVarExpr b when n == 0:
                return new(LBool.Undef, b.Index);
            case var t when n == 0:
                return new(IsPropQuick(t));
            default:
                return new(LBool.Undef);
        }

        static ArrowPropResult ProcessResult(ArrowPropResult r, Expr binderType) => r.BVar switch
        {
            0 => CheckProp(binderType),
            > 0 => new(LBool.Undef, r.BVar - 1),
            _ => r,
        };

        static ArrowPropResult CheckProp(Expr e) => e switch
        {
            SortExpr s => s.Level.IsNeverZero() ? new(LBool.False) : s.Level.Kind == LevelKind.Zero ? new(LBool.True) : new(LBool.Undef),
            AppExpr { Fn: ConstExpr c, Arg: var a } when c.Name == MetaNames.OutParam => CheckProp(a),
            _ => new(LBool.Undef),
        };
    }

    private LBool IsArrowProposition(Expr e, int n)
    {
        var r = IsArrowProposition1(e, n);
        return r.BVar >= 0 ? LBool.Undef : r.Value;
    }

    private LBool IsProofQuickApp(Expr f, int arity)
    {
        while (true)
        {
            switch (f)
            {
                case ConstExpr c:
                    return IsArrowProposition(InferConstType(c.Name, c.Levels), arity);
                case FVarExpr fv:
                    return IsArrowProposition(InferFVarType(fv.Id), arity);
                case MVarExpr mv:
                    return IsArrowProposition(InferMVarType(mv.Id), arity);
                case AppExpr a:
                    f = a.Fn;
                    arity++;
                    continue;
                case MDataExpr m:
                    f = m.Expr;
                    continue;
                case LetExpr l:
                    f = l.Body;
                    continue;
                case LamExpr lam when arity == 0:
                    return IsProofQuick(lam.Body);
                case LamExpr lam:
                    f = lam.Body;
                    arity--;
                    continue;
                default:
                    return LBool.Undef;
            }
        }
    }

    /// <summary>Lean's <c>isProofQuick</c>: whether <paramref name="e"/> is a proof, cheaply.</summary>
    internal LBool IsProofQuick(Expr e)
    {
        while (true)
        {
            switch (e)
            {
                case BVarExpr or ProjExpr:
                    return LBool.Undef;
                case NatLitExpr or StrLitExpr or SortExpr or ForallExpr:
                    return LBool.False;
                case LamExpr lam:
                    e = lam.Body;
                    continue;
                case LetExpr l:
                    e = l.Body;
                    continue;
                case MDataExpr m:
                    e = m.Expr;
                    continue;
                case ConstExpr c:
                    return IsArrowProposition(InferConstType(c.Name, c.Levels), 0);
                case FVarExpr fv:
                    return IsArrowProposition(InferFVarType(fv.Id), 0);
                case MVarExpr mv:
                    return IsArrowProposition(InferMVarType(mv.Id), 0);
                case AppExpr a:
                    return IsProofQuickApp(a.Fn, 1);
                default:
                    return LBool.Undef;
            }
        }
    }

    /// <summary>Whether <paramref name="e"/> is a proof, i.e. its type is a proposition (Lean's <c>isProof</c>).</summary>
    public bool IsProof(Expr e) => IsProofQuick(e) switch
    {
        LBool.True => true,
        LBool.False => false,
        _ => IsProp(InferType(e)),
    };

    private static LBool IsArrowType(Expr e, int n)
    {
        while (true)
        {
            switch (e)
            {
                case SortExpr when n == 0:
                    return LBool.True;
                case ForallExpr when n == 0:
                    return LBool.False;
                case ForallExpr f:
                    e = f.Body;
                    n--;
                    continue;
                case LetExpr l:
                    e = l.Body;
                    continue;
                case MDataExpr m:
                    e = m.Expr;
                    continue;
                default:
                    return LBool.Undef;
            }
        }
    }

    private LBool IsTypeQuickApp(Expr f, int arity)
    {
        while (true)
        {
            switch (f)
            {
                case ConstExpr c:
                    return IsArrowType(InferConstType(c.Name, c.Levels), arity);
                case FVarExpr fv:
                    return IsArrowType(InferFVarType(fv.Id), arity);
                case MVarExpr mv:
                    return IsArrowType(InferMVarType(mv.Id), arity);
                case AppExpr a:
                    f = a.Fn;
                    arity++;
                    continue;
                case MDataExpr m:
                    f = m.Expr;
                    continue;
                case LetExpr l:
                    f = l.Body;
                    continue;
                case LamExpr when arity == 0:
                    return LBool.False;
                case LamExpr lam:
                    f = lam.Body;
                    arity--;
                    continue;
                default:
                    return LBool.Undef;
            }
        }
    }

    private LBool IsTypeQuick(Expr e)
    {
        while (true)
        {
            switch (e)
            {
                case BVarExpr or ProjExpr:
                    return LBool.Undef;
                case NatLitExpr or StrLitExpr or LamExpr:
                    return LBool.False;
                case SortExpr or ForallExpr:
                    return LBool.True;
                case LetExpr l:
                    e = l.Body;
                    continue;
                case MDataExpr m:
                    e = m.Expr;
                    continue;
                case ConstExpr c:
                    return IsArrowType(InferConstType(c.Name, c.Levels), 0);
                case FVarExpr fv:
                    return IsArrowType(InferFVarType(fv.Id), 0);
                case MVarExpr mv:
                    return IsArrowType(InferMVarType(mv.Id), 0);
                case AppExpr a:
                    return IsTypeQuickApp(a.Fn, 1);
                default:
                    return LBool.Undef;
            }
        }
    }

    /// <summary>Whether the type of <paramref name="e"/> is a sort (Lean's <c>isType</c>).</summary>
    public bool IsType(Expr e) => IsTypeQuick(e) switch
    {
        LBool.True => true,
        LBool.False => false,
        _ => WhnfD(InferType(e)) is SortExpr,
    };

    /// <summary><c>u</c> if <paramref name="type"/> is <c>Sort u</c> or <c>As → Sort u</c> (Lean's <c>typeFormerTypeLevel</c>).</summary>
    public Level? TypeFormerTypeLevel(Expr type)
    {
        var t = type;
        while (t is ForallExpr f)
        {
            t = f.Body;
        }
        if (t is SortExpr s0)
        {
            return s0.Level;
        }
        return Go(type, []);

        Level? Go(Expr type, List<Expr> xs)
        {
            switch (type)
            {
                case SortExpr s:
                    return s.Level;
                case ForallExpr f:
                    return WithLocalDecl(f.BinderName, f.BinderInfo, f.BinderType.InstantiateRev(xs), x => Go(f.Body, [.. xs, x]));
                default:
                    var r = WhnfD(type.InstantiateRev(xs));
                    return r switch
                    {
                        SortExpr s => s.Level,
                        ForallExpr => Go(r, []),
                        _ => null,
                    };
            }
        }
    }

    /// <summary>Whether <paramref name="type"/> is <c>Sort _</c> or <c>As → Sort _</c> (Lean's <c>isTypeFormerType</c>).</summary>
    public bool IsTypeFormerType(Expr type) => TypeFormerTypeLevel(type) is not null;

    /// <summary>Whether <paramref name="type"/> is <c>Prop</c> or <c>As → Prop</c> (Lean's <c>isPropFormerType</c>).</summary>
    public bool IsPropFormerType(Expr type) => TypeFormerTypeLevel(type) is { Kind: LevelKind.Zero };

    /// <summary>Whether the type of <paramref name="e"/> is a type-former type (Lean's <c>isTypeFormer</c>).</summary>
    public bool IsTypeFormer(Expr e) => IsTypeFormerType(InferType(e));
}
