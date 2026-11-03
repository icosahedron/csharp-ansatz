using System.Collections.Immutable;
using Warrant.Cic;

namespace Warrant.Meta;

/// <summary>What unification needs to know about one parameter of a function (Lean's <c>ParamInfo</c>).</summary>
/// <param name="BinderInfo">The binder annotation.</param>
/// <param name="HasFwdDeps">Whether a later parameter or the result type depends on it.</param>
/// <param name="BackDeps">The positions of earlier parameters its type depends on.</param>
/// <param name="IsProp">Whether its type is a proposition.</param>
/// <param name="IsInstance">Whether its type is a class and its binder is not explicit.</param>
/// <param name="HigherOrderOutParam">Whether it is a higher-order output parameter of an instance parameter.</param>
/// <param name="DependsOnHigherOrderOutParam">Whether its type depends on such an output parameter.</param>
public sealed record ParamInfo(
    BinderInfo BinderInfo,
    bool HasFwdDeps,
    ImmutableArray<int> BackDeps,
    bool IsProp,
    bool IsInstance,
    bool HigherOrderOutParam,
    bool DependsOnHigherOrderOutParam)
{
    /// <summary>Whether the binder is explicit.</summary>
    public bool IsExplicit => BinderInfo == BinderInfo.Default;

    /// <summary>Whether the binder is instance-implicit.</summary>
    public bool IsInstImplicit => BinderInfo == BinderInfo.InstImplicit;
}

/// <summary>Lean's <c>FunInfo</c>: parameter information of a function, for <c>isDefEqArgs</c>.</summary>
/// <param name="ParamInfo">One entry per parameter.</param>
/// <param name="ResultDeps">The parameters the result type depends on.</param>
public sealed record FunInfo(ImmutableArray<ParamInfo> ParamInfo, ImmutableArray<int> ResultDeps);

// A port of Lean/Meta/FunInfo.lean and the class test of Lean/Meta/Basic.lean (isClass?).
public sealed partial class MetaM
{
    private readonly Dictionary<(ulong, Expr, int), FunInfo> _funInfoCache = [];

    private static ImmutableArray<int> CollectDeps(IReadOnlyList<Expr> fvars, Expr e)
    {
        var deps = new SortedSet<int>();
        Visit(e);
        return [.. deps];

        void Visit(Expr e)
        {
            if (!e.HasFVar)
            {
                return;
            }
            switch (e)
            {
                case AppExpr a:
                    Visit(a.Fn);
                    Visit(a.Arg);
                    break;
                case BindingExpr b:
                    Visit(b.BinderType);
                    Visit(b.Body);
                    break;
                case LetExpr l:
                    Visit(l.BinderType);
                    Visit(l.Value);
                    Visit(l.Body);
                    break;
                case ProjExpr p:
                    Visit(p.Struct);
                    break;
                case MDataExpr m:
                    Visit(m.Expr);
                    break;
                case FVarExpr:
                    for (int i = 0; i < fvars.Count; i++)
                    {
                        if (fvars[i].Equals(e))
                        {
                            deps.Add(i);
                            break;
                        }
                    }
                    break;
            }
        }
    }

    private static List<ParamInfo> UpdateHasFwdDeps(List<ParamInfo> pinfo, ImmutableArray<int> backDeps)
    {
        foreach (int i in backDeps)
        {
            if (!pinfo[i].HasFwdDeps)
            {
                pinfo[i] = pinfo[i] with { HasFwdDeps = true };
            }
        }
        return pinfo;
    }

    private FunInfo GetFunInfoAux(Expr fn, int? maxArgs)
    {
        var key = (Config.Key, fn, maxArgs ?? -1);
        if (_funInfoCache.TryGetValue(key, out var cached))
        {
            return cached;
        }
        var fnType = InferType(fn);
        var info = WithAtLeastTransparency(TransparencyMode.Default, () => ForallBoundedTelescope(fnType, maxArgs, (fvars, type) =>
        {
            var paramInfo = new List<ParamInfo>();
            var higherOrderOutParams = new HashSet<FVarId>();
            for (int i = 0; i < fvars.Length; i++)
            {
                var decl = GetFVarLocalDecl(fvars[i]);
                var backDeps = CollectDeps(fvars, decl.Type);
                bool dependsOnHigherOrderOutParam = higherOrderOutParams.Count > 0
                    && Kernel.ExprOps.Find(decl.Type, (x, _) => x is FVarExpr fx && higherOrderOutParams.Contains(fx.Id)) is not null;
                var className = IsClass(decl.Type);
                bool isInstance = className is not null && decl.BinderInfo != BinderInfo.Default;
                UpdateHasFwdDeps(paramInfo, backDeps);
                paramInfo.Add(new ParamInfo(decl.BinderInfo, false, backDeps, IsProp(decl.Type), isInstance, false, dependsOnHigherOrderOutParam));
                if (isInstance && Attributes.GetOutParams(className!) is { IsEmpty: false } outParams)
                {
                    var args = decl.Type.GetAppArgs();
                    for (int k = 0; k < args.Length; k++)
                    {
                        if (!outParams.Contains(k))
                        {
                            continue;
                        }
                        int idx = Array.FindIndex(fvars, x => x.Equals(args[k]));
                        if (idx >= 0 && Whnf(InferType(args[k])) is ForallExpr)
                        {
                            paramInfo[idx] = paramInfo[idx] with { HigherOrderOutParam = true };
                            higherOrderOutParams.Add(((FVarExpr)args[k]).Id);
                        }
                    }
                }
            }
            var resultDeps = CollectDeps(fvars, type);
            UpdateHasFwdDeps(paramInfo, resultDeps);
            return new FunInfo([.. paramInfo], resultDeps);
        }));
        _funInfoCache[key] = info;
        return info;
    }

    /// <summary>Parameter information for <paramref name="fn"/>, as far as its type reduces (Lean's <c>getFunInfo</c>).</summary>
    public FunInfo GetFunInfo(Expr fn, int? maxArgs = null) => GetFunInfoAux(fn, maxArgs);

    /// <summary>Parameter information for <paramref name="fn"/> applied to <paramref name="nargs"/> arguments (Lean's <c>getFunInfoNArgs</c>).</summary>
    public FunInfo GetFunInfoNArgs(Expr fn, int nargs) => GetFunInfoAux(fn, nargs);

    private LBool IsClassQuickConst(Name constName, out Name? className)
    {
        className = null;
        if (Attributes.IsClass(constName))
        {
            className = constName;
            return LBool.True;
        }
        var info = Env.Find(constName) ?? throw new MetaException($"unknown constant '{constName}'");
        // Lean's getConstTemp?: a definition we may be able to unfold (reducible, or any at default and all).
        if (info is DefinitionInfo && (GetTransparency() is TransparencyMode.All or TransparencyMode.Default || IsReducible(constName)))
        {
            return LBool.Undef;
        }
        return LBool.False;
    }

    private LBool IsClassQuick(Expr e, out Name? className)
    {
        className = null;
        switch (e)
        {
            case BVarExpr or NatLitExpr or StrLitExpr or FVarExpr or SortExpr or LamExpr:
                return LBool.False;
            case LetExpr or ProjExpr:
                return LBool.Undef;
            case ForallExpr f:
                return IsClassQuick(f.Body, out className);
            case MDataExpr m:
                return IsClassQuick(m.Expr, out className);
            case ConstExpr c:
                return IsClassQuickConst(c.Name, out className);
            case MVarExpr mv:
                return MCtx.GetExprAssignment(mv.Id) is { } val ? IsClassQuick(val, out className) : LBool.False;
            case AppExpr:
                switch (e.GetAppFn())
                {
                    case ConstExpr c:
                        return IsClassQuickConst(c.Name, out className);
                    case LamExpr:
                        return LBool.Undef;
                    case MVarExpr mv:
                        if (MCtx.GetExprAssignment(mv.Id) is not { } v)
                        {
                            return LBool.False;
                        }
                        return v.GetAppFn() is ConstExpr vc ? IsClassQuickConst(vc.Name, out className) : LBool.Undef;
                    default:
                        return LBool.False;
                }
            default:
                return LBool.False;
        }
    }

    private Name? IsClassExpensive(Expr type) =>
        WithReducible(() => ForallTelescopeReducing(type, (_, t) =>
            t.GetAppFn() is ConstExpr c && Attributes.IsClass(c.Name) ? c.Name : null, whnfType: true));

    /// <summary>The class <paramref name="type"/> is an instance of, if any (Lean's <c>isClass?</c>).</summary>
    public Name? IsClass(Expr type)
    {
        ArgumentNullException.ThrowIfNull(type);
        try
        {
            return IsClassQuick(type, out var c) switch
            {
                LBool.True => c,
                LBool.False => null,
                _ => IsClassExpensive(type),
            };
        }
        catch (MetaException ex) when (ex is not MetaResourceException)
        {
            return null;
        }
    }
}
