using System.Runtime.CompilerServices;
using Warrant.Cic;

namespace Warrant.Kernel;

/// <summary>
/// Operations on expressions used by the kernel: substitution of bound variables, abstraction of
/// free variables, lifting and lowering of de Bruijn indices, universe-parameter instantiation and
/// beta reduction. A port of Lean 4's <c>instantiate.cpp</c>, <c>abstract.cpp</c>,
/// <c>replace_fn.cpp</c> and parts of <c>expr.cpp</c>.
/// </summary>
/// <remarks>
/// Traversals are recursive (as in Lean's C++ kernel) and are meant to run on a thread with a large
/// stack; see <see cref="KernelThread"/>. Results for compound subterms are cached by node identity
/// and binder offset, so shared DAGs are processed once.
/// </remarks>
public static class ExprOps
{
    /// <summary>
    /// Rebuilds <paramref name="e"/> bottom-up. <paramref name="f"/> is called with each subterm and
    /// the number of binders above it; a non-null result replaces the subterm (and is not descended
    /// into), null means "descend".
    /// </summary>
    public static Expr Replace(Expr e, Func<Expr, int, Expr?> f) => new Replacer(f).Apply(e, 0);

    private sealed class Replacer(Func<Expr, int, Expr?> f)
    {
        private Dictionary<(Expr, int), Expr>? _cache;

        public Expr Apply(Expr e, int offset)
        {
            bool compound = e.Kind is ExprKind.App or ExprKind.Lam or ExprKind.Forall or ExprKind.Let or ExprKind.MData or ExprKind.Proj;
            if (compound && _cache is not null && _cache.TryGetValue((e, offset), out var cached))
            {
                return cached;
            }
            var r = f(e, offset) ?? e switch
            {
                AppExpr a => UpdateApp(a, Apply(a.Fn, offset), Apply(a.Arg, offset)),
                LamExpr l => UpdateBinding(l, Apply(l.BinderType, offset), Apply(l.Body, offset + 1)),
                ForallExpr p => UpdateBinding(p, Apply(p.BinderType, offset), Apply(p.Body, offset + 1)),
                LetExpr l => UpdateLet(l, Apply(l.BinderType, offset), Apply(l.Value, offset), Apply(l.Body, offset + 1)),
                MDataExpr m => UpdateMData(m, Apply(m.Expr, offset)),
                ProjExpr p => UpdateProj(p, Apply(p.Struct, offset)),
                _ => e,
            };
            if (compound)
            {
                (_cache ??= new Dictionary<(Expr, int), Expr>(RefOffsetComparer.Instance))[(e, offset)] = r;
            }
            return r;
        }
    }

    /// <summary>
    /// Finds a subterm satisfying <paramref name="pred"/> (given the subterm and its binder offset),
    /// visiting each shared subterm/offset pair once.
    /// </summary>
    public static Expr? Find(Expr e, Func<Expr, int, bool> pred)
    {
        var visited = new HashSet<(Expr, int)>(RefOffsetComparer.Instance);
        return FindCore(e, 0, pred, visited);
    }

    private static Expr? FindCore(Expr e, int offset, Func<Expr, int, bool> pred, HashSet<(Expr, int)> visited)
    {
        bool compound = e.Kind is ExprKind.App or ExprKind.Lam or ExprKind.Forall or ExprKind.Let or ExprKind.MData or ExprKind.Proj;
        if (compound && !visited.Add((e, offset)))
        {
            return null;
        }
        if (pred(e, offset))
        {
            return e;
        }
        return e switch
        {
            AppExpr a => FindCore(a.Fn, offset, pred, visited) ?? FindCore(a.Arg, offset, pred, visited),
            BindingExpr b => FindCore(b.BinderType, offset, pred, visited) ?? FindCore(b.Body, offset + 1, pred, visited),
            LetExpr l => FindCore(l.BinderType, offset, pred, visited) ?? FindCore(l.Value, offset, pred, visited) ?? FindCore(l.Body, offset + 1, pred, visited),
            MDataExpr m => FindCore(m.Expr, offset, pred, visited),
            ProjExpr p => FindCore(p.Struct, offset, pred, visited),
            _ => null,
        };
    }

    /// <summary>
    /// Visits subterms (with binder offsets); descends into a subterm only while
    /// <paramref name="visit"/> returns true. Shared subterm/offset pairs are visited once.
    /// </summary>
    public static void ForEach(Expr e, Func<Expr, int, bool> visit)
    {
        var visited = new HashSet<(Expr, int)>(RefOffsetComparer.Instance);
        ForEachCore(e, 0, visit, visited);
    }

    private static void ForEachCore(Expr e, int offset, Func<Expr, int, bool> visit, HashSet<(Expr, int)> visited)
    {
        bool compound = e.Kind is ExprKind.App or ExprKind.Lam or ExprKind.Forall or ExprKind.Let or ExprKind.MData or ExprKind.Proj;
        if (compound && !visited.Add((e, offset)))
        {
            return;
        }
        if (!visit(e, offset))
        {
            return;
        }
        switch (e)
        {
            case AppExpr a:
                ForEachCore(a.Fn, offset, visit, visited);
                ForEachCore(a.Arg, offset, visit, visited);
                break;
            case BindingExpr b:
                ForEachCore(b.BinderType, offset, visit, visited);
                ForEachCore(b.Body, offset + 1, visit, visited);
                break;
            case LetExpr l:
                ForEachCore(l.BinderType, offset, visit, visited);
                ForEachCore(l.Value, offset, visit, visited);
                ForEachCore(l.Body, offset + 1, visit, visited);
                break;
            case MDataExpr m:
                ForEachCore(m.Expr, offset, visit, visited);
                break;
            case ProjExpr p:
                ForEachCore(p.Struct, offset, visit, visited);
                break;
        }
    }

    // ------------------------------------------------------------------ bound variables

    /// <summary>
    /// Replaces loose bound variables <c>#s … #(s+n-1)</c> by <c>subst[0] … subst[n-1]</c> (lifted
    /// under binders) and lowers the loose variables above them by <c>n</c>.
    /// </summary>
    public static Expr Instantiate(Expr e, int s, ReadOnlySpan<Expr> subst)
    {
        int n = subst.Length;
        if (s >= e.LooseBVarRange || n == 0)
        {
            return e;
        }
        var arr = subst.ToArray();
        return Replace(e, (m, offset) =>
        {
            int s1 = s + offset;
            if (s1 >= m.LooseBVarRange)
            {
                return m;
            }
            if (m is BVarExpr b && b.Index >= s1)
            {
                return b.Index < s1 + n ? LiftLooseBVars(arr[b.Index - s1], 0, offset) : Expr.BVar(b.Index - n);
            }
            return null;
        });
    }

    /// <summary>Replaces <c>#0 … #(n-1)</c> by <c>subst[0] … subst[n-1]</c>.</summary>
    public static Expr Instantiate(Expr e, ReadOnlySpan<Expr> subst) => Instantiate(e, 0, subst);

    /// <summary>Replaces <c>#0</c> by <paramref name="value"/>.</summary>
    public static Expr Instantiate(Expr e, Expr value) => Instantiate(e, 0, [value]);

    /// <summary>Replaces <c>#0 … #(n-1)</c> by <c>subst[n-1] … subst[0]</c> (the innermost binder gets the last element).</summary>
    public static Expr InstantiateRev(Expr e, ReadOnlySpan<Expr> subst)
    {
        int n = subst.Length;
        if (!e.HasLooseBVars || n == 0)
        {
            return e;
        }
        var arr = subst.ToArray();
        return Replace(e, (m, offset) =>
        {
            if (offset >= m.LooseBVarRange)
            {
                return m;
            }
            if (m is BVarExpr b && b.Index >= offset)
            {
                return b.Index < offset + n
                    ? LiftLooseBVars(arr[n - (b.Index - offset) - 1], 0, offset)
                    : Expr.BVar(b.Index - n);
            }
            return null;
        });
    }

    /// <summary>Adds <paramref name="d"/> to every loose bound variable with index ≥ <paramref name="s"/>.</summary>
    public static Expr LiftLooseBVars(Expr e, int s, int d)
    {
        if (d == 0 || s >= e.LooseBVarRange)
        {
            return e;
        }
        return Replace(e, (m, offset) =>
        {
            int s1 = s + offset;
            if (s1 >= m.LooseBVarRange)
            {
                return m;
            }
            if (m is BVarExpr b && b.Index >= s1)
            {
                return Expr.BVar(b.Index + d);
            }
            return null;
        });
    }

    /// <summary>Subtracts <paramref name="d"/> from every loose bound variable with index ≥ <paramref name="s"/>.</summary>
    public static Expr LowerLooseBVars(Expr e, int s, int d)
    {
        if (d == 0 || s >= e.LooseBVarRange)
        {
            return e;
        }
        return Replace(e, (m, offset) =>
        {
            int s1 = s + offset;
            if (s1 >= m.LooseBVarRange)
            {
                return m;
            }
            if (m is BVarExpr b && b.Index >= s1)
            {
                return Expr.BVar(b.Index - d);
            }
            return null;
        });
    }

    /// <summary>Whether the loose bound variable <c>#i</c> occurs in <paramref name="e"/>.</summary>
    public static bool HasLooseBVar(Expr e, int i)
    {
        if (!e.HasLooseBVars)
        {
            return false;
        }
        bool found = false;
        ForEach(e, (m, offset) =>
        {
            if (found)
            {
                return false;
            }
            int ni = i + offset;
            if (ni >= m.LooseBVarRange)
            {
                return false;
            }
            if (m is BVarExpr b && b.Index == ni)
            {
                found = true;
            }
            return true;
        });
        return found;
    }

    /// <summary>
    /// Replaces the free variables <c>fvars[0] … fvars[n-1]</c> by bound variables, so that
    /// <c>fvars[n-1]</c> becomes <c>#0</c> (the innermost binder).
    /// </summary>
    public static Expr Abstract(Expr e, ReadOnlySpan<Expr> fvars)
    {
        if (!e.HasFVar || fvars.Length == 0)
        {
            return e;
        }
        int n = fvars.Length;
        var ids = new FVarId[n];
        for (int i = 0; i < n; i++)
        {
            ids[i] = ((FVarExpr)fvars[i]).Id;
        }
        return Replace(e, (m, offset) =>
        {
            if (!m.HasFVar)
            {
                return m;
            }
            if (m is FVarExpr f)
            {
                for (int i = n - 1; i >= 0; i--)
                {
                    if (ids[i] == f.Id)
                    {
                        return Expr.BVar(offset + n - i - 1);
                    }
                }
                return m;
            }
            return null;
        });
    }

    // ------------------------------------------------------------------ universe parameters

    /// <summary>Substitutes <paramref name="levels"/> for the universe parameters <paramref name="names"/>.</summary>
    public static Expr InstantiateLevelParams(Expr e, EquatableArray<Name> names, EquatableArray<Level> levels)
    {
        if (!e.HasLevelParam || names.Count == 0)
        {
            return e;
        }
        return Replace(e, (m, _) =>
        {
            if (!m.HasLevelParam)
            {
                return m;
            }
            return m switch
            {
                ConstExpr c => UpdateConst(c, c.Levels.Select(l => LevelOps.Instantiate(l, names, levels)).ToEquatableArray()),
                SortExpr s => UpdateSort(s, LevelOps.Instantiate(s.Level, names, levels)),
                _ => null,
            };
        });
    }

    /// <summary>The type of <paramref name="info"/> instantiated at <paramref name="levels"/>.</summary>
    public static Expr InstantiateTypeLevelParams(ConstantInfo info, EquatableArray<Level> levels)
    {
        if (info.LevelParams.Count != levels.Count)
        {
            throw new KernelException($"#universes mismatch instantiating the type of '{info.Name}'");
        }
        return levels.Count == 0 ? info.Type : InstantiateLevelParams(info.Type, info.LevelParams, levels);
    }

    /// <summary>The value of <paramref name="info"/> instantiated at <paramref name="levels"/>.</summary>
    public static Expr InstantiateValueLevelParams(ConstantInfo info, EquatableArray<Level> levels)
    {
        var value = info.Value ?? throw new KernelException($"'{info.Name}' has no value");
        if (info.LevelParams.Count != levels.Count)
        {
            throw new KernelException($"#universes mismatch instantiating the value of '{info.Name}'");
        }
        return levels.Count == 0 ? value : InstantiateLevelParams(value, info.LevelParams, levels);
    }

    // ------------------------------------------------------------------ applications and beta

    /// <summary><c>fn args[0] … args[n-1]</c>.</summary>
    public static Expr MkApp(Expr fn, ReadOnlySpan<Expr> args)
    {
        var e = fn;
        foreach (var a in args)
        {
            e = Expr.App(e, a);
        }
        return e;
    }

    /// <summary><c>fn revArgs[n-1] … revArgs[0]</c> (arguments given in reverse order).</summary>
    public static Expr MkRevApp(Expr fn, ReadOnlySpan<Expr> revArgs)
    {
        var e = fn;
        for (int i = revArgs.Length - 1; i >= 0; i--)
        {
            e = Expr.App(e, revArgs[i]);
        }
        return e;
    }

    /// <summary>The arguments of an application spine in reverse order (last argument first), and its head.</summary>
    public static Expr GetAppRevArgs(Expr e, List<Expr> revArgs)
    {
        while (e is AppExpr a)
        {
            revArgs.Add(a.Arg);
            e = a.Fn;
        }
        return e;
    }

    /// <summary>Whether <paramref name="e"/> is <c>(fun x => b) a …</c>.</summary>
    public static bool IsHeadBeta(Expr e) => e is AppExpr && e.GetAppFn() is LamExpr;

    /// <summary>Beta-reduces the head of <paramref name="e"/> until it is no longer a redex.</summary>
    public static Expr HeadBetaReduce(Expr e)
    {
        while (IsHeadBeta(e))
        {
            var revArgs = new List<Expr>();
            var f = GetAppRevArgs(e, revArgs);
            e = ApplyBeta(f, revArgs);
        }
        return e;
    }

    /// <summary>Applies <paramref name="f"/> to arguments (given in reverse) and beta-reduces leading lambdas.</summary>
    public static Expr ApplyBeta(Expr f, List<Expr> revArgs)
    {
        if (revArgs.Count == 0)
        {
            return f;
        }
        var span = System.Runtime.InteropServices.CollectionsMarshal.AsSpan(revArgs);
        int i = 0;
        while (f is LamExpr lam)
        {
            if (i + 1 < span.Length)
            {
                f = lam.Body;
                i++;
            }
            else
            {
                return Instantiate(lam.Body, span);
            }
        }
        int n = span.Length - i;
        return MkRevApp(Instantiate(f, span[n..]), span[..n]);
    }

    /// <summary>
    /// Beta-reduces <c>(fun xs => b) as</c> only when the result needs no substitution (Lean's
    /// <c>cheap_beta_reduce</c>), to avoid growing inferred types.
    /// </summary>
    public static Expr CheapBetaReduce(Expr e)
    {
        if (e is not AppExpr)
        {
            return e;
        }
        var fn = e.GetAppFn();
        if (fn is not LamExpr)
        {
            return e;
        }
        var args = e.GetAppArgs();
        int i = 0;
        while (fn is LamExpr lam && i < args.Length)
        {
            i++;
            fn = lam.Body;
        }
        if (!fn.HasLooseBVars)
        {
            return MkApp(fn, args.AsSpan(i));
        }
        if (fn is BVarExpr b)
        {
            return MkApp(args[i - b.Index - 1], args.AsSpan(i));
        }
        return e;
    }

    /// <summary>
    /// Strips the type annotation gadgets <c>optParam</c>, <c>autoParam</c>, <c>outParam</c> and
    /// <c>semiOutParam</c> at the head of <paramref name="e"/> (Lean's <c>consumeTypeAnnotations</c>).
    /// </summary>
    public static Expr ConsumeTypeAnnotations(Expr e)
    {
        while (true)
        {
            if (IsAppOfArity(e, KernelNames.OptParam, 2) || IsAppOfArity(e, KernelNames.AutoParam, 2))
            {
                e = ((AppExpr)((AppExpr)e).Fn).Arg;
            }
            else if (IsAppOfArity(e, KernelNames.OutParam, 1) || IsAppOfArity(e, KernelNames.SemiOutParam, 1))
            {
                e = ((AppExpr)e).Arg;
            }
            else
            {
                return e;
            }
        }
    }

    /// <summary>Whether <paramref name="e"/> is the constant <paramref name="name"/> applied to exactly <paramref name="arity"/> arguments.</summary>
    public static bool IsAppOfArity(Expr e, Name name, int arity) =>
        e.GetAppFn() is ConstExpr c && c.Name == name && e.GetAppNumArgs() == arity;

    /// <summary>
    /// Marks as implicit the first <paramref name="numParams"/> Pi binders whose variable occurs in
    /// later explicit binder domains (Lean's <c>infer_implicit</c>; used for recursor types).
    /// </summary>
    public static Expr InferImplicit(Expr t, int numParams, bool strict)
    {
        if (numParams == 0 || t is not ForallExpr pi)
        {
            return t;
        }
        var body = InferImplicit(pi.Body, numParams - 1, strict);
        var info = pi.BinderInfo == BinderInfo.Default && HasLooseBVarsInDomain(body, 0, strict)
            ? BinderInfo.Implicit
            : pi.BinderInfo;
        return ReferenceEquals(body, pi.Body) && info == pi.BinderInfo ? pi : Expr.Forall(pi.BinderName, pi.BinderType, body, info);
    }

    private static bool HasLooseBVarsInDomain(Expr b, int vidx, bool strict)
    {
        if (b is ForallExpr pi)
        {
            if (HasLooseBVar(pi.BinderType, vidx))
            {
                if (pi.BinderInfo == BinderInfo.Default)
                {
                    return true;
                }
                if (HasLooseBVarsInDomain(pi.Body, 0, strict))
                {
                    return true;
                }
            }
            return HasLooseBVarsInDomain(pi.Body, vidx + 1, strict);
        }
        return !strict && HasLooseBVar(b, vidx);
    }

    // ------------------------------------------------------------------ updates preserving sharing

    internal static Expr UpdateApp(AppExpr e, Expr fn, Expr arg) =>
        ReferenceEquals(fn, e.Fn) && ReferenceEquals(arg, e.Arg) ? e : Expr.App(fn, arg);

    internal static Expr UpdateBinding(BindingExpr e, Expr type, Expr body)
    {
        if (ReferenceEquals(type, e.BinderType) && ReferenceEquals(body, e.Body))
        {
            return e;
        }
        return e.Kind == ExprKind.Lam
            ? Expr.Lam(e.BinderName, type, body, e.BinderInfo)
            : Expr.Forall(e.BinderName, type, body, e.BinderInfo);
    }

    internal static Expr UpdateLet(LetExpr e, Expr type, Expr value, Expr body) =>
        ReferenceEquals(type, e.BinderType) && ReferenceEquals(value, e.Value) && ReferenceEquals(body, e.Body)
            ? e
            : Expr.Let(e.BinderName, type, value, body, e.NonDependent);

    internal static Expr UpdateMData(MDataExpr e, Expr inner) =>
        ReferenceEquals(inner, e.Expr) ? e : Expr.MData(e.Data, inner);

    internal static Expr UpdateProj(ProjExpr e, Expr inner) =>
        ReferenceEquals(inner, e.Struct) ? e : Expr.Proj(e.TypeName, e.Index, inner);

    internal static Expr UpdateConst(ConstExpr e, EquatableArray<Level> levels) =>
        e.Levels.Equals(levels) ? e : Expr.Const(e.Name, levels);

    internal static Expr UpdateSort(SortExpr e, Level level) =>
        ReferenceEquals(level, e.Level) ? e : Expr.Sort(level);

    private sealed class RefOffsetComparer : IEqualityComparer<(Expr, int)>
    {
        public static readonly RefOffsetComparer Instance = new();

        public bool Equals((Expr, int) x, (Expr, int) y) => ReferenceEquals(x.Item1, y.Item1) && x.Item2 == y.Item2;

        public int GetHashCode((Expr, int) obj) => HashCode.Combine(RuntimeHelpers.GetHashCode(obj.Item1), obj.Item2);
    }
}
