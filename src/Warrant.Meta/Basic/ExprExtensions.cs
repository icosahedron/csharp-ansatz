using Warrant.Cic;
using Warrant.Kernel;

namespace Warrant.Meta;

/// <summary>
/// The <c>Lean.Expr</c> helpers Meta needs beyond the kernel's <see cref="ExprOps"/>: abstraction
/// over free <em>and</em> meta variables, range instantiation, <c>betaRev</c> and <c>headBeta</c>
/// with Lean's exact behaviour, and the sharing-preserving <c>update*</c> functions.
/// </summary>
public static class ExprExtensions
{
    /// <summary>
    /// Replaces the free or meta variables <paramref name="xs"/> by bound variables, <c>xs[n-1]</c>
    /// becoming <c>#0</c> (Lean's <c>Expr.abstract</c>). It does not instantiate assigned
    /// metavariables.
    /// </summary>
    public static Expr Abstract(this Expr e, IReadOnlyList<Expr> xs) => e.AbstractRange(xs.Count, xs);

    /// <summary>Like <see cref="Abstract"/>, over the first <c>min n xs.Count</c> entries only (Lean's <c>Expr.abstractRange</c>).</summary>
    public static Expr AbstractRange(this Expr e, int n, IReadOnlyList<Expr> xs)
    {
        ArgumentNullException.ThrowIfNull(e);
        ArgumentNullException.ThrowIfNull(xs);
        n = Math.Min(n, xs.Count);
        if (n == 0 || (!e.HasFVar && !e.HasExprMVar))
        {
            return e;
        }
        return ExprOps.Replace(e, (m, offset) =>
        {
            if (!m.HasFVar && !m.HasExprMVar)
            {
                return m;
            }
            if (m.Kind is ExprKind.FVar or ExprKind.MVar)
            {
                for (int i = n - 1; i >= 0; i--)
                {
                    if (m.Equals(xs[i]))
                    {
                        return Expr.BVar(offset + n - i - 1);
                    }
                }
                return m;
            }
            return null;
        });
    }

    /// <summary>
    /// Instantiates the loose bound variables with <c>xs[beginIdx..endIdx)</c>, the last element
    /// replacing <c>#0</c> (Lean's <c>Expr.instantiateRevRange</c>).
    /// </summary>
    public static Expr InstantiateRevRange(this Expr e, int beginIdx, int endIdx, IReadOnlyList<Expr> xs)
    {
        ArgumentNullException.ThrowIfNull(xs);
        if (beginIdx >= endIdx || !e.HasLooseBVars)
        {
            return e;
        }
        var subst = new Expr[endIdx - beginIdx];
        for (int i = 0; i < subst.Length; i++)
        {
            subst[i] = xs[beginIdx + i];
        }
        return ExprOps.InstantiateRev(e, subst);
    }

    /// <summary>Instantiates the loose bound variables with <paramref name="xs"/>, the last element replacing <c>#0</c>.</summary>
    public static Expr InstantiateRev(this Expr e, IReadOnlyList<Expr> xs) => e.InstantiateRevRange(0, xs.Count, xs);

    /// <summary><c>f args[i] … args[j-1]</c> (Lean's <c>mkAppRange</c>).</summary>
    public static Expr MkAppRange(Expr f, int i, int j, IReadOnlyList<Expr> args)
    {
        ArgumentNullException.ThrowIfNull(args);
        for (; i < j; i++)
        {
            f = Expr.App(f, args[i]);
        }
        return f;
    }

    /// <summary><c>f args[0] … args[n-1]</c> (Lean's <c>mkAppN</c>).</summary>
    public static Expr MkAppN(Expr f, IReadOnlyList<Expr> args) => MkAppRange(f, 0, args.Count, args);

    /// <summary><c>f revArgs[j-1] … revArgs[i]</c> (Lean's <c>mkAppRevRange</c>).</summary>
    public static Expr MkAppRevRange(Expr f, int i, int j, IReadOnlyList<Expr> revArgs)
    {
        ArgumentNullException.ThrowIfNull(revArgs);
        while (j > i)
        {
            j--;
            f = Expr.App(f, revArgs[j]);
        }
        return f;
    }

    /// <summary>The arguments of an application spine in reverse order (Lean's <c>getAppRevArgs</c>).</summary>
    public static Expr[] GetAppRevArgs(this Expr e)
    {
        var args = e.GetAppArgs();
        Array.Reverse(args);
        return args;
    }

    /// <summary>
    /// Applies <paramref name="f"/> to the arguments <paramref name="revArgs"/> (in reverse order),
    /// beta-reducing the lambdas at its head; metadata on the way is dropped and, with
    /// <paramref name="useZeta"/>, lets are expanded (Lean's <c>Expr.betaRev</c>).
    /// </summary>
    public static Expr BetaRev(this Expr f, IReadOnlyList<Expr> revArgs, bool useZeta = false)
    {
        ArgumentNullException.ThrowIfNull(revArgs);
        int sz = revArgs.Count;
        if (sz == 0)
        {
            return f;
        }
        var arr = revArgs as Expr[] ?? [.. revArgs];
        var e = f;
        int i = 0;
        while (true)
        {
            switch (e)
            {
                case LamExpr lam:
                    if (i + 1 < sz)
                    {
                        e = lam.Body;
                        i++;
                        continue;
                    }
                    return ExprOps.Instantiate(lam.Body, arr);
                case LetExpr let when useZeta && i < sz:
                    e = ExprOps.Instantiate(let.Body, let.Value);
                    continue;
                case MDataExpr m:
                    e = m.Expr;
                    continue;
            }
            int n = sz - i;
            return MkAppRevRange(ExprOps.Instantiate(e, arr.AsSpan(n, sz - n)), 0, n, arr);
        }
    }

    /// <summary>Applies <paramref name="f"/> to <paramref name="args"/> with <see cref="BetaRev"/> (Lean's <c>Expr.beta</c>).</summary>
    public static Expr Beta(this Expr f, IReadOnlyList<Expr> args)
    {
        ArgumentNullException.ThrowIfNull(args);
        var rev = args.ToArray();
        Array.Reverse(rev);
        return f.BetaRev(rev);
    }

    /// <summary>Whether <paramref name="e"/> is a lambda, possibly under metadata (or lets, with <paramref name="useZeta"/>).</summary>
    public static bool IsHeadBetaTargetFn(this Expr e, bool useZeta) => e switch
    {
        LamExpr => true,
        LetExpr l => useZeta && l.Body.IsHeadBetaTargetFn(useZeta),
        MDataExpr m => m.Expr.IsHeadBetaTargetFn(useZeta),
        _ => false,
    };

    /// <summary>Whether <paramref name="e"/> is an application whose head is a lambda (Lean's <c>isHeadBetaTarget</c>).</summary>
    public static bool IsHeadBetaTarget(this Expr e, bool useZeta = false) =>
        e is AppExpr && e.GetAppFn().IsHeadBetaTargetFn(useZeta);

    /// <summary><c>(fun x => e) a</c> to <c>e[x := a]</c>, once at the head (Lean's <c>Expr.headBeta</c>).</summary>
    public static Expr HeadBeta(this Expr e)
    {
        var f = e.GetAppFn();
        return f.IsHeadBetaTargetFn(false) ? f.BetaRev(e.GetAppRevArgs()) : e;
    }

    // ------------------------------------------------------------------ updates preserving sharing

    /// <summary>Rebuilds an application only if a child changed (Lean's <c>updateApp!</c>).</summary>
    public static Expr UpdateApp(this AppExpr e, Expr fn, Expr arg) =>
        ReferenceEquals(fn, e.Fn) && ReferenceEquals(arg, e.Arg) ? e : Expr.App(fn, arg);

    /// <summary>Rebuilds a lambda or Pi only if a child changed (Lean's <c>updateLambdaE!</c>/<c>updateForallE!</c>).</summary>
    public static Expr UpdateBinding(this BindingExpr e, Expr type, Expr body)
    {
        if (ReferenceEquals(type, e.BinderType) && ReferenceEquals(body, e.Body))
        {
            return e;
        }
        return e.Kind == ExprKind.Lam
            ? Expr.Lam(e.BinderName, type, body, e.BinderInfo)
            : Expr.Forall(e.BinderName, type, body, e.BinderInfo);
    }

    /// <summary>Rebuilds a let only if a child changed (Lean's <c>updateLetE!</c>).</summary>
    public static Expr UpdateLet(this LetExpr e, Expr type, Expr value, Expr body) =>
        ReferenceEquals(type, e.BinderType) && ReferenceEquals(value, e.Value) && ReferenceEquals(body, e.Body)
            ? e
            : Expr.Let(e.BinderName, type, value, body, e.NonDependent);

    /// <summary>Rebuilds a metadata node only if its child changed (Lean's <c>updateMData!</c>).</summary>
    public static Expr UpdateMData(this MDataExpr e, Expr inner) =>
        ReferenceEquals(inner, e.Expr) ? e : Expr.MData(e.Data, inner);

    /// <summary>Rebuilds a projection only if its child changed (Lean's <c>updateProj!</c>).</summary>
    public static Expr UpdateProj(this ProjExpr e, Expr inner) =>
        ReferenceEquals(inner, e.Struct) ? e : Expr.Proj(e.TypeName, e.Index, inner);

    /// <summary>Rebuilds a constant only if a level changed (Lean's <c>updateConst!</c>).</summary>
    public static Expr UpdateConst(this ConstExpr e, EquatableArray<Level> levels) =>
        e.Levels.Equals(levels) ? e : Expr.Const(e.Name, levels);

    /// <summary>Rebuilds a sort only if its level changed (Lean's <c>updateSort!</c>).</summary>
    public static Expr UpdateSort(this SortExpr e, Level level) =>
        ReferenceEquals(level, e.Level) ? e : Expr.Sort(level);
}
