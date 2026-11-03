using Warrant.Cic;
using Warrant.Kernel;

namespace Warrant.Meta;

// The telescopes that reduce (Lean/Meta/Basic.lean 1487-1641, 1751-1797, 2176-2200). Like the
// non-reducing ones in MetaM.cs, they do not register local instances yet.
public sealed partial class MetaM
{
    private T ForallTelescopeReducingAuxAux<T>(bool reducing, int? maxFVars, Expr type, Func<Expr[], Expr, T> k, bool cleanupAnnotations, bool whnfTypeIfReducing)
    {
        var lctx = LCtx;
        var fvars = new List<Expr>();
        int j = 0;
        while (true)
        {
            if (type is ForallExpr f && (maxFVars is not { } max || fvars.Count < max))
            {
                Budget.Tick();
                var d = f.BinderType.InstantiateRevRange(j, fvars.Count, fvars);
                if (cleanupAnnotations)
                {
                    d = CleanupAnnotations(d);
                }
                var fvarId = MkFreshFVarId();
                lctx = lctx.MkLocalDecl(fvarId, f.BinderName, d, f.BinderInfo);
                fvars.Add(Expr.FVar(fvarId));
                type = f.Body;
                continue;
            }
            var body = type.InstantiateRevRange(j, fvars.Count, fvars);
            if (type is ForallExpr)
            {
                // The telescope reached maxFVars.
                Expr[] xs0 = [.. fvars];
                return WithReader(c => c with { LCtx = lctx }, () => k(xs0, body));
            }
            var lctxNow = lctx;
            var (again, result) = WithReader(c => c with { LCtx = lctxNow }, () =>
            {
                if (reducing && (maxFVars is not { } m || fvars.Count < m))
                {
                    var newType = Whnf(body);
                    if (newType is ForallExpr)
                    {
                        return (newType, default(T));
                    }
                    return ((Expr?)null, k([.. fvars], whnfTypeIfReducing ? newType : body));
                }
                return (null, k([.. fvars], body));
            });
            if (again is null)
            {
                return result!;
            }
            type = again;
            j = fvars.Count;
        }
    }

    private static Expr CleanupAnnotations(Expr e)
    {
        while (true)
        {
            var e1 = ExprOps.ConsumeTypeAnnotations(e.ConsumeMData());
            if (ReferenceEquals(e1, e))
            {
                return e;
            }
            e = e1;
        }
    }

    private T ForallTelescopeReducingAux<T>(Expr type, int? maxFVars, Func<Expr[], Expr, T> k, bool cleanupAnnotations, bool whnfType)
    {
        if (maxFVars == 0)
        {
            return k([], whnfType ? Whnf(type) : type);
        }
        var newType = Whnf(type);
        if (newType is ForallExpr)
        {
            return ForallTelescopeReducingAuxAux(true, maxFVars, newType, k, cleanupAnnotations, whnfType);
        }
        return k([], whnfType ? newType : type);
    }

    /// <summary>
    /// Like <see cref="ForallTelescope{T}"/>, but reduces the body with <see cref="Whnf"/> to find
    /// more binders (Lean's <c>forallTelescopeReducing</c>). With <paramref name="whnfType"/>,
    /// <paramref name="k"/> receives the reduced body.
    /// </summary>
    public T ForallTelescopeReducing<T>(Expr type, Func<Expr[], Expr, T> k, bool cleanupAnnotations = false, bool whnfType = false)
    {
        ArgumentNullException.ThrowIfNull(type);
        ArgumentNullException.ThrowIfNull(k);
        return ForallTelescopeReducingAux(type, null, k, cleanupAnnotations, whnfType);
    }

    /// <summary>
    /// Like <see cref="ForallTelescopeReducing{T}"/>, stopping after <paramref name="maxFVars"/>
    /// binders (Lean's <c>forallBoundedTelescope</c>).
    /// </summary>
    public T ForallBoundedTelescope<T>(Expr type, int? maxFVars, Func<Expr[], Expr, T> k, bool cleanupAnnotations = false, bool whnfType = false)
    {
        ArgumentNullException.ThrowIfNull(type);
        ArgumentNullException.ThrowIfNull(k);
        return ForallTelescopeReducingAux(type, maxFVars, k, cleanupAnnotations, whnfType);
    }

    private (Expr[] MVars, BinderInfo[] BinderInfos, Expr Type) ForallMetaTelescopeReducingAux(Expr e, bool reducing, int? maxMVars, MetavarKind kind)
    {
        var mvars = new List<Expr>();
        var bis = new List<BinderInfo>();
        int j = 0;
        var type = e;
        while (true)
        {
            if (maxMVars == mvars.Count)
            {
                return ([.. mvars], [.. bis], type.InstantiateRevRange(j, mvars.Count, mvars));
            }
            if (type is ForallExpr f)
            {
                Budget.Tick();
                var d = f.BinderType.InstantiateRevRange(j, mvars.Count, mvars);
                var k = f.BinderInfo == BinderInfo.InstImplicit ? MetavarKind.Synthetic : kind;
                mvars.Add(MkFreshExprMVar(d, k, f.BinderName));
                bis.Add(f.BinderInfo);
                type = f.Body;
                continue;
            }
            var t = type.InstantiateRevRange(j, mvars.Count, mvars);
            if (reducing)
            {
                var newType = Whnf(t);
                if (newType is ForallExpr)
                {
                    type = newType;
                    j = mvars.Count;
                    continue;
                }
            }
            return ([.. mvars], [.. bis], t);
        }
    }

    /// <summary>
    /// Like <see cref="ForallMetaTelescope"/>, reducing the body to find more binders (Lean's
    /// <c>forallMetaTelescopeReducing</c>); at most <paramref name="maxMVars"/> binders if given.
    /// </summary>
    public (Expr[] MVars, BinderInfo[] BinderInfos, Expr Type) ForallMetaTelescopeReducing(Expr e, int? maxMVars = null, MetavarKind kind = MetavarKind.Natural)
    {
        ArgumentNullException.ThrowIfNull(e);
        return ForallMetaTelescopeReducingAux(e, reducing: true, maxMVars, kind);
    }

    /// <summary>Lean's <c>forallMetaBoundedTelescope</c>.</summary>
    public (Expr[] MVars, BinderInfo[] BinderInfos, Expr Type) ForallMetaBoundedTelescope(Expr e, int maxMVars, MetavarKind kind = MetavarKind.Natural) =>
        ForallMetaTelescopeReducing(e, maxMVars, kind);

    /// <summary>
    /// <c>B[p₁, …, pₙ]</c> for <paramref name="e"/> = <c>∀ (a₁ : A₁) … (aₙ : Aₙ), B</c>, reducing to
    /// expose binders (Lean's <c>instantiateForall</c>).
    /// </summary>
    /// <exception cref="MetaException">There are too many parameters.</exception>
    public Expr InstantiateForall(Expr e, IReadOnlyList<Expr> ps)
    {
        ArgumentNullException.ThrowIfNull(ps);
        foreach (var p in ps)
        {
            if (Whnf(e) is not ForallExpr f)
            {
                throw new MetaException("invalid instantiateForall, too many parameters");
            }
            e = ExprOps.Instantiate(f.Body, p);
        }
        return e;
    }

    /// <summary>
    /// <c>t[p₁, …, pₙ]</c> for <paramref name="e"/> = <c>fun (a₁ : A₁) … (aₙ : Aₙ) => t</c>, reducing
    /// to expose binders (Lean's <c>instantiateLambda</c>).
    /// </summary>
    /// <exception cref="MetaException">There are too many parameters.</exception>
    public Expr InstantiateLambda(Expr e, IReadOnlyList<Expr> ps)
    {
        ArgumentNullException.ThrowIfNull(ps);
        foreach (var p in ps)
        {
            if (Whnf(e) is not LamExpr l)
            {
                throw new MetaException("invalid instantiateLambda, too many parameters");
            }
            e = ExprOps.Instantiate(l.Body, p);
        }
        return e;
    }
}
