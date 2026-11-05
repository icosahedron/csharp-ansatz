using System.Collections.Immutable;
using System.Runtime.CompilerServices;
using Warrant.Cic;
using Warrant.Kernel;

namespace Warrant.Meta;

/// <summary>
/// Binder construction that is correct in the presence of metavariables: <c>elimMVarDeps</c>,
/// <c>revert</c>, <c>mkBinding</c> and <c>collectForwardDeps</c> (a port of Lean 4's
/// <c>MetavarContext.MkBinding</c>, Lean/MetavarContext.lean 963-1374; docs/m5a/02).
/// </summary>
/// <remarks>
/// <para>
/// Abstracting a free variable <c>x</c> out of a term that contains <c>?m</c>, where <c>x</c> is in
/// <c>?m</c>'s local context, would leave <c>x</c> free if <c>?m</c> were later assigned a term
/// using it. So <c>?m</c> is first replaced by <c>?n x</c>, for a fresh <c>?n : ∀ x, A</c> whose
/// context lacks <c>x</c>:
/// </para>
/// <list type="bullet">
/// <item>natural and synthetic <c>?m</c> are assigned <c>?m := ?n x</c>;</item>
/// <item>a synthetic-opaque <c>?m</c> (a goal) cannot be assigned here, so <c>?n</c> gets the
/// delayed assignment <c>?n #[x] := ?m</c>, which instantiation substitutes once <c>?m</c> is
/// solved.</item>
/// </list>
/// One instance serves one operation; its cache is by node identity and is reset whenever the
/// variables being eliminated change.
/// </remarks>
internal sealed class MkBinding : IMonadMCtx
{
    private readonly NameGenerator _ngen;
    private readonly bool _preserveOrder;
    private readonly BinderInfo _binderInfoForMVars;
    private readonly ImmutableHashSet<MVarId> _mvarIdsToAbstract;
    private Dictionary<Expr, Expr> _cache = new(ReferenceEqualityComparer.Instance);

    public MkBinding(
        MetavarContext mctx,
        NameGenerator ngen,
        int nextMacroScope,
        MetaBudget? budget,
        bool preserveOrder,
        BinderInfo binderInfoForMVars = BinderInfo.Implicit,
        ImmutableHashSet<MVarId>? mvarIdsToAbstract = null)
    {
        MCtx = mctx;
        _ngen = ngen;
        NextMacroScope = nextMacroScope;
        Budget = budget;
        _preserveOrder = preserveOrder;
        _binderInfoForMVars = binderInfoForMVars;
        _mvarIdsToAbstract = mvarIdsToAbstract ?? [];
    }

    public MetavarContext MCtx { get; set; }

    public MetaBudget? Budget { get; }

    /// <summary>The next macro scope for fresh binder names; the caller reads it back.</summary>
    public int NextMacroScope { get; private set; }

    private Name MkFreshBinderName() => Name.From("x", "_@", "_hyg").Append((ulong)NextMacroScope++);

    /// <summary>
    /// <paramref name="toRevert"/> together with every variable of <paramref name="lctx"/> that may
    /// depend on them, sorted by index (Lean's <c>collectForwardDeps</c>). With
    /// <c>preserveOrder</c>, the given order is kept and must respect dependencies.
    /// </summary>
    public Expr[] CollectForwardDeps(LocalContext lctx, IReadOnlyList<Expr> toRevert, bool generalizeNondepLet = true)
    {
        if (toRevert.Count == 0)
        {
            return [];
        }
        if (_preserveOrder)
        {
            // toRevert[j] must not depend on toRevert[i] for j < i.
            for (int i = 0; i < toRevert.Count; i++)
            {
                var fvarId = LocalContext.FVarIdOf(toRevert[i]);
                for (int j = 0; j < i; j++)
                {
                    var prevDecl = lctx.GetFVar(toRevert[j]);
                    if (this.LocalDeclDependsOn(prevDecl, fvarId, generalizeNondepLet))
                    {
                        throw RevertFailure();
                    }
                }
            }
        }
        var newToRevert = _preserveOrder ? new List<Expr>(toRevert) : new List<Expr>(toRevert.Count);
        var firstDeclToVisit = GetLocalDeclWithSmallestIdx(lctx, toRevert);
        int initSize = newToRevert.Count;
        foreach (var decl in lctx.DeclsFrom(firstDeclToVisit.Index))
        {
            bool already = false;
            for (int i = 0; i < initSize; i++)
            {
                if (decl.FVarId == LocalContext.FVarIdOf(newToRevert[i]))
                {
                    already = true;
                    break;
                }
            }
            if (already)
            {
                continue;
            }
            if (toRevert.Any(x => decl.FVarId == LocalContext.FVarIdOf(x)))
            {
                newToRevert.Add(decl.ToExpr());
            }
            else if (this.FindLocalDeclDependsOn(decl, id => newToRevert.Any(x => LocalContext.FVarIdOf(x) == id), generalizeNondepLet: generalizeNondepLet))
            {
                newToRevert.Add(decl.ToExpr());
            }
        }
        return [.. newToRevert];
    }

    /// <summary>The failure Lean's <c>liftMkBindingM</c> reports for <c>Exception.revertFailure</c>.</summary>
    private static MetaException RevertFailure() =>
        new("failed to create binder due to failure when reverting variable dependencies");

    private static LocalDecl GetLocalDeclWithSmallestIdx(LocalContext lctx, IReadOnlyList<Expr> xs)
    {
        var d = lctx.GetFVar(xs[0]);
        for (int i = 1; i < xs.Count; i++)
        {
            if (xs[i] is FVarExpr)
            {
                var curr = lctx.GetFVar(xs[i]);
                if (curr.Index < d.Index)
                {
                    d = curr;
                }
            }
        }
        return d;
    }

    /// <summary><paramref name="lctx"/> without the free variables of <paramref name="toRevert"/> (Lean's <c>reduceLocalContext</c>).</summary>
    public static LocalContext ReduceLocalContext(LocalContext lctx, IReadOnlyList<Expr> toRevert)
    {
        for (int i = toRevert.Count - 1; i >= 0; i--)
        {
            if (toRevert[i] is FVarExpr f)
            {
                lctx = lctx.Erase(f.Id);
            }
        }
        return lctx;
    }

    private static Expr[] GetInScope(LocalContext lctx, IReadOnlyList<Expr> xs) =>
        [.. xs.Where(x => x is FVarExpr f && lctx.Contains(f.Id))];

    private T WithFreshCache<T>(Func<T> x)
    {
        var saved = _cache;
        _cache = new(ReferenceEqualityComparer.Instance);
        try
        {
            return x();
        }
        finally
        {
            _cache = saved;
        }
    }

    /// <summary>
    /// <c>mvar ys</c> for the free variables <c>ys</c> of <paramref name="xs"/>; local definitions are
    /// skipped unless the metavariable is synthetic opaque (Lean's <c>mkMVarApp</c>).
    /// </summary>
    private static Expr MkMVarApp(LocalContext lctx, Expr mvar, IReadOnlyList<Expr> xs, MetavarKind kind)
    {
        var e = mvar;
        foreach (var x in xs)
        {
            if (x is not FVarExpr)
            {
                continue;
            }
            if (kind == MetavarKind.SyntheticOpaque || !lctx.GetFVar(x).IsLet())
            {
                e = Expr.App(e, x);
            }
        }
        return e;
    }

    private Expr Visit(IReadOnlyList<Expr> xs, Expr e)
    {
        if (!e.HasExprMVar && !e.HasLevelMVar)
        {
            return e;
        }
        if (_cache.TryGetValue(e, out var cached))
        {
            return cached;
        }
        var r = Elim(xs, e);
        _cache[e] = r;
        return r;
    }

    private Expr[] VisitAll(IReadOnlyList<Expr> xs, IReadOnlyList<Expr> args)
    {
        var r = new Expr[args.Count];
        for (int i = 0; i < r.Length; i++)
        {
            r[i] = Visit(xs, args[i]);
        }
        return r;
    }

    private Expr Elim(IReadOnlyList<Expr> xs, Expr e)
    {
        Budget?.Tick();
        RuntimeHelpers.EnsureSufficientExecutionStack();
        return e switch
        {
            ProjExpr p => p.UpdateProj(Visit(xs, p.Struct)),
            BindingExpr b => b.UpdateBinding(Visit(xs, b.BinderType), Visit(xs, b.Body)),
            LetExpr l => l.UpdateLet(Visit(xs, l.BinderType), Visit(xs, l.Value), Visit(xs, l.Body)),
            MDataExpr m => m.UpdateMData(Visit(xs, m.Expr)),
            AppExpr => ElimApp(xs, e.GetAppFn(), e.GetAppArgs()),
            MVarExpr => ElimApp(xs, e, []),
            _ => e,
        };
    }

    /// <summary>
    /// The type of the auxiliary metavariable that replaces one of type <paramref name="e"/> whose
    /// context contains <paramref name="xs"/>: <c>∀ xs, e</c>, with lets for used local definitions
    /// (Lean's <c>mkAuxMVarType</c>; see "Gruesome details" in Lean/MetavarContext.lean).
    /// </summary>
    private Expr MkAuxMVarType(LocalContext lctx, IReadOnlyList<Expr> xs, MetavarKind kind, Expr e, bool usedLetOnly)
    {
        e = AbstractRangeAux(xs, xs.Count, e);
        for (int i = xs.Count - 1; i >= 0; i--)
        {
            var x = xs[i];
            if (x is FVarExpr)
            {
                switch (lctx.GetFVar(x))
                {
                    case CDecl c:
                        e = Expr.Forall(c.UserName, AbstractRangeAux(xs, i, c.Type.HeadBeta()), e, c.Info);
                        break;
                    case LDecl { Nondep: true } l:
                        e = Expr.Forall(l.UserName, AbstractRangeAux(xs, i, l.Type.HeadBeta()), e);
                        break;
                    case LDecl l:
                        if (!usedLetOnly || ExprOps.HasLooseBVar(e, 0))
                        {
                            var type = AbstractRangeAux(xs, i, l.Type.HeadBeta());
                            var value = AbstractRangeAux(xs, i, l.Value);
                            e = Expr.Let(l.UserName, type, value, e);
                            if (kind == MetavarKind.SyntheticOpaque)
                            {
                                // A delayed assignment's ?n takes the let variable as an argument.
                                e = Expr.Forall(l.UserName, type, ExprOps.LiftLooseBVars(e, 0, 1));
                            }
                        }
                        else if (kind == MetavarKind.SyntheticOpaque)
                        {
                            e = Expr.Forall(l.UserName, AbstractRangeAux(xs, i, l.Type.HeadBeta()), e);
                        }
                        else
                        {
                            e = ExprOps.LowerLooseBVars(e, 1, 1);
                        }
                        break;
                }
            }
            else
            {
                // `xs` may contain metavariables as "may dependencies".
                var mvarDecl = MCtx.GetDecl(((MVarExpr)x).Id);
                var type = AbstractRangeAux(xs, i, mvarDecl.Type.HeadBeta());
                var id = mvarDecl.UserName.IsAnonymous ? MkFreshBinderName() : mvarDecl.UserName;
                e = Expr.Forall(id, type, e, _binderInfoForMVars);
            }
        }
        return e;
    }

    private Expr AbstractRangeAux(IReadOnlyList<Expr> xs, int i, Expr e) => Elim(xs, e).AbstractRange(i, xs);

    /// <summary>
    /// Eliminates <paramref name="xs"/> from <paramref name="mvarId"/>'s context: returns
    /// <c>?n ys args</c> for a fresh <c>?n</c> whose type abstracts <c>ys</c>, the forward
    /// dependencies of the <paramref name="xs"/> in that context, and assigns or delayed-assigns
    /// <paramref name="mvarId"/> (Lean's <c>elimMVar</c>).
    /// </summary>
    private (Expr Result, Expr[] ToRevert) ElimMVar(IReadOnlyList<Expr> xs, MVarId mvarId, IReadOnlyList<Expr> args, bool usedLetOnly)
    {
        var mvarDecl = MCtx.GetDecl(mvarId);
        var mvarLCtx = mvarDecl.LCtx;
        var toRevert = GetInScope(mvarLCtx, xs);
        if (toRevert.Length == 0)
        {
            return (ExprExtensions.MkAppN(Expr.MVar(mvarId), VisitAll(xs, args)), []);
        }
        // A read-only metavariable cannot be assigned, so the auxiliary one is synthetic opaque and
        // the link is a delayed assignment.
        var newMVarKind = !MCtx.IsAssignable(mvarId) ? MetavarKind.SyntheticOpaque : mvarDecl.Kind;
        var newArgs = VisitAll(xs, args);
        toRevert = CollectForwardDeps(mvarLCtx, toRevert);
        var newMVarLCtx = ReduceLocalContext(mvarLCtx, toRevert);
        var newLocalInsts = mvarDecl.LocalInstances.RemoveAll(inst => toRevert.Any(x => inst.FVar.Equals(x)));
        // The cache must be reset: toRevert may differ from xs.
        var reverted = toRevert;
        var newMVarType = WithFreshCache(() => MkAuxMVarType(mvarLCtx, reverted, newMVarKind, mvarDecl.Type, usedLetOnly));
        var newMVarId = new MVarId(_ngen.Next());
        var newMVar = Expr.MVar(newMVarId);
        var result = MkMVarApp(mvarLCtx, newMVar, toRevert, newMVarKind);
        int numScopeArgs = mvarDecl.NumScopeArgs + result.GetAppNumArgs();
        MCtx = MCtx.AddExprMVarDecl(newMVarId, Name.Anonymous, newMVarLCtx, newLocalInsts, newMVarType, newMVarKind, numScopeArgs);
        if (mvarDecl.Kind != MetavarKind.SyntheticOpaque)
        {
            MCtx = MCtx.Assign(mvarId, result);
        }
        else
        {
            // If ?m is itself `?m #[x₁ … xₙ] := ?pending`, then ?n #[ys, x₁ … xₙ] := ?pending.
            var (mvarIdPending, nestedFVars) = MCtx.GetDelayedMVarAssignment(mvarId) is { } d
                ? (d.MVarIdPending, d.FVars)
                : (mvarId, ImmutableArray<Expr>.Empty);
            MCtx = MCtx.AssignDelayedMVar(newMVarId, [.. toRevert, .. nestedFVars], mvarIdPending);
        }
        return (ExprExtensions.MkAppN(result, newArgs), toRevert);
    }

    private Expr ElimApp(IReadOnlyList<Expr> xs, Expr f, IReadOnlyList<Expr> args)
    {
        if (f is MVarExpr mv)
        {
            if (MCtx.GetExprAssignment(mv.Id) is { } newF)
            {
                if (newF is LamExpr)
                {
                    // Arguments may become irrelevant after beta reduction.
                    var visited = VisitAll(xs, args);
                    Array.Reverse(visited);
                    return Elim(xs, newF.BetaRev(visited));
                }
                return ElimApp(xs, newF, args);
            }
            if (_mvarIdsToAbstract.Contains(mv.Id))
            {
                return ExprExtensions.MkAppN(f, VisitAll(xs, args));
            }
            // usedLetOnly avoids needless let binders in the new metavariable's type.
            return ElimMVar(xs, mv.Id, args, usedLetOnly: true).Result;
        }
        return ExprExtensions.MkAppN(Visit(xs, f), VisitAll(xs, args));
    }

    /// <summary>
    /// <paramref name="e"/> with every unassigned metavariable whose context contains one of
    /// <paramref name="xs"/> replaced as described above (Lean's <c>elimMVarDeps</c>).
    /// </summary>
    public Expr ElimMVarDeps(IReadOnlyList<Expr> xs, Expr e)
    {
        if (!e.HasExprMVar && !e.HasLevelMVar)
        {
            return e;
        }
        return WithFreshCache(() => Elim(xs, e));
    }

    /// <summary>
    /// Reverts <paramref name="xs"/> (and their forward dependencies) from <paramref name="mvarId"/>'s
    /// context: returns the new metavariable applied to the reverted variables, and those variables
    /// (Lean's <c>revert</c>). Reverting a let variable always yields a let binder.
    /// </summary>
    public (Expr Result, Expr[] Reverted) Revert(IReadOnlyList<Expr> xs, MVarId mvarId) =>
        WithFreshCache(() => ElimMVar(xs, mvarId, [], usedLetOnly: false));

    /// <summary>
    /// Like <see cref="ExprExtensions.AbstractRange"/>, after eliminating metavariable dependencies
    /// on <paramref name="xs"/> (Lean's <c>MkBinding.abstractRange</c>).
    /// </summary>
    public Expr AbstractRange(IReadOnlyList<Expr> xs, int i, Expr e) => ElimMVarDeps(xs, e).AbstractRange(i, xs);

    private static Expr MkLambdaEta(Name x, BinderInfo bi, Expr t, Expr b, bool etaReduce)
    {
        if (etaReduce && b is AppExpr { Arg: BVarExpr { Index: 0 } } app && !ExprOps.HasLooseBVar(app.Fn, 0))
        {
            return ExprOps.LowerLooseBVars(app.Fn, 1, 1);
        }
        return Expr.Lam(x, t, b, bi);
    }

    /// <summary>
    /// <c>fun xs => e</c> or <c>∀ xs, e</c> for free or meta variables <paramref name="xs"/>, in
    /// order and closed under forward dependencies (Lean's <c>MkBinding.mkBinding</c>).
    /// </summary>
    /// <param name="isLambda">Lambdas rather than Pis.</param>
    /// <param name="lctx">The local context declaring the free variables of <paramref name="xs"/>.</param>
    /// <param name="xs">The variables to bind.</param>
    /// <param name="e">The body.</param>
    /// <param name="usedOnly">Bind only the hypotheses the body uses.</param>
    /// <param name="usedLetOnly">Bind only the local definitions the body uses.</param>
    /// <param name="etaReduce">Eta-reduce <c>fun x => f x</c> to <c>f</c>.</param>
    /// <param name="generalizeNondepLet">Bind nondependent local definitions as hypotheses.</param>
    public Expr MkBindingCore(bool isLambda, LocalContext lctx, IReadOnlyList<Expr> xs, Expr e, bool usedOnly, bool usedLetOnly, bool etaReduce, bool generalizeNondepLet)
    {
        e = AbstractRange(xs, xs.Count, e);
        for (int i = xs.Count - 1; i >= 0; i--)
        {
            var x = xs[i];
            if (x is FVarExpr)
            {
                switch (lctx.GetFVar(x))
                {
                    case CDecl c:
                        e = HandleCDecl(i, c.UserName, c.Type, c.Info, e);
                        break;
                    case LDecl l when generalizeNondepLet && l.Nondep:
                        e = HandleCDecl(i, l.UserName, l.Type, BinderInfo.Default, e);
                        break;
                    case LDecl l:
                        e = !usedLetOnly || ExprOps.HasLooseBVar(e, 0)
                            ? Expr.Let(l.UserName, AbstractRange(xs, i, l.Type), AbstractRange(xs, i, l.Value), e, l.Nondep)
                            : ExprOps.LowerLooseBVars(e, 1, 1);
                        break;
                }
            }
            else
            {
                var mvarDecl = MCtx.GetDecl(((MVarExpr)x).Id);
                var type = AbstractRange(xs, i, mvarDecl.Type.HeadBeta());
                var id = mvarDecl.UserName.IsAnonymous ? MkFreshBinderName() : mvarDecl.UserName;
                e = isLambda
                    ? MkLambdaEta(id, _binderInfoForMVars, type, e, etaReduce)
                    : Expr.Forall(id, type, e, _binderInfoForMVars);
            }
        }
        return e;

        Expr HandleCDecl(int i, Name n, Expr type, BinderInfo bi, Expr body)
        {
            if (usedOnly && !ExprOps.HasLooseBVar(body, 0))
            {
                return ExprOps.LowerLooseBVars(body, 1, 1);
            }
            var t = AbstractRange(xs, i, type.HeadBeta());
            return isLambda ? MkLambdaEta(n, bi, t, body, etaReduce) : Expr.Forall(n, t, body, bi);
        }
    }
}
