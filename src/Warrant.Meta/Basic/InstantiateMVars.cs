using System.Runtime.CompilerServices;
using Warrant.Cic;

namespace Warrant.Meta;

/// <summary>
/// <c>instantiateMVars</c>: substitutes assigned metavariables in a term. Lean 4.35.0 implements it
/// in C++ (<c>instantiate_mvars.cpp</c>, not in the toolchain); this ports the behaviour its
/// docstring documents (Lean/MetavarContext.lean, 573-650) and Lean's earlier Lean implementation.
/// </summary>
/// <remarks>
/// <list type="bullet">
/// <item>An assigned <c>?m</c> is replaced by its value, recursively, and the instantiated value is
/// written back to the context (path compression), so a later call does not repeat the work.</item>
/// <item>An application <c>?f a₁ … aₙ</c> whose head is assigned a lambda is beta-reduced, so
/// assignments made through delayed abstraction do not leave <c>(fun x => t) a</c> behind.</item>
/// <item>Regular assignments take precedence over delayed ones.</item>
/// <item>A delayed-assigned <c>?m #[x₁ … xₖ] := ?p</c> is replaced only where it is applied to at
/// least <c>k</c> arguments <em>and</em> <c>?p</c>'s instantiated value has no expression
/// metavariable: <c>?m a₁ … aₙ</c> becomes <c>v[xᵢ := aᵢ] aₖ₊₁ … aₙ</c>. Otherwise only the
/// arguments are instantiated. Substituting earlier would leave the <c>xᵢ</c> free outside their
/// binders.</item>
/// <item>Universe metavariables are instantiated too.</item>
/// </list>
/// One instance serves one call over one context. Its cache is by node identity, so each shared
/// subterm is visited once and the cost is linear in the size of the term and of the assignments it
/// reaches.
/// </remarks>
internal sealed class InstantiateMVarsFn(MetavarContext mctx, MetaBudget? budget)
{
    private readonly Dictionary<Expr, Expr> _cache = new(ReferenceEqualityComparer.Instance);
    private readonly HashSet<MVarId> _alreadyNormalized = [];

    /// <summary>The context, updated with instantiated (path-compressed) assignments.</summary>
    public MetavarContext MCtx { get; private set; } = mctx;

    public Level VisitLevel(Level l)
    {
        if (!l.HasMVar)
        {
            return l;
        }
        RuntimeHelpers.EnsureSufficientExecutionStack();
        switch (l.Kind)
        {
            case LevelKind.Succ:
            {
                var a = VisitLevel(l.Lhs!);
                return ReferenceEquals(a, l.Lhs) ? l : Level.Succ(a);
            }
            case LevelKind.Max:
            case LevelKind.IMax:
            {
                var a = VisitLevel(l.Lhs!);
                var b = VisitLevel(l.Rhs!);
                if (ReferenceEquals(a, l.Lhs) && ReferenceEquals(b, l.Rhs))
                {
                    return l;
                }
                return l.Kind == LevelKind.Max ? Level.Max(a, b) : Level.IMax(a, b);
            }
            case LevelKind.MVar:
            {
                var id = l.MVarId!.Value;
                if (MCtx.GetLevelAssignment(id) is not { } a)
                {
                    return l;
                }
                if (!a.HasMVar)
                {
                    return a;
                }
                budget?.Tick();
                var aNew = VisitLevel(a);
                if (!ReferenceEquals(a, aNew))
                {
                    MCtx = MCtx.AssignLevelMVar(id, aNew);
                }
                return aNew;
            }
            default:
                return l;
        }
    }

    public Expr Visit(Expr e)
    {
        if (!e.HasExprMVar && !e.HasLevelMVar)
        {
            return e;
        }
        if (_cache.TryGetValue(e, out var cached))
        {
            return cached;
        }
        budget?.Tick();
        RuntimeHelpers.EnsureSufficientExecutionStack();
        var r = e switch
        {
            ProjExpr p => p.UpdateProj(Visit(p.Struct)),
            BindingExpr b => b.UpdateBinding(Visit(b.BinderType), Visit(b.Body)),
            LetExpr l => l.UpdateLet(Visit(l.BinderType), Visit(l.Value), Visit(l.Body)),
            MDataExpr m => m.UpdateMData(Visit(m.Expr)),
            ConstExpr c => c.UpdateConst(VisitLevels(c.Levels)),
            SortExpr s => s.UpdateSort(VisitLevel(s.Level)),
            AppExpr => VisitApp(e),
            MVarExpr mv => GetAssignment(mv.Id) ?? e,
            _ => e,
        };
        _cache[e] = r;
        return r;
    }

    private EquatableArray<Level> VisitLevels(EquatableArray<Level> levels)
    {
        Level[]? changed = null;
        for (int i = 0; i < levels.Count; i++)
        {
            var l = VisitLevel(levels[i]);
            if (!ReferenceEquals(l, levels[i]))
            {
                changed ??= [.. levels];
                changed[i] = l;
            }
        }
        return changed is null ? levels : EquatableArray.Create<Level>(changed);
    }

    /// <summary>
    /// The instantiated assignment of <paramref name="mvarId"/>, or null if it is unassigned. The
    /// first time a value with metavariables is reached it is instantiated and written back.
    /// </summary>
    private Expr? GetAssignment(MVarId mvarId)
    {
        if (MCtx.GetExprAssignment(mvarId) is not { } a)
        {
            return null;
        }
        if ((!a.HasExprMVar && !a.HasLevelMVar) || _alreadyNormalized.Contains(mvarId))
        {
            return a;
        }
        _alreadyNormalized.Add(mvarId);
        var aNew = Visit(a);
        if (!ReferenceEquals(a, aNew))
        {
            MCtx = MCtx.Assign(mvarId, aNew);
        }
        return aNew;
    }

    private Expr VisitApp(Expr e)
    {
        var f = e.GetAppFn();
        if (f is not MVarExpr fm)
        {
            return InstArgs(e, Visit(f));
        }
        // Regular assignments take precedence over delayed ones.
        if (GetAssignment(fm.Id) is { } fNew)
        {
            // Beta-reduce an assigned head, so instantiation leaves no `(fun x => t) a`. Zeta is on
            // so that every argument is substituted, and instantiated, rather than dropped (Lean
            // issue #4375).
            return fNew is LamExpr ? Visit(fNew.BetaRev(e.GetAppRevArgs(), useZeta: true)) : InstArgs(e, fNew);
        }
        if (MCtx.GetDelayedMVarAssignment(fm.Id) is not { } d)
        {
            return InstArgs(e, f);
        }
        // A delayed substitution: `?m #[fvars] := ?pending` applied to arguments. It fires only when
        // there are enough arguments for `fvars` and `?pending`'s value is fully solved.
        var fvars = d.FVars;
        if (fvars.Length > e.GetAppNumArgs())
        {
            return InstArgs(e, f);
        }
        var newVal = GetAssignment(d.MVarIdPending);
        if (newVal is null || newVal.HasExprMVar)
        {
            return InstArgs(e, f);
        }
        var args = e.GetAppArgs();
        for (int i = 0; i < args.Length; i++)
        {
            args[i] = Visit(args[i]);
        }
        // With `?m #[x, y] := g x y` and `?m t₁ t₂ t₃`: abstracting gives `g #1 #0`, instantiating
        // with t₁ t₂ gives `g t₁ t₂`, and the remaining argument gives `g t₁ t₂ t₃`.
        var result = newVal.Abstract(fvars).InstantiateRevRange(0, fvars.Length, args);
        return ExprExtensions.MkAppRange(result, fvars.Length, args.Length, args);
    }

    /// <summary>Instantiates the arguments of <paramref name="e"/> and reapplies them to <paramref name="f"/>.</summary>
    private Expr InstArgs(Expr e, Expr f)
    {
        var args = e.GetAppArgs();
        bool changed = !ReferenceEquals(f, e.GetAppFn());
        for (int i = 0; i < args.Length; i++)
        {
            var a = Visit(args[i]);
            changed |= !ReferenceEquals(a, args[i]);
            args[i] = a;
        }
        return changed ? ExprExtensions.MkAppN(f, args) : e;
    }
}

/// <summary>Instantiation of local contexts and metavariable declarations (Lean's <c>instantiateLCtxMVars</c> and friends).</summary>
public static class InstantiateMVarsExtensions
{
    /// <summary>
    /// <paramref name="lctx"/> with every type and value instantiated (Lean's
    /// <c>instantiateLCtxMVars</c>); like Lean, it is rebuilt, so holes left by erased declarations
    /// are closed.
    /// </summary>
    public static LocalContext InstantiateLCtxMVars(this IMonadMCtx m, LocalContext lctx)
    {
        ArgumentNullException.ThrowIfNull(lctx);
        var result = LocalContext.Empty;
        foreach (var decl in lctx.Decls)
        {
            var type = m.InstantiateMVars(decl.Type);
            result = decl switch
            {
                CDecl { Kind: LocalDeclKind.AuxDecl } c => result.MkAuxDecl(c.FVarId, c.UserName, type,
                    lctx.GetAuxDeclFullName(c.FVarId) ?? throw new MetaException($"Invalid auxiliary declaration found in local context: {c.UserName} does not have an associated full name.")),
                CDecl c => result.MkLocalDecl(c.FVarId, c.UserName, type, c.Info, c.Kind),
                LDecl l => result.MkLetDecl(l.FVarId, l.UserName, type, m.InstantiateMVars(l.Value), l.Nondep, l.Kind),
                _ => throw new InvalidOperationException("unreachable"),
            };
        }
        return result;
    }

    /// <summary>Instantiates the local context and type of <paramref name="mvarId"/>'s declaration (Lean's <c>instantiateMVarDeclMVars</c>).</summary>
    public static void InstantiateMVarDeclMVars(this IMonadMCtx m, MVarId mvarId)
    {
        ArgumentNullException.ThrowIfNull(m);
        var decl = m.MCtx.GetDecl(mvarId);
        var lctx = m.InstantiateLCtxMVars(decl.LCtx);
        var type = m.InstantiateMVars(decl.Type);
        m.MCtx = m.MCtx with { Decls = m.MCtx.Decls.SetItem(mvarId, decl with { LCtx = lctx, Type = type }) };
    }

    /// <summary>Instantiates a local declaration's type and value (Lean's <c>instantiateLocalDeclMVars</c>).</summary>
    public static LocalDecl InstantiateLocalDeclMVars(this IMonadMCtx m, LocalDecl localDecl) => localDecl switch
    {
        CDecl c => c with { Type = m.InstantiateMVars(c.Type) },
        LDecl l => l with { Type = m.InstantiateMVars(l.Type), Value = m.InstantiateMVars(l.Value) },
        _ => throw new ArgumentException("unknown local declaration", nameof(localDecl)),
    };
}
