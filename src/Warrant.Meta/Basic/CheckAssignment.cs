using System.Runtime.CompilerServices;
using Warrant.Cic;

namespace Warrant.Meta;

public sealed partial class MetaM
{
    /// <summary>
    /// Assigns <c>?mvarId := val</c> if the assignment passes <see cref="CheckAssignment"/>, and
    /// reports whether it did (Lean's <c>MVarId.checkedAssign</c>). Like Lean's, it does not compare
    /// types and does not check that <paramref name="mvarId"/> is unassigned.
    /// </summary>
    public bool CheckedAssign(MVarId mvarId, Expr val)
    {
        if (CheckAssignment(mvarId, [], val) is not { } v)
        {
            return false;
        }
        Assign(mvarId, v);
        return true;
    }

    /// <summary>
    /// Checks that <c>?mvarId := fun fvars => v</c> is a sound assignment and returns the possibly
    /// rewritten <paramref name="v"/>, or null (a port of Lean's <c>checkAssignment</c>,
    /// Lean/Meta/ExprDefEq.lean 1315). It rejects:
    /// <list type="bullet">
    /// <item><c>?mvarId</c> occurring in <paramref name="v"/>, in the type of an <paramref name="fvars"/>
    /// variable, or in the type of a metavariable of <paramref name="v"/> (occurs checks);</item>
    /// <item>a free variable of <paramref name="v"/> that is neither in <c>?mvarId</c>'s local context nor
    /// among <paramref name="fvars"/>, unless it is a local definition, whose value is checked instead
    /// (the scope check that keeps a hypothesis from escaping into a proof);</item>
    /// <item>a metavariable of <paramref name="v"/> whose local context is not contained in
    /// <c>?mvarId</c>'s.</item>
    /// </list>
    /// </summary>
    /// <remarks>
    /// Lean's context approximation (<c>Config.ctxApprox</c>, off by default), which would instead
    /// narrow such a metavariable's context, is not part of this layer.
    /// </remarks>
    public Expr? CheckAssignment(MVarId mvarId, IReadOnlyList<Expr> fvars, Expr v)
    {
        ArgumentNullException.ThrowIfNull(fvars);
        ArgumentNullException.ThrowIfNull(v);
        // ?m must not occur in the type of an abstracted variable, or ?m := fun fvars => v is cyclic.
        foreach (var fvar in fvars)
        {
            if (!MCtx.OccursCheck(mvarId, GetFVarLocalDecl(fvar).Type))
            {
                return null;
            }
        }
        if (!v.HasExprMVar && !v.HasFVar)
        {
            return v;
        }
        var mvarDecl = GetMVarDecl(mvarId);
        bool hasCtxLocals = fvars.Any(mvarDecl.LCtx.ContainsFVar);
        if (!CheckAssignmentQuick(hasCtxLocals, mvarDecl, mvarId, fvars, v))
        {
            var checker = new CheckAssignmentFn(this, mvarId, mvarDecl, fvars, hasCtxLocals);
            if (checker.Check(this.InstantiateMVars(v)) is not { } checkedV)
            {
                return null;
            }
            v = checkedV;
        }
        return TypeOccursCheck(mvarId, v) ? v : null;
    }

    /// <summary>
    /// A fast conservative pass of <see cref="CheckAssignment"/> (Lean's <c>CheckAssignmentQuick</c>):
    /// true means the assignment is fine as is; false means the full check must decide.
    /// </summary>
    private bool CheckAssignmentQuick(bool hasCtxLocals, MetavarDecl mvarDecl, MVarId mvarId, IReadOnlyList<Expr> fvars, Expr e)
    {
        var mctx = MCtx;
        var lctx = LCtx;
        var visited = new HashSet<Expr>(ReferenceEqualityComparer.Instance);
        return Visit(e);

        bool Visit(Expr e)
        {
            if (!e.HasExprMVar && !e.HasFVar)
            {
                return true;
            }
            if (!visited.Add(e))
            {
                return true;
            }
            RuntimeHelpers.EnsureSufficientExecutionStack();
            switch (e)
            {
                case MDataExpr m:
                    return Visit(m.Expr);
                case ProjExpr p:
                    return Visit(p.Struct);
                case AppExpr a:
                    return Visit(a.Fn) && Visit(a.Arg);
                case BindingExpr b:
                    return Visit(b.BinderType) && Visit(b.Body);
                case LetExpr l:
                    return Visit(l.BinderType) && Visit(l.Value) && Visit(l.Body);
                case FVarExpr f:
                    if (mvarDecl.LCtx.Contains(f.Id))
                    {
                        return true;
                    }
                    if (lctx.Find(f.Id) is LDecl { Nondep: false })
                    {
                        return false; // the full check zeta-expands it
                    }
                    return fvars.Any(x => x.Equals(f));
                case MVarExpr mv:
                    var id = mv.Id;
                    if (mctx.IsAssigned(id) || id == mvarId || hasCtxLocals)
                    {
                        return false;
                    }
                    if (mctx.FindDecl(id) is not { } decl || !decl.LCtx.IsSubPrefixOf(mvarDecl.LCtx, fvars))
                    {
                        return false;
                    }
                    return !mctx.IsDelayedAssigned(id);
                default:
                    return true;
            }
        }
    }

    /// <summary>
    /// Whether no metavariable of <paramref name="v"/> has <paramref name="mvarId"/> in its type:
    /// with <c>?m₁ : Nat</c> and <c>?m₂ : Fin ?m₁</c>, <c>?m₁ := ?m₂.1</c> must fail (Lean's
    /// <c>typeOccursCheck</c>, issue #4405).
    /// </summary>
    private bool TypeOccursCheck(MVarId mvarId, Expr v)
    {
        if (!v.HasExprMVar)
        {
            return true;
        }
        var mctx = MCtx;
        var visited = new HashSet<Expr>(ReferenceEqualityComparer.Instance);
        var pending = new Stack<Expr>();
        pending.Push(v);
        while (pending.Count > 0)
        {
            var e = pending.Pop();
            if (!e.HasExprMVar || !visited.Add(e))
            {
                continue;
            }
            switch (e)
            {
                case MDataExpr m:
                    pending.Push(m.Expr);
                    break;
                case ProjExpr p:
                    pending.Push(p.Struct);
                    break;
                case AppExpr a:
                    pending.Push(a.Arg);
                    pending.Push(a.Fn);
                    break;
                case BindingExpr b:
                    pending.Push(b.Body);
                    pending.Push(b.BinderType);
                    break;
                case LetExpr l:
                    pending.Push(l.Body);
                    pending.Push(l.Value);
                    pending.Push(l.BinderType);
                    break;
                case MVarExpr mv:
                    if (mctx.FindDecl(mv.Id) is not { } decl || !mctx.OccursCheck(mvarId, decl.Type))
                    {
                        return false;
                    }
                    break;
            }
        }
        return true;
    }

    /// <summary>The full check of <see cref="CheckAssignment"/> (Lean's <c>CheckAssignment.check</c>); null means it fails.</summary>
    private sealed class CheckAssignmentFn(MetaM meta, MVarId mvarId, MetavarDecl mvarDecl, IReadOnlyList<Expr> fvars, bool hasCtxLocals)
    {
        private readonly Dictionary<Expr, Expr> _cache = new(ReferenceEqualityComparer.Instance);

        public Expr? Check(Expr e)
        {
            if (!e.HasExprMVar && !e.HasFVar)
            {
                return e;
            }
            if (_cache.TryGetValue(e, out var cached))
            {
                return cached;
            }
            meta.Budget.Tick();
            Expr? r;
            switch (e)
            {
                case MDataExpr m:
                    r = Check(m.Expr) is { } b ? m.UpdateMData(b) : null;
                    break;
                case ProjExpr p:
                    r = Check(p.Struct) is { } s ? p.UpdateProj(s) : null;
                    break;
                case BindingExpr bnd:
                    r = Check(bnd.BinderType) is { } d && Check(bnd.Body) is { } body ? bnd.UpdateBinding(d, body) : null;
                    break;
                case LetExpr l:
                    r = Check(l.BinderType) is { } t && Check(l.Value) is { } v && Check(l.Body) is { } lb ? l.UpdateLet(t, v, lb) : null;
                    break;
                case FVarExpr:
                    r = CheckFVar(e);
                    break;
                case MVarExpr mv:
                    r = CheckMVar(mv);
                    break;
                case AppExpr:
                    // On failure, a beta-redex is reduced and checked again: `?m := (fun _ => A) a`
                    // succeeds even when `a` is out of scope.
                    r = CheckApp(e) ?? (e.IsHeadBetaTarget() ? CheckApp(e.HeadBeta()) : null);
                    break;
                default:
                    r = e;
                    break;
            }
            if (r is not null)
            {
                _cache[e] = r;
            }
            return r;
        }

        private Expr? CheckFVar(Expr fvar)
        {
            if (mvarDecl.LCtx.ContainsFVar(fvar))
            {
                return fvar;
            }
            // A dependent local definition is expanded: its value may be in scope even if it is not.
            if (meta.LCtx.FindFVar(fvar) is LDecl { Nondep: false } l)
            {
                return Check(l.Value);
            }
            return fvars.Any(x => x.Equals(fvar)) ? fvar : null;
        }

        private Expr? CheckMVar(MVarExpr mvar)
        {
            var id = mvar.Id;
            if (id == mvarId)
            {
                return null; // occurs check
            }
            if (meta.MCtx.GetExprAssignment(id) is { } v)
            {
                return Check(v);
            }
            var decl = meta.MCtx.FindDecl(id) ?? throw new MetaException($"unknown metavariable '?{id}'");
            if (hasCtxLocals)
            {
                return null; // not a pattern; the caller falls back to first-order unification
            }
            if (meta.MCtx.GetDelayedMVarAssignment(id) is { } delayed && !meta.MCtx.OccursCheck(mvarId, Expr.MVar(delayed.MVarIdPending)))
            {
                return null; // the occurs check must look through the pending metavariable
            }
            // The context of ?n, minus the variables being abstracted, must be a subprefix of ?m's.
            if (decl.LCtx.IsSubPrefixOf(mvarDecl.LCtx, fvars))
            {
                return mvar;
            }
            // Otherwise ?n would need a smaller context, which only context approximation creates.
            return null;
        }

        private Expr? CheckApp(Expr e)
        {
            var f = e.GetAppFn();
            var args = e.GetAppArgs();
            if (Check(f) is not { } newF)
            {
                return null;
            }
            bool changed = !ReferenceEquals(newF, f);
            for (int i = 0; i < args.Length; i++)
            {
                if (Check(args[i]) is not { } a)
                {
                    return null;
                }
                changed |= !ReferenceEquals(a, args[i]);
                args[i] = a;
            }
            return changed ? ExprExtensions.MkAppN(newF, args) : e;
        }
    }
}
