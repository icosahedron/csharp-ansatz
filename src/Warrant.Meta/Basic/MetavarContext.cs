using System.Collections.Immutable;
using Warrant.Cic;

namespace Warrant.Meta;

/// <summary>How unification treats a metavariable (Lean's <c>MetavarKind</c>; docs/m5a/02).</summary>
public enum MetavarKind : byte
{
    /// <summary>Assigned freely by unification: <c>apply</c>'s arguments, telescopes.</summary>
    Natural,

    /// <summary>Unification avoids assigning it; instance arguments, solved by instance resolution.</summary>
    Synthetic,

    /// <summary>Never assigned by unification; goals, which only a tactic assigns.</summary>
    SyntheticOpaque,
}

/// <summary>A local type-class instance, by class and free variable (Lean's <c>LocalInstance</c>).</summary>
/// <param name="ClassName">The class.</param>
/// <param name="FVar">The free variable that is the instance.</param>
public sealed record LocalInstance(Name ClassName, Expr FVar);

/// <summary>The declaration of an expression metavariable (Lean's <c>MetavarDecl</c>).</summary>
/// <param name="UserName">The goal tag shown as <c>case tag</c>; anonymous if none.</param>
/// <param name="LCtx">The local context the metavariable's value may use.</param>
/// <param name="Type">Its type, in <paramref name="LCtx"/>.</param>
/// <param name="Depth">The metavariable-context depth it was created at; only metavariables of the current depth are assignable.</param>
/// <param name="LocalInstances">The local instances of <paramref name="LCtx"/>.</param>
/// <param name="Kind">How unification treats it.</param>
/// <param name="NumScopeArgs">How many of its arguments stand for dependencies (see Lean's <c>CheckAssignment</c>).</param>
/// <param name="Index">Its creation order, for display.</param>
public sealed record MetavarDecl(
    Name UserName,
    LocalContext LCtx,
    Expr Type,
    int Depth,
    ImmutableArray<LocalInstance> LocalInstances,
    MetavarKind Kind,
    int NumScopeArgs,
    int Index);

/// <summary>The declaration of a universe metavariable (Lean's <c>LevelMetavarDecl</c>).</summary>
/// <param name="Depth">The metavariable-context depth it was created at.</param>
/// <param name="Index">Its creation order, for display.</param>
public sealed record LevelMetavarDecl(int Depth, int Index);

/// <summary>
/// A delayed assignment <c>?m #[fvars] := ?pending</c>: <c>?m</c> stands for
/// <c>fun fvars => ?pending</c>, to be substituted only once <c>?pending</c> is fully solved (Lean's
/// <c>DelayedMetavarAssignment</c>; docs/m5a/02, "Delayed assignment").
/// </summary>
/// <param name="FVars">Free variables of <paramref name="MVarIdPending"/>'s local context.</param>
/// <param name="MVarIdPending">A synthetic-opaque metavariable not solved yet.</param>
public sealed record DelayedMetavarAssignment(ImmutableArray<Expr> FVars, MVarId MVarIdPending);

/// <summary>
/// The metavariable context: declarations and assignments of expression, universe and delayed
/// metavariables (a port of Lean 4's <c>Lean/MetavarContext.lean</c>).
/// </summary>
/// <remarks>
/// It is immutable, on <see cref="System.Collections.Immutable"/> maps as Lean's are
/// <c>PersistentHashMap</c>s, so saving and restoring it for backtracking is a reference copy. The
/// low-level <c>Assign*</c> methods do no checks; <see cref="MetaM.CheckedAssign"/> does.
/// </remarks>
public sealed record MetavarContext
{
    /// <summary>The empty context.</summary>
    public static MetavarContext Empty { get; } = new();

    /// <summary>The current depth; only metavariables declared at this depth are assignable.</summary>
    public int Depth { get; init; }

    /// <summary>Universe metavariables declared at this depth or deeper are assignable.</summary>
    public int LevelAssignDepth { get; init; }

    /// <summary>Counter for <see cref="LevelMetavarDecl.Index"/>.</summary>
    public int LMVarCounter { get; init; }

    /// <summary>Counter for <see cref="MetavarDecl.Index"/>.</summary>
    public int MVarCounter { get; init; }

    /// <summary>Universe metavariable declarations.</summary>
    public ImmutableDictionary<LMVarId, LevelMetavarDecl> LDecls { get; init; } = ImmutableDictionary<LMVarId, LevelMetavarDecl>.Empty;

    /// <summary>Expression metavariable declarations.</summary>
    public ImmutableDictionary<MVarId, MetavarDecl> Decls { get; init; } = ImmutableDictionary<MVarId, MetavarDecl>.Empty;

    /// <summary>Goal tags to metavariables.</summary>
    public ImmutableDictionary<Name, MVarId> UserNames { get; init; } = ImmutableDictionary<Name, MVarId>.Empty;

    /// <summary>Universe metavariable assignments.</summary>
    public ImmutableDictionary<LMVarId, Level> LAssignment { get; init; } = ImmutableDictionary<LMVarId, Level>.Empty;

    /// <summary>Expression metavariable assignments.</summary>
    public ImmutableDictionary<MVarId, Expr> EAssignment { get; init; } = ImmutableDictionary<MVarId, Expr>.Empty;

    /// <summary>Delayed assignments.</summary>
    public ImmutableDictionary<MVarId, DelayedMetavarAssignment> DAssignment { get; init; } = ImmutableDictionary<MVarId, DelayedMetavarAssignment>.Empty;

    /// <summary>
    /// Declares <paramref name="mvarId"/> at the current depth (Lean's <c>addExprMVarDecl</c>); the
    /// id must be fresh.
    /// </summary>
    public MetavarContext AddExprMVarDecl(
        MVarId mvarId,
        Name userName,
        LocalContext lctx,
        ImmutableArray<LocalInstance> localInstances,
        Expr type,
        MetavarKind kind = MetavarKind.Natural,
        int numScopeArgs = 0)
    {
        ArgumentNullException.ThrowIfNull(userName);
        return this with
        {
            MVarCounter = MVarCounter + 1,
            Decls = Decls.SetItem(mvarId, new MetavarDecl(userName, lctx, type, Depth, localInstances, kind, numScopeArgs, MVarCounter)),
            UserNames = userName.IsAnonymous ? UserNames : UserNames.SetItem(userName, mvarId),
        };
    }

    /// <summary>Declares the universe metavariable <paramref name="mvarId"/> at the current depth (Lean's <c>addLevelMVarDecl</c>).</summary>
    public MetavarContext AddLevelMVarDecl(LMVarId mvarId) => this with
    {
        LMVarCounter = LMVarCounter + 1,
        LDecls = LDecls.SetItem(mvarId, new LevelMetavarDecl(Depth, LMVarCounter)),
    };

    /// <summary>The declaration of <paramref name="mvarId"/>, or null.</summary>
    public MetavarDecl? FindDecl(MVarId mvarId) => Decls.TryGetValue(mvarId, out var d) ? d : null;

    /// <summary>The declaration of <paramref name="mvarId"/>.</summary>
    /// <exception cref="MetaException">It is not declared.</exception>
    public MetavarDecl GetDecl(MVarId mvarId) =>
        FindDecl(mvarId) ?? throw new MetaException($"unknown metavariable '?{mvarId}'");

    /// <summary>The declaration of the universe metavariable <paramref name="mvarId"/>, or null.</summary>
    public LevelMetavarDecl? FindLevelDecl(LMVarId mvarId) => LDecls.TryGetValue(mvarId, out var d) ? d : null;

    /// <summary>The declaration of the universe metavariable <paramref name="mvarId"/>.</summary>
    /// <exception cref="MetaException">It is not declared.</exception>
    public LevelMetavarDecl GetLevelDecl(LMVarId mvarId) =>
        FindLevelDecl(mvarId) ?? throw new MetaException($"unknown universe metavariable '?{mvarId}'");

    /// <summary>The metavariable tagged <paramref name="userName"/>, or null.</summary>
    public MVarId? FindUserName(Name userName) => UserNames.TryGetValue(userName, out var m) ? m : null;

    /// <summary>
    /// Replaces <paramref name="mvarId"/>'s declaration by <c>f(decl)</c>, which may change terms
    /// only up to definitional equality; does nothing if it is not declared.
    /// </summary>
    public MetavarContext ModifyExprMVarDecl(MVarId mvarId, Func<MetavarDecl, MetavarDecl> f)
    {
        ArgumentNullException.ThrowIfNull(f);
        return FindDecl(mvarId) is { } d ? this with { Decls = Decls.SetItem(mvarId, f(d)) } : this;
    }

    /// <summary>Sets the kind of <paramref name="mvarId"/>.</summary>
    public MetavarContext SetMVarKind(MVarId mvarId, MetavarKind kind) =>
        this with { Decls = Decls.SetItem(mvarId, GetDecl(mvarId) with { Kind = kind }) };

    /// <summary>Sets the goal tag of <paramref name="mvarId"/>, keeping <see cref="UserNames"/> in step.</summary>
    public MetavarContext SetMVarUserName(MVarId mvarId, Name userName)
    {
        ArgumentNullException.ThrowIfNull(userName);
        var decl = GetDecl(mvarId);
        var userNames = UserNames.Remove(decl.UserName);
        return this with
        {
            Decls = Decls.SetItem(mvarId, decl with { UserName = userName }),
            UserNames = userName.IsAnonymous ? userNames : userNames.SetItem(userName, mvarId),
        };
    }

    /// <summary>Sets the type of <paramref name="mvarId"/> (to a definitionally equal one).</summary>
    public MetavarContext SetMVarType(MVarId mvarId, Expr type) =>
        this with { Decls = Decls.SetItem(mvarId, GetDecl(mvarId) with { Type = type }) };

    /// <summary>Replaces the local context of <paramref name="mvarId"/> by <c>f(lctx)</c>, if it is declared.</summary>
    public MetavarContext ModifyExprMVarLCtx(MVarId mvarId, Func<LocalContext, LocalContext> f) =>
        ModifyExprMVarDecl(mvarId, d => d with { LCtx = f(d.LCtx) });

    /// <summary>
    /// One level deeper (Lean's <c>incDepth</c>): metavariables declared so far become read-only, and
    /// universe ones too unless <paramref name="allowLevelAssignments"/>.
    /// </summary>
    public MetavarContext IncDepth(bool allowLevelAssignments = false)
    {
        int depth = Depth + 1;
        return this with { Depth = depth, LevelAssignDepth = allowLevelAssignments ? LevelAssignDepth : depth };
    }

    /// <summary>The assignment of <paramref name="mvarId"/>, or null.</summary>
    public Expr? GetExprAssignment(MVarId mvarId) => EAssignment.TryGetValue(mvarId, out var v) ? v : null;

    /// <summary>The assignment of the universe metavariable <paramref name="mvarId"/>, or null.</summary>
    public Level? GetLevelAssignment(LMVarId mvarId) => LAssignment.TryGetValue(mvarId, out var v) ? v : null;

    /// <summary>The delayed assignment of <paramref name="mvarId"/>, or null.</summary>
    public DelayedMetavarAssignment? GetDelayedMVarAssignment(MVarId mvarId) => DAssignment.TryGetValue(mvarId, out var d) ? d : null;

    /// <summary>Whether <paramref name="mvarId"/> is assigned.</summary>
    public bool IsAssigned(MVarId mvarId) => EAssignment.ContainsKey(mvarId);

    /// <summary>Whether <paramref name="mvarId"/> is delayed-assigned.</summary>
    public bool IsDelayedAssigned(MVarId mvarId) => DAssignment.ContainsKey(mvarId);

    /// <summary>Whether <paramref name="mvarId"/> is assigned or delayed-assigned, i.e. already solved.</summary>
    public bool IsAssignedOrDelayedAssigned(MVarId mvarId) => IsAssigned(mvarId) || IsDelayedAssigned(mvarId);

    /// <summary>Whether the universe metavariable <paramref name="mvarId"/> is assigned.</summary>
    public bool IsLevelMVarAssigned(LMVarId mvarId) => LAssignment.ContainsKey(mvarId);

    /// <summary>Whether <paramref name="mvarId"/> belongs to the current depth (Lean's <c>MVarId.isAssignable</c>).</summary>
    public bool IsAssignable(MVarId mvarId) => GetDecl(mvarId).Depth == Depth;

    /// <summary>Whether the universe metavariable <paramref name="mvarId"/> may be assigned (Lean's <c>isLevelMVarAssignable</c>).</summary>
    public bool IsLevelMVarAssignable(LMVarId mvarId) => GetLevelDecl(mvarId).Depth >= LevelAssignDepth;

    /// <summary>
    /// Follows delayed assignments <c>?m₁ := fun … => ?m₂</c>, … to the first metavariable that is
    /// not delayed-assigned (Lean's <c>getDelayedMVarRoot</c>).
    /// </summary>
    public MVarId GetDelayedMVarRoot(MVarId mvarId)
    {
        while (GetDelayedMVarAssignment(mvarId) is { } d)
        {
            mvarId = d.MVarIdPending;
        }
        return mvarId;
    }

    /// <summary>Records <c>?mvarId := val</c>, without any check (Lean's <c>MVarId.assign</c>).</summary>
    public MetavarContext Assign(MVarId mvarId, Expr val)
    {
        ArgumentNullException.ThrowIfNull(val);
        return this with { EAssignment = EAssignment.SetItem(mvarId, val) };
    }

    /// <summary>Records <c>?mvarId := val</c> for a universe metavariable, without any check (Lean's <c>assignLevelMVar</c>).</summary>
    public MetavarContext AssignLevelMVar(LMVarId mvarId, Level val)
    {
        ArgumentNullException.ThrowIfNull(val);
        return this with { LAssignment = LAssignment.SetItem(mvarId, val) };
    }

    /// <summary>
    /// Records the delayed assignment <c>?mvarId #[fvars] := ?mvarIdPending</c>; the caller ensures
    /// <paramref name="mvarId"/> is neither assigned nor delayed-assigned (Lean's <c>assignDelayedMVar</c>).
    /// </summary>
    public MetavarContext AssignDelayedMVar(MVarId mvarId, ImmutableArray<Expr> fvars, MVarId mvarIdPending) =>
        this with { DAssignment = DAssignment.SetItem(mvarId, new DelayedMetavarAssignment(fvars, mvarIdPending)) };

    /// <summary>
    /// Substitutes assigned metavariables in <paramref name="e"/>, recursively, and returns the
    /// result with this context updated by path compression (Lean's <c>instantiateMVarsCore</c>). See
    /// <see cref="InstantiateMVars"/> for the rules.
    /// </summary>
    public (Expr Result, MetavarContext MCtx) InstantiateMVars(Expr e, MetaBudget? budget = null)
    {
        ArgumentNullException.ThrowIfNull(e);
        if (!e.HasExprMVar && !e.HasLevelMVar)
        {
            return (e, this);
        }
        var fn = new InstantiateMVarsFn(this, budget);
        var r = fn.Visit(e);
        return (r, fn.MCtx);
    }

    /// <summary>Substitutes assigned universe metavariables in <paramref name="l"/>, with path compression.</summary>
    public (Level Result, MetavarContext MCtx) InstantiateLevelMVars(Level l, MetaBudget? budget = null)
    {
        ArgumentNullException.ThrowIfNull(l);
        if (!l.HasMVar)
        {
            return (l, this);
        }
        var fn = new InstantiateMVarsFn(this, budget);
        var r = fn.VisitLevel(l);
        return (r, fn.MCtx);
    }

    /// <summary>
    /// Whether <paramref name="e"/> depends on a free variable satisfying <paramref name="pf"/> or an
    /// unassigned metavariable satisfying <paramref name="pm"/> (Lean's <c>findExprDependsOn</c>).
    /// Assigned metavariables are followed; an unassigned one that fails <paramref name="pm"/> counts
    /// as depending on every variable of its local context, since it may be assigned a term using it.
    /// </summary>
    public (bool Result, MetavarContext MCtx) FindExprDependsOn(Expr e, Func<FVarId, bool>? pf = null, Func<MVarId, bool>? pm = null, MetaBudget? budget = null)
    {
        ArgumentNullException.ThrowIfNull(e);
        if (!e.HasFVar && !e.HasExprMVar && !e.HasLevelMVar)
        {
            return (false, this);
        }
        var dep = new DependsOn(this, pf ?? (_ => false), pm ?? (_ => false), budget);
        bool r = dep.Visit(e);
        return (r, dep.MCtx);
    }

    /// <summary>
    /// Like <see cref="FindExprDependsOn"/>, for a local declaration's type and value; with
    /// <paramref name="generalizeNondepLet"/>, the value of a nondependent let is ignored (Lean's
    /// <c>findLocalDeclDependsOn</c>).
    /// </summary>
    public (bool Result, MetavarContext MCtx) FindLocalDeclDependsOn(LocalDecl localDecl, Func<FVarId, bool>? pf = null, Func<MVarId, bool>? pm = null, bool generalizeNondepLet = true, MetaBudget? budget = null)
    {
        ArgumentNullException.ThrowIfNull(localDecl);
        var (r, mctx) = FindExprDependsOn(localDecl.Type, pf, pm, budget);
        if (r || localDecl is not LDecl l || (generalizeNondepLet && l.Nondep))
        {
            return (r, mctx);
        }
        return mctx.FindExprDependsOn(l.Value, pf, pm, budget);
    }

    /// <summary>
    /// Whether <paramref name="e"/> does <em>not</em> contain <paramref name="mvarId"/>, directly or
    /// through assignments and delayed assignments (Lean's <c>occursCheck</c>).
    /// </summary>
    public bool OccursCheck(MVarId mvarId, Expr e)
    {
        ArgumentNullException.ThrowIfNull(e);
        if (!e.HasExprMVar)
        {
            return true;
        }
        var visited = new HashSet<Expr>(ReferenceEqualityComparer.Instance);
        var pending = new Stack<Expr>();
        pending.Push(e);
        while (pending.Count > 0)
        {
            var x = pending.Pop();
            if (!x.HasExprMVar || !visited.Add(x))
            {
                continue;
            }
            switch (x)
            {
                case ProjExpr p:
                    pending.Push(p.Struct);
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
                case MDataExpr m:
                    pending.Push(m.Expr);
                    break;
                case AppExpr a:
                    pending.Push(a.Arg);
                    pending.Push(a.Fn);
                    break;
                case MVarExpr mv:
                    // visitMVar: follow assignments, then the delayed-assignment chain.
                    var id = mv.Id;
                    while (true)
                    {
                        if (id == mvarId)
                        {
                            return false;
                        }
                        if (GetExprAssignment(id) is { } v)
                        {
                            pending.Push(v);
                            break;
                        }
                        if (GetDelayedMVarAssignment(id) is not { } d)
                        {
                            break;
                        }
                        id = d.MVarIdPending;
                    }
                    break;
            }
        }
        return true;
    }

    private sealed class DependsOn(MetavarContext mctx, Func<FVarId, bool> pf, Func<MVarId, bool> pm, MetaBudget? budget)
    {
        private readonly HashSet<Expr> _visited = new(ReferenceEqualityComparer.Instance);

        public MetavarContext MCtx { get; private set; } = mctx;

        public bool Visit(Expr e)
        {
            if (!e.HasExprMVar && !e.HasFVar)
            {
                return false;
            }
            if (!_visited.Add(e))
            {
                return false;
            }
            budget?.Tick();
            return VisitMain(e);
        }

        private bool VisitApp(Expr e)
        {
            while (e is AppExpr a)
            {
                if (Visit(a.Arg))
                {
                    return true;
                }
                e = a.Fn;
            }
            return Visit(e);
        }

        private bool VisitMain(Expr e)
        {
            switch (e)
            {
                case ProjExpr p:
                    return Visit(p.Struct);
                case BindingExpr b:
                    return Visit(b.BinderType) || Visit(b.Body);
                case LetExpr l:
                    return Visit(l.BinderType) || Visit(l.Value) || Visit(l.Body);
                case MDataExpr m:
                    return Visit(m.Expr);
                case AppExpr:
                    var f = e.GetAppFn();
                    if (f is MVarExpr fm)
                    {
                        var (e2, mctx2) = MCtx.InstantiateMVars(e, budget);
                        MCtx = mctx2;
                        if (!e2.GetAppFn().Equals(f))
                        {
                            return VisitMain(e2);
                        }
                        if (pm(fm.Id))
                        {
                            return true;
                        }
                    }
                    return VisitApp(e);
                case MVarExpr mv:
                    if (MCtx.GetExprAssignment(mv.Id) is { } a)
                    {
                        return Visit(a);
                    }
                    if (pm(mv.Id))
                    {
                        return true;
                    }
                    return MCtx.GetDecl(mv.Id).LCtx.Decls.Any(d => pf(d.FVarId));
                case FVarExpr fv:
                    return pf(fv.Id);
                default:
                    return false;
            }
        }
    }
}

/// <summary>
/// A computation that carries a metavariable context (Lean's <c>MonadMCtx</c>): <see cref="MetaM"/>,
/// and the internal states of binder construction and instantiation.
/// </summary>
public interface IMonadMCtx
{
    /// <summary>The current metavariable context.</summary>
    MetavarContext MCtx { get; set; }

    /// <summary>The budget charged by traversals, if any.</summary>
    MetaBudget? Budget { get; }
}

/// <summary>Lean's <c>MonadMCtx</c> operations, over any <see cref="IMonadMCtx"/>.</summary>
public static class MonadMCtxExtensions
{
    /// <summary>
    /// Substitutes assigned metavariables in <paramref name="e"/> and keeps the path-compressed
    /// context (Lean's <c>instantiateMVars</c>).
    /// </summary>
    public static Expr InstantiateMVars(this IMonadMCtx m, Expr e)
    {
        ArgumentNullException.ThrowIfNull(m);
        ArgumentNullException.ThrowIfNull(e);
        if (!e.HasExprMVar && !e.HasLevelMVar)
        {
            return e;
        }
        var (r, mctx) = m.MCtx.InstantiateMVars(e, m.Budget);
        m.MCtx = mctx;
        return r;
    }

    /// <summary>Substitutes assigned universe metavariables in <paramref name="l"/> (Lean's <c>instantiateLevelMVars</c>).</summary>
    public static Level InstantiateLevelMVars(this IMonadMCtx m, Level l)
    {
        ArgumentNullException.ThrowIfNull(m);
        var (r, mctx) = m.MCtx.InstantiateLevelMVars(l, m.Budget);
        m.MCtx = mctx;
        return r;
    }

    /// <summary>See <see cref="MetavarContext.FindExprDependsOn"/>.</summary>
    public static bool FindExprDependsOn(this IMonadMCtx m, Expr e, Func<FVarId, bool>? pf = null, Func<MVarId, bool>? pm = null)
    {
        ArgumentNullException.ThrowIfNull(m);
        var (r, mctx) = m.MCtx.FindExprDependsOn(e, pf, pm, m.Budget);
        m.MCtx = mctx;
        return r;
    }

    /// <summary>See <see cref="MetavarContext.FindLocalDeclDependsOn"/>.</summary>
    public static bool FindLocalDeclDependsOn(this IMonadMCtx m, LocalDecl localDecl, Func<FVarId, bool>? pf = null, Func<MVarId, bool>? pm = null, bool generalizeNondepLet = true)
    {
        ArgumentNullException.ThrowIfNull(m);
        var (r, mctx) = m.MCtx.FindLocalDeclDependsOn(localDecl, pf, pm, generalizeNondepLet, m.Budget);
        m.MCtx = mctx;
        return r;
    }

    /// <summary>Whether <paramref name="e"/> depends on <paramref name="fvarId"/> (Lean's <c>dependsOn</c>/<c>exprDependsOn</c>).</summary>
    public static bool DependsOn(this IMonadMCtx m, Expr e, FVarId fvarId) => m.FindExprDependsOn(e, x => x == fvarId);

    /// <summary>Whether <paramref name="localDecl"/> depends on <paramref name="fvarId"/> (Lean's <c>localDeclDependsOn</c>).</summary>
    public static bool LocalDeclDependsOn(this IMonadMCtx m, LocalDecl localDecl, FVarId fvarId, bool generalizeNondepLet = true) =>
        m.FindLocalDeclDependsOn(localDecl, x => x == fvarId, generalizeNondepLet: generalizeNondepLet);

    /// <summary>
    /// Whether <paramref name="e"/> depends on <paramref name="x"/>, a free variable or an
    /// unassigned metavariable (Lean's <c>exprDependsOn'</c>).
    /// </summary>
    public static bool ExprDependsOn(this IMonadMCtx m, Expr e, Expr x) => x switch
    {
        FVarExpr f => m.FindExprDependsOn(e, pf: id => id == f.Id),
        MVarExpr mv => m.FindExprDependsOn(e, pm: id => id == mv.Id),
        _ => false,
    };
}
