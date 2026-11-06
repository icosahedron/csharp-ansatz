using System.Collections.Immutable;
using Warrant.Cic;
using Warrant.Kernel;

namespace Warrant.Meta;

/// <summary>Meta's configuration (Lean's <c>Meta.Config</c>); the reduction fields are in <c>Reduce/Transparency.cs</c>.</summary>
public sealed partial record MetaConfig
{
    /// <summary>The defaults.</summary>
    public static MetaConfig Default { get; } = new();

    /// <summary>
    /// Let unification assign synthetic-opaque metavariables (goals); <c>exact</c> turns it on
    /// through <see cref="MetaM.WithAssignableSyntheticOpaque"/>.
    /// </summary>
    public bool AssignSyntheticOpaque { get; init; }
}

/// <summary>The part of <see cref="MetaM"/>'s state that scopes save and restore (Lean's <c>Meta.Context</c>).</summary>
/// <param name="LCtx">The local context.</param>
/// <param name="LocalInstances">The local instances of <paramref name="LCtx"/>.</param>
/// <param name="Config">The configuration.</param>
public sealed record MetaContext(LocalContext LCtx, ImmutableArray<LocalInstance> LocalInstances, MetaConfig Config)
{
    /// <summary>An empty local context with the default configuration.</summary>
    public static MetaContext Empty { get; } = new(LocalContext.Empty, [], MetaConfig.Default);
}

/// <summary>A universe constraint <c>Lhs =?= Rhs</c> that unification postponed (Lean's <c>PostponedEntry</c>).</summary>
/// <param name="Lhs">The left-hand side.</param>
/// <param name="Rhs">The right-hand side.</param>
public sealed record PostponedEntry(Level Lhs, Level Rhs);

/// <summary>The backtrackable state of <see cref="MetaM"/> (Lean's <c>Meta.SavedState</c>).</summary>
/// <param name="MCtx">The metavariable context.</param>
/// <param name="Postponed">The postponed universe constraints.</param>
/// <remarks>
/// As in Lean, the name generator and the caches are not restored, so names created after a save
/// stay unique.
/// </remarks>
public sealed record SavedState(MetavarContext MCtx, ImmutableList<PostponedEntry> Postponed);

/// <summary>
/// The Meta monad: the environment, the metavariable context, the current local context and the
/// budget, with the operations of Lean 4's <c>Lean/Meta/Basic.lean</c> that do not need reduction
/// (fresh metavariables, scopes, the non-reducing telescopes, and binder construction).
/// </summary>
/// <remarks>
/// <para>
/// Lean's <c>ReaderT Context (StateRefT State CoreM)</c> becomes one mutable object: the
/// <see cref="MCtx"/> is state, and the <see cref="Context"/> is set for the extent of a
/// <c>With*</c> scope and restored afterwards, even on an exception. An instance is single-threaded.
/// </para>
/// <para>
/// <c>whnf</c>, <c>inferType</c> and <c>isDefEq</c>, which Lean forward-declares in Basic.lean and
/// implements in separate files, are added to this partial class by the reduction layer, together
/// with the telescopes that reduce (<c>forallTelescopeReducing</c>, <c>forallBoundedTelescope</c>,
/// <c>forallMetaTelescopeReducing</c>, <c>instantiateForall</c>).
/// </para>
/// <para>
/// Local instances are carried through scopes but not detected: <see cref="WithLocalDecl{T}"/>
/// does not yet register a variable whose type is a class (Lean's <c>withNewLocalInstances</c>),
/// which needs class information from the attribute sidecar.
/// </para>
/// </remarks>
public sealed partial class MetaM : IMonadMCtx
{
    private static readonly Name UniqPrefix = Name.From("_uniq");

    private readonly NameGenerator _ngen = new(UniqPrefix);
    private int _nextMacroScope = 1;

    /// <summary>Creates a Meta computation over <paramref name="env"/>.</summary>
    /// <param name="env">The environment constants are looked up in.</param>
    /// <param name="limits">Meta's fuel, deadline and cancellation token (default: <see cref="MetaLimits.Default"/>).</param>
    public MetaM(KernelEnvironment env, MetaLimits? limits = null)
    {
        Env = env ?? throw new ArgumentNullException(nameof(env));
        Budget = new MetaBudget(limits ?? MetaLimits.Default);
        KernelLimits = KernelLimits.Interactive with { Deadline = Budget.Limits.Deadline, CancellationToken = Budget.Limits.CancellationToken };
    }

    /// <summary>
    /// The limits of the kernel that <see cref="Check"/> hands ground terms to (M5b KTD12); by default the kernel's
    /// interactive fuel with Meta's deadline and cancellation token. The kernel running out of them fails with a
    /// <see cref="MetaResourceException"/>.
    /// </summary>
    public KernelLimits KernelLimits { get; init; }

    /// <summary>The environment.</summary>
    public KernelEnvironment Env { get; }

    /// <summary>The fuel, deadline and cancellation token Meta's traversals charge.</summary>
    public MetaBudget Budget { get; }

    MetaBudget? IMonadMCtx.Budget => Budget;

    /// <summary>The metavariable context.</summary>
    public MetavarContext MCtx { get; set; } = MetavarContext.Empty;

    /// <summary>The current scope: local context, local instances and configuration.</summary>
    public MetaContext Context { get; private set; } = MetaContext.Empty;

    /// <summary>The current local context (Lean's <c>getLCtx</c>).</summary>
    public LocalContext LCtx => Context.LCtx;

    /// <summary>The current local instances (Lean's <c>getLocalInstances</c>).</summary>
    public ImmutableArray<LocalInstance> LocalInstances => Context.LocalInstances;

    /// <summary>The current configuration (Lean's <c>getConfig</c>).</summary>
    public MetaConfig Config => Context.Config;

    /// <summary>A fresh free-variable id.</summary>
    public FVarId MkFreshFVarId() => new(_ngen.Next());

    /// <summary>A fresh metavariable id.</summary>
    public MVarId MkFreshMVarId() => new(_ngen.Next());

    /// <summary>A fresh universe-metavariable id.</summary>
    public LMVarId MkFreshLMVarId() => new(_ngen.Next());

    /// <summary>The universe constraints unification postponed (Lean's <c>State.postponed</c>).</summary>
    public ImmutableList<PostponedEntry> Postponed { get; set; } = [];

    /// <summary>Saves the backtrackable state (Lean's <c>saveState</c>); O(1).</summary>
    public SavedState SaveState() => new(MCtx, Postponed);

    /// <summary>Restores a saved state (Lean's <c>SavedState.restore</c>).</summary>
    public void Restore(SavedState saved)
    {
        ArgumentNullException.ThrowIfNull(saved);
        MCtx = saved.MCtx;
        Postponed = saved.Postponed;
    }

    /// <summary>Runs <paramref name="k"/> in the scope <c>f(Context)</c>, then restores the scope (Lean's <c>withReader</c>).</summary>
    public T WithReader<T>(Func<MetaContext, MetaContext> f, Func<T> k)
    {
        ArgumentNullException.ThrowIfNull(f);
        ArgumentNullException.ThrowIfNull(k);
        var saved = Context;
        Context = f(saved);
        try
        {
            return k();
        }
        finally
        {
            Context = saved;
        }
    }

    /// <summary>Runs <paramref name="k"/> with the configuration <c>f(Config)</c> (Lean's <c>withConfig</c>).</summary>
    public T WithConfig<T>(Func<MetaConfig, MetaConfig> f, Func<T> k)
    {
        ArgumentNullException.ThrowIfNull(f);
        return WithReader(c => c with { Config = f(c.Config) }, k);
    }

    /// <summary>Runs <paramref name="k"/> letting unification assign goals (Lean's <c>withAssignableSyntheticOpaque</c>).</summary>
    public T WithAssignableSyntheticOpaque<T>(Func<T> k) => WithConfig(c => c with { AssignSyntheticOpaque = true }, k);

    /// <summary>Creates a metavariable in an explicit local context (Lean's <c>mkFreshExprMVarAt</c>).</summary>
    public MVarExpr MkFreshExprMVarAt(
        LocalContext lctx,
        ImmutableArray<LocalInstance> localInsts,
        Expr type,
        MetavarKind kind = MetavarKind.Natural,
        Name? userName = null,
        int numScopeArgs = 0)
    {
        var mvarId = MkFreshMVarId();
        MCtx = MCtx.AddExprMVarDecl(mvarId, userName ?? Name.Anonymous, lctx, localInsts, type, kind, numScopeArgs);
        return Expr.MVar(mvarId);
    }

    /// <summary>Creates a universe metavariable (Lean's <c>mkFreshLevelMVar</c>).</summary>
    public Level MkFreshLevelMVar()
    {
        var mvarId = MkFreshLMVarId();
        MCtx = MCtx.AddLevelMVarDecl(mvarId);
        return Level.MVar(mvarId);
    }

    /// <summary>
    /// Creates a metavariable in the current local context (Lean's <c>mkFreshExprMVar</c>). With no
    /// type, its type is itself a fresh metavariable <c>?α : Sort ?u</c>.
    /// </summary>
    public MVarExpr MkFreshExprMVar(Expr? type, MetavarKind kind = MetavarKind.Natural, Name? userName = null)
    {
        type ??= MkFreshExprMVarAt(LCtx, LocalInstances, Expr.Sort(MkFreshLevelMVar()));
        return MkFreshExprMVarAt(LCtx, LocalInstances, type, kind, userName);
    }

    /// <summary>Creates a type metavariable <c>?α : Sort ?u</c> (Lean's <c>mkFreshTypeMVar</c>).</summary>
    public MVarExpr MkFreshTypeMVar(MetavarKind kind = MetavarKind.Natural, Name? userName = null) =>
        MkFreshExprMVar(Expr.Sort(MkFreshLevelMVar()), kind, userName);

    /// <summary><paramref name="num"/> fresh universe metavariables (Lean's <c>mkFreshLevelMVars</c>).</summary>
    public EquatableArray<Level> MkFreshLevelMVars(int num)
    {
        var levels = new Level[num];
        for (int i = 0; i < num; i++)
        {
            levels[i] = MkFreshLevelMVar();
        }
        return levels;
    }

    /// <summary>The constant <paramref name="declName"/> at fresh universe metavariables, e.g. <c>@congrArg.{?u, ?v}</c> (Lean's <c>mkConstWithFreshMVarLevels</c>).</summary>
    /// <exception cref="MetaException">The constant is unknown.</exception>
    public ConstExpr MkConstWithFreshMVarLevels(Name declName)
    {
        var info = GetConstInfo(declName);
        return Expr.Const(declName, MkFreshLevelMVars(info.LevelParams.Count));
    }

    /// <summary>The declaration of a constant (Lean's <c>getConstInfo</c>).</summary>
    /// <exception cref="MetaException">The constant is unknown.</exception>
    public ConstantInfo GetConstInfo(Name declName) =>
        Env.Find(declName) ?? throw new MetaException($"unknown constant '{declName}'");

    /// <summary>The declaration of <paramref name="mvarId"/>.</summary>
    /// <exception cref="MetaException">It is not declared.</exception>
    public MetavarDecl GetMVarDecl(MVarId mvarId) => MCtx.GetDecl(mvarId);

    /// <summary>The kind of <paramref name="mvarId"/>.</summary>
    public MetavarKind GetMVarKind(MVarId mvarId) => GetMVarDecl(mvarId).Kind;

    /// <summary>Whether <paramref name="e"/> is a synthetic or synthetic-opaque metavariable (Lean's <c>isSyntheticMVar</c>).</summary>
    public bool IsSyntheticMVar(Expr e) => e is MVarExpr m && GetMVarKind(m.Id) is MetavarKind.Synthetic or MetavarKind.SyntheticOpaque;

    /// <summary>Sets the kind of <paramref name="mvarId"/>.</summary>
    public void SetMVarKind(MVarId mvarId, MetavarKind kind) => MCtx = MCtx.SetMVarKind(mvarId, kind);

    /// <summary>Sets the type of <paramref name="mvarId"/> (to a definitionally equal one).</summary>
    public void SetMVarType(MVarId mvarId, Expr type) => MCtx = MCtx.SetMVarType(mvarId, type);

    /// <summary>Sets the goal tag of <paramref name="mvarId"/>.</summary>
    public void SetMVarUserName(MVarId mvarId, Name userName) => MCtx = MCtx.SetMVarUserName(mvarId, userName);

    /// <summary>Whether <paramref name="mvarId"/> was created at another depth, so cannot be assigned here (Lean's <c>MVarId.isReadOnly</c>).</summary>
    public bool IsReadOnly(MVarId mvarId) => GetMVarDecl(mvarId).Depth != MCtx.Depth;

    /// <summary>
    /// Whether unification must leave <paramref name="mvarId"/> alone: it is read-only, or a goal
    /// while <see cref="MetaConfig.AssignSyntheticOpaque"/> is off (Lean's <c>isReadOnlyOrSyntheticOpaque</c>).
    /// </summary>
    public bool IsReadOnlyOrSyntheticOpaque(MVarId mvarId)
    {
        var decl = GetMVarDecl(mvarId);
        if (decl.Depth != MCtx.Depth)
        {
            return true;
        }
        return decl.Kind == MetavarKind.SyntheticOpaque && !Config.AssignSyntheticOpaque;
    }

    /// <summary>Whether the universe metavariable <paramref name="mvarId"/> is read-only here (Lean's <c>LMVarId.isReadOnly</c>).</summary>
    public bool IsReadOnly(LMVarId mvarId) => MCtx.GetLevelDecl(mvarId).Depth < MCtx.LevelAssignDepth;

    /// <summary>Whether <paramref name="mvarId"/> is assigned.</summary>
    public bool IsAssigned(MVarId mvarId) => MCtx.IsAssigned(mvarId);

    /// <summary>Whether <paramref name="mvarId"/> is delayed-assigned.</summary>
    public bool IsDelayedAssigned(MVarId mvarId) => MCtx.IsDelayedAssigned(mvarId);

    /// <summary>
    /// Records <c>?mvarId := val</c> with no checks (Lean's <c>MVarId.assign</c>); see
    /// <see cref="CheckedAssign"/>. With <see cref="DebugCheckAssignments"/>, a ground value is first
    /// checked by the kernel against the metavariable's type.
    /// </summary>
    public void Assign(MVarId mvarId, Expr val)
    {
        if (DebugCheckAssignments)
        {
            DebugCheckAssignment(mvarId, val);
        }
        MCtx = MCtx.Assign(mvarId, val);
    }

    /// <summary>Records <c>?mvarId := val</c> for a universe metavariable, with no checks (Lean's <c>assignLevelMVar</c>).</summary>
    public void AssignLevelMVar(LMVarId mvarId, Level val) => MCtx = MCtx.AssignLevelMVar(mvarId, val);

    /// <summary>The declaration of <paramref name="fvarId"/> in the current context, or null.</summary>
    public LocalDecl? FindLocalDecl(FVarId fvarId) => LCtx.Find(fvarId);

    /// <summary>The declaration of <paramref name="fvarId"/> in the current context.</summary>
    /// <exception cref="MetaException">It is not declared.</exception>
    public LocalDecl GetLocalDecl(FVarId fvarId) => LCtx.Get(fvarId);

    /// <summary>The declaration of the free variable <paramref name="fvar"/> (Lean's <c>getFVarLocalDecl</c>).</summary>
    public LocalDecl GetFVarLocalDecl(Expr fvar) => LCtx.GetFVar(fvar);

    /// <summary>The last declaration named <paramref name="userName"/> (Lean's <c>getLocalDeclFromUserName</c>).</summary>
    /// <exception cref="MetaException">There is none.</exception>
    public LocalDecl GetLocalDeclFromUserName(Name userName) =>
        LCtx.FindFromUserName(userName) ?? throw new MetaException($"unknown local declaration '{userName}'");

    /// <summary>Whether a later declaration depends on <paramref name="fvarId"/> (Lean's <c>FVarId.hasForwardDeps</c>).</summary>
    public bool HasForwardDeps(FVarId fvarId)
    {
        var decl = GetLocalDecl(fvarId);
        return LCtx.DeclsFrom(decl.Index + 1).Any(other => this.LocalDeclDependsOn(other, fvarId));
    }

    private T LiftMkBinding<T>(Func<MkBinding, T> x, bool preserveOrder = false, BinderInfo binderInfoForMVars = BinderInfo.Implicit, ImmutableHashSet<MVarId>? mvarIdsToAbstract = null)
    {
        var m = new MkBinding(MCtx, _ngen, _nextMacroScope, Budget, preserveOrder, binderInfoForMVars, mvarIdsToAbstract);
        try
        {
            return x(m);
        }
        finally
        {
            // Like liftMkBindingM, keep the context even when binder construction fails.
            MCtx = m.MCtx;
            _nextMacroScope = m.NextMacroScope;
        }
    }

    /// <summary>
    /// Like <see cref="ExprExtensions.AbstractRange"/> over the first <paramref name="n"/> of
    /// <paramref name="xs"/>, but correct when <paramref name="e"/> has metavariables whose context
    /// contains them (Lean's <c>abstractRangeM</c>).
    /// </summary>
    public Expr AbstractRangeM(Expr e, int n, IReadOnlyList<Expr> xs) => LiftMkBinding(m => m.AbstractRange(xs, n, e));

    /// <summary>Replaces the free or meta variables <paramref name="xs"/> by bound variables, handling metavariables (Lean's <c>abstractM</c>).</summary>
    public Expr AbstractM(Expr e, IReadOnlyList<Expr> xs) => AbstractRangeM(e, xs.Count, xs);

    /// <summary>Replaces <paramref name="fvars"/> by <paramref name="vs"/> in <paramref name="e"/>, handling metavariables (Lean's <c>replaceFVarsM</c>).</summary>
    public Expr ReplaceFVarsM(Expr e, IReadOnlyList<Expr> fvars, IReadOnlyList<Expr> vs) => AbstractM(e, fvars).InstantiateRev(vs);

    /// <summary>
    /// <paramref name="toRevert"/> and the declarations of the current context that depend on
    /// them, in context order (Lean's <c>collectForwardDeps</c>).
    /// </summary>
    public Expr[] CollectForwardDeps(IReadOnlyList<Expr> toRevert, bool preserveOrder, bool generalizeNondepLet = true) =>
        LiftMkBinding(m => m.CollectForwardDeps(LCtx, toRevert, generalizeNondepLet), preserveOrder);

    /// <summary>
    /// Eliminates the dependencies of <paramref name="e"/>'s metavariables on <paramref name="xs"/>
    /// (Lean's <c>elimMVarDeps</c>); see <see cref="MkBinding"/>.
    /// </summary>
    public Expr ElimMVarDeps(IReadOnlyList<Expr> xs, Expr e, bool preserveOrder = false)
    {
        ArgumentNullException.ThrowIfNull(xs);
        return xs.Count == 0 ? e : LiftMkBinding(m => m.ElimMVarDeps(xs, e), preserveOrder);
    }

    /// <summary>
    /// Low level: reverts <paramref name="xs"/> and their forward dependencies from
    /// <paramref name="mvarId"/>'s context, returning the replacement term and the reverted
    /// variables (Lean's <c>MetavarContext.revert</c>).
    /// </summary>
    public (Expr Result, Expr[] Reverted) RevertCore(IReadOnlyList<Expr> xs, MVarId mvarId, bool preserveOrder) =>
        LiftMkBinding(m => m.Revert(xs, mvarId), preserveOrder);

    /// <summary>
    /// <c>∀ xs, e</c> for free or meta variables <paramref name="xs"/>, correct when
    /// <paramref name="e"/> has metavariables (Lean's <c>mkForallFVars</c>).
    /// </summary>
    public Expr MkForallFVars(IReadOnlyList<Expr> xs, Expr e, bool usedOnly = false, bool usedLetOnly = true, bool generalizeNondepLet = true, BinderInfo binderInfoForMVars = BinderInfo.Implicit)
    {
        ArgumentNullException.ThrowIfNull(xs);
        return xs.Count == 0 ? e : MkBindingM(false, xs, e, usedOnly, usedLetOnly, etaReduce: false, generalizeNondepLet, binderInfoForMVars);
    }

    /// <summary>
    /// <c>fun xs => e</c> for free or meta variables <paramref name="xs"/>. A goal <c>?g</c> in
    /// <paramref name="e"/> whose context contains one of them becomes <c>?n xs</c> with the delayed
    /// assignment <c>?n #[xs] := ?g</c> (Lean's <c>mkLambdaFVars</c>; KTD3).
    /// </summary>
    public Expr MkLambdaFVars(IReadOnlyList<Expr> xs, Expr e, bool usedOnly = false, bool usedLetOnly = true, bool etaReduce = false, bool generalizeNondepLet = true, BinderInfo binderInfoForMVars = BinderInfo.Implicit)
    {
        ArgumentNullException.ThrowIfNull(xs);
        return xs.Count == 0 ? e : MkBindingM(true, xs, e, usedOnly, usedLetOnly, etaReduce, generalizeNondepLet, binderInfoForMVars);
    }

    /// <summary><see cref="MkLambdaFVars"/> for let variables (Lean's <c>mkLetFVars</c>).</summary>
    public Expr MkLetFVars(IReadOnlyList<Expr> xs, Expr e, bool usedLetOnly = true, bool generalizeNondepLet = true, BinderInfo binderInfoForMVars = BinderInfo.Implicit) =>
        MkLambdaFVars(xs, e, usedLetOnly: usedLetOnly, generalizeNondepLet: generalizeNondepLet, binderInfoForMVars: binderInfoForMVars);

    private Expr MkBindingM(bool isLambda, IReadOnlyList<Expr> xs, Expr e, bool usedOnly, bool usedLetOnly, bool etaReduce, bool generalizeNondepLet, BinderInfo binderInfoForMVars)
    {
        var mvarIdsToAbstract = xs.OfType<MVarExpr>().Select(m => m.Id).ToImmutableHashSet();
        var lctx = LCtx;
        return LiftMkBinding(
            m => m.MkBindingCore(isLambda, lctx, xs, e, usedOnly, usedLetOnly, etaReduce, generalizeNondepLet),
            preserveOrder: false,
            binderInfoForMVars,
            mvarIdsToAbstract);
    }

    /// <summary>
    /// Runs <paramref name="k"/> with a fresh hypothesis <c>(name : type)</c> added to the local
    /// context, then removes it (Lean's <c>withLocalDecl</c>).
    /// </summary>
    public T WithLocalDecl<T>(Name name, BinderInfo bi, Expr type, Func<FVarExpr, T> k, LocalDeclKind kind = LocalDeclKind.Default)
    {
        ArgumentNullException.ThrowIfNull(k);
        var fvarId = MkFreshFVarId();
        var fvar = Expr.FVar(fvarId);
        return WithReader(c => c with { LCtx = c.LCtx.MkLocalDecl(fvarId, name, type, bi, kind) }, () => k(fvar));
    }

    /// <summary><see cref="WithLocalDecl{T}"/> with the default binder annotation (Lean's <c>withLocalDeclD</c>).</summary>
    public T WithLocalDeclD<T>(Name name, Expr type, Func<FVarExpr, T> k) => WithLocalDecl(name, BinderInfo.Default, type, k);

    /// <summary>
    /// Adds hypotheses one after another, each type built from the variables before it, and runs
    /// <paramref name="k"/> on all of them (Lean's <c>withLocalDecls</c>).
    /// </summary>
    public T WithLocalDecls<T>(IReadOnlyList<(Name Name, BinderInfo Info, Func<IReadOnlyList<Expr>, Expr> Type)> declInfos, Func<IReadOnlyList<Expr>, T> k, LocalDeclKind kind = LocalDeclKind.Default)
    {
        ArgumentNullException.ThrowIfNull(declInfos);
        ArgumentNullException.ThrowIfNull(k);
        return Loop([]);

        T Loop(List<Expr> acc)
        {
            if (acc.Count >= declInfos.Count)
            {
                return k(acc);
            }
            var (name, bi, typeCtor) = declInfos[acc.Count];
            return WithLocalDecl(name, bi, typeCtor(acc), x => Loop([.. acc, x]), kind);
        }
    }

    /// <summary>
    /// Runs <paramref name="k"/> with a fresh local definition <c>(name : type := val)</c>, then
    /// removes it (Lean's <c>withLetDecl</c>).
    /// </summary>
    public T WithLetDecl<T>(Name name, Expr type, Expr val, Func<FVarExpr, T> k, bool nondep = false, LocalDeclKind kind = LocalDeclKind.Default)
    {
        ArgumentNullException.ThrowIfNull(k);
        var fvarId = MkFreshFVarId();
        var fvar = Expr.FVar(fvarId);
        return WithReader(c => c with { LCtx = c.LCtx.MkLetDecl(fvarId, name, type, val, nondep, kind) }, () => k(fvar));
    }

    /// <summary>Runs <paramref name="k"/> in another local context (Lean's <c>withLCtx</c>).</summary>
    public T WithLCtx<T>(LocalContext lctx, ImmutableArray<LocalInstance> localInsts, Func<T> k) =>
        WithReader(c => c with { LCtx = lctx, LocalInstances = localInsts }, k);

    /// <summary>Runs <paramref name="k"/> in <paramref name="mvarId"/>'s local context (Lean's <c>MVarId.withContext</c>).</summary>
    public T WithContext<T>(MVarId mvarId, Func<T> k)
    {
        var decl = GetMVarDecl(mvarId);
        return WithLCtx(decl.LCtx, decl.LocalInstances, k);
    }

    /// <summary>
    /// Runs <paramref name="k"/> one metavariable-context depth deeper, so metavariables created
    /// before it are read-only (and universe ones too unless <paramref name="allowLevelAssignments"/>),
    /// then restores the metavariable context as it was (Lean's <c>withNewMCtxDepth</c>).
    /// </summary>
    /// <remarks>
    /// Lean 4.35.0 restores the whole saved context afterwards, so assignments made inside do not
    /// survive; a caller that needs a result instantiates it before leaving.
    /// </remarks>
    public T WithNewMCtxDepth<T>(Func<T> k, bool allowLevelAssignments = false)
    {
        ArgumentNullException.ThrowIfNull(k);
        var saved = MCtx;
        MCtx = MCtx.IncDepth(allowLevelAssignments);
        try
        {
            return k();
        }
        finally
        {
            MCtx = saved;
        }
    }

    /// <summary>Runs <paramref name="k"/> with <paramref name="mctx"/>, then restores the current context (Lean's <c>withMCtx</c>).</summary>
    public T WithMCtx<T>(MetavarContext mctx, Func<T> k)
    {
        ArgumentNullException.ThrowIfNull(mctx);
        ArgumentNullException.ThrowIfNull(k);
        var saved = MCtx;
        MCtx = mctx;
        try
        {
            return k();
        }
        finally
        {
            MCtx = saved;
        }
    }

    /// <summary>Runs <paramref name="k"/> and then restores the metavariable context (Lean's <c>withoutModifyingMCtx</c>).</summary>
    public T WithoutModifyingMCtx<T>(Func<T> k) => WithMCtx(MCtx, k);

    /// <summary>
    /// For <paramref name="type"/> of the form <c>∀ xs, A</c>, runs <paramref name="k"/> on fresh
    /// free variables for <c>xs</c> and the instantiated <c>A</c> (Lean's <c>forallTelescope</c>).
    /// It does not reduce <c>A</c> to find more binders.
    /// </summary>
    public T ForallTelescope<T>(Expr type, Func<Expr[], Expr, T> k)
    {
        ArgumentNullException.ThrowIfNull(type);
        ArgumentNullException.ThrowIfNull(k);
        var lctx = LCtx;
        var fvars = new List<Expr>();
        while (type is ForallExpr f)
        {
            Budget.Tick();
            var d = f.BinderType.InstantiateRevRange(0, fvars.Count, fvars);
            var fvarId = MkFreshFVarId();
            lctx = lctx.MkLocalDecl(fvarId, f.BinderName, d, f.BinderInfo);
            fvars.Add(Expr.FVar(fvarId));
            type = f.Body;
        }
        var body = type.InstantiateRevRange(0, fvars.Count, fvars);
        Expr[] xs = [.. fvars];
        return WithReader(c => c with { LCtx = lctx }, () => k(xs, body));
    }

    private T LambdaTelescopeImp<T>(Expr e, bool consumeLambda, bool consumeLet, bool preserveNondepLet, bool nondepLetOnly, int? maxFVars, Func<Expr[], Expr, T> k)
    {
        ArgumentNullException.ThrowIfNull(e);
        ArgumentNullException.ThrowIfNull(k);
        var lctx = LCtx;
        var fvars = new List<Expr>();
        while (maxFVars is not { } max || fvars.Count < max)
        {
            if (consumeLambda && e is LamExpr lam)
            {
                Budget.Tick();
                var d = lam.BinderType.InstantiateRevRange(0, fvars.Count, fvars);
                var fvarId = MkFreshFVarId();
                lctx = lctx.MkLocalDecl(fvarId, lam.BinderName, d, lam.BinderInfo);
                fvars.Add(Expr.FVar(fvarId));
                e = lam.Body;
            }
            else if (consumeLet && e is LetExpr let && (let.NonDependent || !nondepLetOnly))
            {
                Budget.Tick();
                var t = let.BinderType.InstantiateRevRange(0, fvars.Count, fvars);
                var v = let.Value.InstantiateRevRange(0, fvars.Count, fvars);
                var fvarId = MkFreshFVarId();
                lctx = lctx.MkLetDecl(fvarId, let.BinderName, t, v, let.NonDependent && preserveNondepLet);
                fvars.Add(Expr.FVar(fvarId));
                e = let.Body;
            }
            else
            {
                break;
            }
        }
        var body = e.InstantiateRevRange(0, fvars.Count, fvars);
        Expr[] xs = [.. fvars];
        return WithReader(c => c with { LCtx = lctx }, () => k(xs, body));
    }

    /// <summary>For <c>fun xs => b</c>, runs <paramref name="k"/> on fresh free variables and the instantiated body (Lean's <c>lambdaTelescope</c>).</summary>
    public T LambdaTelescope<T>(Expr e, Func<Expr[], Expr, T> k) =>
        LambdaTelescopeImp(e, consumeLambda: true, consumeLet: false, preserveNondepLet: true, nondepLetOnly: false, maxFVars: null, k);

    /// <summary>Like <see cref="LambdaTelescope{T}"/>, consuming lets too (Lean's <c>lambdaLetTelescope</c>).</summary>
    public T LambdaLetTelescope<T>(Expr e, Func<Expr[], Expr, T> k, bool preserveNondepLet = true) =>
        LambdaTelescopeImp(e, consumeLambda: true, consumeLet: true, preserveNondepLet, nondepLetOnly: false, maxFVars: null, k);

    /// <summary>Like <see cref="LambdaTelescope{T}"/>, consuming at most <paramref name="maxFVars"/> lambdas (Lean's <c>lambdaBoundedTelescope</c>).</summary>
    public T LambdaBoundedTelescope<T>(Expr e, int maxFVars, Func<Expr[], Expr, T> k) =>
        LambdaTelescopeImp(e, consumeLambda: true, consumeLet: false, preserveNondepLet: true, nondepLetOnly: false, maxFVars, k);

    /// <summary>For <c>let xs := vs; b</c>, runs <paramref name="k"/> on fresh let variables and the body (Lean's <c>letTelescope</c>).</summary>
    public T LetTelescope<T>(Expr e, Func<Expr[], Expr, T> k, bool preserveNondepLet = true, bool nondepLetOnly = false) =>
        LambdaTelescopeImp(e, consumeLambda: false, consumeLet: true, preserveNondepLet, nondepLetOnly, maxFVars: null, k);

    /// <summary>
    /// For <c>∀ xs, A</c>, creates a metavariable for each binder (synthetic for instance-implicit
    /// ones, <paramref name="kind"/> otherwise) and returns them, their binder annotations and the
    /// instantiated <c>A</c> (Lean's <c>forallMetaTelescope</c>). It does not reduce <c>A</c>.
    /// </summary>
    public (Expr[] MVars, BinderInfo[] BinderInfos, Expr Type) ForallMetaTelescope(Expr e, MetavarKind kind = MetavarKind.Natural)
    {
        ArgumentNullException.ThrowIfNull(e);
        var mvars = new List<Expr>();
        var bis = new List<BinderInfo>();
        while (e is ForallExpr f)
        {
            Budget.Tick();
            var d = f.BinderType.InstantiateRevRange(0, mvars.Count, mvars);
            var k = f.BinderInfo == BinderInfo.InstImplicit ? MetavarKind.Synthetic : kind;
            mvars.Add(MkFreshExprMVar(d, k, f.BinderName));
            bis.Add(f.BinderInfo);
            e = f.Body;
        }
        return ([.. mvars], [.. bis], e.InstantiateRevRange(0, mvars.Count, mvars));
    }

    /// <summary>
    /// For <c>fun xs => b</c>, creates a natural metavariable for each of at most
    /// <paramref name="maxMVars"/> binders and returns them, their annotations and the instantiated
    /// body (Lean's <c>lambdaMetaTelescope</c>).
    /// </summary>
    public (Expr[] MVars, BinderInfo[] BinderInfos, Expr Body) LambdaMetaTelescope(Expr e, int? maxMVars = null)
    {
        ArgumentNullException.ThrowIfNull(e);
        var mvars = new List<Expr>();
        var bis = new List<BinderInfo>();
        while ((maxMVars is not { } max || mvars.Count < max) && e is LamExpr lam)
        {
            Budget.Tick();
            var d = lam.BinderType.InstantiateRevRange(0, mvars.Count, mvars);
            mvars.Add(MkFreshExprMVar(d));
            bis.Add(lam.BinderInfo);
            e = lam.Body;
        }
        return ([.. mvars], [.. bis], e.InstantiateRevRange(0, mvars.Count, mvars));
    }
}
