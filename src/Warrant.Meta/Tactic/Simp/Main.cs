using System.Collections.Immutable;
using System.Runtime.CompilerServices;
using Warrant.Cic;
using Warrant.Kernel;

namespace Warrant.Meta;

/// <summary>
/// What one <c>simp</c> call rewrites with (Lean's <c>Simp.Context</c>): the configuration, the theorem sets (tried in
/// order), and the <c>@[congr]</c> lemmas by function.
/// </summary>
/// <param name="Config">The configuration.</param>
/// <param name="Theorems">The theorem sets.</param>
/// <param name="CongrTheorems">The congruence lemmas, by the function they are about, highest priority first.</param>
public sealed record SimpContext(SimpConfig Config, ImmutableList<SimpTheorems> Theorems, IReadOnlyDictionary<Name, ImmutableArray<CongrEntry>> CongrTheorems)
{
    private static readonly ConditionalWeakTable<Sidecar, IReadOnlyDictionary<Name, ImmutableArray<CongrEntry>>> CongrCache = new();

    /// <summary>
    /// The <c>@[congr]</c> lemmas of <paramref name="sidecar"/>, by function, highest priority first; grouped once per
    /// base sidecar (<see cref="Sidecar.Base"/>), whose entries every fork shares and which never change after loading.
    /// </summary>
    public static IReadOnlyDictionary<Name, ImmutableArray<CongrEntry>> CongrTheoremsOf(Sidecar sidecar)
    {
        ArgumentNullException.ThrowIfNull(sidecar);
        return CongrCache.GetValue(sidecar.Base, static s => s.CongrEntries
            .GroupBy(c => c.Function)
            .ToDictionary(g => g.Key, g => g.OrderByDescending(c => c.Priority).ToImmutableArray()));
    }
}

/// <summary>
/// The simplifier: a port of Lean 4.35.0's <c>Simp.main</c> (Lean/Meta/Tactic/Simp/Main.lean, Rewrite.lean, Types.lean;
/// plan KTD11, docs/m5a/05). One instance is one run (Lean's <c>SimpM</c>), with its cache and step count.
/// </summary>
/// <remarks>
/// <para>
/// Ported: the main loop with <c>pre</c> and <c>post</c> procedures, congruence through applications (<c>congrArg</c>,
/// <c>congrFun</c>, <c>congr</c>) and <c>@[congr]</c> lemmas, implications with <c>contextual</c>, foralls over
/// propositions, lambdas (<c>funext</c>), projections, rewriting with argument synthesis and discharge,
/// <c>decide := true</c>, and the structural simprocs <c>reduceIte</c> and <c>reduceDIte</c>.
/// </para>
/// <para>
/// Not ported (chapter 5): the ground arithmetic simprocs, <c>dsimp</c> (a subterm simp may only change by definition
/// is left as it is), automatically generated congruence lemmas (<c>mkCongrSimp?</c>; such an argument is likewise left
/// as it is), matcher equations, permutation lemmas and loop protection. Each only makes simp weaker, never unsound:
/// the kernel checks the proof.
/// </para>
/// </remarks>
public sealed partial class Simplifier
{
    private readonly MetaM m;
    private ImmutableList<SimpTheorems> _theorems;
    private Dictionary<Expr, SimpResult> _cache = [];
    private int _numSteps;
    private int _dischargeDepth;
    private readonly int _lctxInitSize;

    /// <summary>
    /// The one theorem <c>unfold</c> rewrites with, when this run is Lean's <c>unfold</c> rather than <c>simp</c> (its
    /// <c>Simp.Methods</c>: that theorem as <c>pre</c>, the default <c>post</c> that stops); null for <c>simp</c>.
    /// </summary>
    private readonly SimpTheorem? _unfold;

    /// <summary>Creates a run over <paramref name="meta"/>'s current local context.</summary>
    public Simplifier(MetaM meta, SimpContext context)
    {
        m = meta ?? throw new ArgumentNullException(nameof(meta));
        Context = context ?? throw new ArgumentNullException(nameof(context));
        _theorems = context.Theorems;
        _lctxInitSize = meta.LCtx.NumIndices;
    }

    /// <summary>A run of Lean's <c>unfold</c> with the equation lemma <paramref name="unfold"/> (Lean/Meta/Tactic/Unfold.lean 19-30).</summary>
    internal Simplifier(MetaM meta, SimpContext context, SimpTheorem unfold)
        : this(meta, context) => _unfold = unfold;

    /// <summary>The context.</summary>
    public SimpContext Context { get; }

    private SimpConfig Config => Context.Config;

    /// <summary>
    /// Simplifies <paramref name="e"/> (Lean's <c>Simp.main</c>), at reducible transparency.
    /// </summary>
    /// <exception cref="MetaException">Simp ran out of steps.</exception>
    public SimpResult Run(Expr e)
    {
        ArgumentNullException.ThrowIfNull(e);
        return m.WithReducible(() => Simp(e));
    }

    // Lean's withSimpMetaConfig: the configuration for isDefEq and reduction.
    private T WithMetaConfig<T>(Func<T> k) => m.WithConfig(
        c => c with
        {
            Beta = Config.Beta,
            Iota = Config.Iota,
            Zeta = Config.Zeta,
            ZetaUnused = Config.ZetaUnused,
            ZetaDelta = false,
            Proj = Config.Proj ? ProjReductionKind.YesWithDelta : ProjReductionKind.No,
            Transparency = TransparencyMode.Reducible,
        },
        k);

    // Lean's withSimpIndexConfig: the configuration for discrimination-tree lookups.
    private T WithIndexConfig<T>(Func<T> k) => m.WithConfig(
        c => c with
        {
            Beta = Config.Beta,
            Iota = Config.Iota,
            Zeta = Config.Zeta,
            ZetaUnused = Config.ZetaUnused,
            ZetaDelta = false,
            Proj = ProjReductionKind.No,
            Transparency = TransparencyMode.Reducible,
        },
        k);

    /// <summary>Lean's <c>simp</c> (<c>simpImpl</c>): proofs are left alone.</summary>
    internal SimpResult Simp(Expr e)
    {
        if (m.IsProof(e))
        {
            return new(e);
        }
        return SimpLoop(e);
    }

    private SimpResult SimpLoop(Expr e)
    {
        if (Config.Memoize && _cache.TryGetValue(e, out var cached))
        {
            return cached;
        }
        if (_numSteps > Config.MaxSteps)
        {
            throw new MetaException("`simp` failed: maximum number of steps exceeded");
        }
        m.Budget.Tick();
        _numSteps++;
        var step = Pre(e);
        return step.Kind switch
        {
            SimpStepKind.Done => CacheResult(e, step.Result!),
            SimpStepKind.Visit => CacheResult(e, step.Result!.MkEqTrans(m, SimpLoop(step.Result!.Expr))),
            _ => VisitPreContinue(e, step.Result ?? new SimpResult(e)),
        };
    }

    private SimpResult VisitPreContinue(Expr e, SimpResult r)
    {
        var eNew = ReduceStep(r.Expr);
        if (eNew != r.Expr)
        {
            r = r with { Expr = eNew };
            return CacheResult(e, r.MkEqTrans(m, SimpLoop(eNew)));
        }
        r = r.MkEqTrans(m, SimpStepCore(r.Expr));
        var post = Post(r.Expr);
        if (post.Kind == SimpStepKind.Done)
        {
            return CacheResult(e, r.MkEqTrans(m, post.Result!));
        }
        if (post.Result is { } r2)
        {
            r = r.MkEqTrans(m, r2);
        }
        if (!Config.SinglePass && e != r.Expr)
        {
            r = r.MkEqTrans(m, SimpLoop(r.Expr));
        }
        return CacheResult(e, r);
    }

    private SimpResult CacheResult(Expr e, SimpResult r)
    {
        if (Config.Memoize)
        {
            _cache[e] = r;
        }
        return r;
    }

    // Lean's simpStep: one step by the term's shape.
    private SimpResult SimpStepCore(Expr e) => e switch
    {
        MDataExpr md => SimpMData(md),
        ProjExpr => SimpProj(e),
        AppExpr => SimpApp(e),
        LamExpr => SimpLambda(e),
        ForallExpr => SimpForall(e),
        LetExpr => new(e), // only reached with zeta off; dsimp is not ported
        ConstExpr => new(Reduce(e)),
        MVarExpr => new(m.InstantiateMVars(e)),
        FVarExpr => new(ReduceFVar(e)),
        _ => new(e),
    };

    private SimpResult SimpMData(MDataExpr md)
    {
        var r = Simp(md.Expr);
        return r with { Expr = md.UpdateMData(r.Expr) };
    }

    // Lean's dsimp: not ported; a subterm simp may only change by definition is left as it is (chapter 5).
    private static Expr Dsimp(Expr e) => e;

    private static bool IsOfNatNatLit(Expr e) =>
        e.IsAppOf(MetaNames.OfNatOfNat) && e.GetAppNumArgs() >= 3 && e.GetAppArgs()[1] is NatLitExpr;

    private Expr ReduceFVar(Expr e)
    {
        var decl = m.GetFVarLocalDecl(e);
        return decl.IsImplementationDetail && decl is LDecl let ? let.Value : e;
    }

    // Lean's reduceProjFn?: a projection function applied to a constructor (class projections only then).
    private Expr? ReduceProjFn(Expr e)
    {
        if (e.GetAppFn() is not ConstExpr c || m.GetProjectionFnInfo(c.Name) is not { } projInfo)
        {
            return null;
        }
        if (projInfo.FromClass)
        {
            var args = e.GetAppArgs();
            if (args.Length <= projInfo.NumParams || !m.IsConstructorApp(args[projInfo.NumParams]))
            {
                return null;
            }
            return ReduceProjCont(UnfoldDefinitionAny(e));
        }
        return ReduceProjCont(m.UnfoldDefinition(e));

        Expr? ReduceProjCont(Expr? unfolded) =>
            unfolded is not null && WithMetaConfig(() => m.ReduceProj(unfolded.GetAppFn())) is { } f
                ? ExprExtensions.MkAppN(f, unfolded.GetAppArgs())
                : null;
    }

    // Lean's unfoldDefinitionAny?: never an irreducible definition.
    private Expr? UnfoldDefinitionAny(Expr e) =>
        e.GetAppFn() is ConstExpr c && m.Attributes.GetReducibilityStatus(c.Name) == ReducibilityStatus.Irreducible
            ? null
            : m.UnfoldDefinition(e, ignoreTransparency: true);

    // Lean's reduceStep.
    private Expr ReduceStep(Expr e)
    {
        var f = e.GetAppFn();
        if (f is MVarExpr)
        {
            return m.InstantiateMVars(e);
        }
        return WithMetaConfig(() =>
        {
            if (Config.Beta && f.IsHeadBetaTargetFn(false))
            {
                return f.BetaRev(e.GetAppRevArgs());
            }
            if (Config.Proj)
            {
                if (m.ReduceProj(e) is { } p)
                {
                    return p;
                }
                if (ReduceProjFn(e) is { } pf)
                {
                    return pf;
                }
            }
            if (Config.Iota && m.ReduceRecMatcher(e) is { } r)
            {
                return r;
            }
            if (e is LetExpr let)
            {
                if (Config.Zeta)
                {
                    return MetaM.ExpandLet(let.Body, [let.Value]);
                }
                if (Config.ZetaUnused && !let.Body.HasLooseBVars)
                {
                    return MetaM.ConsumeUnusedLet(let.Body);
                }
            }
            return FoldRawNatLit(e);
        });
    }

    // Lean's foldRawNatLit: an orphan raw literal n becomes OfNat.ofNat n.
    private static Expr FoldRawNatLit(Expr e) => e is NatLitExpr n ? MetaNames.MkNatLit(n.Value) : e;

    private Expr Reduce(Expr e)
    {
        while (true)
        {
            m.Budget.Tick();
            var eNew = ReduceStep(e);
            if (eNew == e)
            {
                return e;
            }
            e = eNew;
        }
    }

    /// <summary>
    /// Lean's <c>withNewLemmas</c>: with <c>contextual</c>, the proofs among <paramref name="xs"/> become rewrite rules
    /// for <paramref name="k"/>, with a fresh cache.
    /// </summary>
    private T WithNewLemmas<T>(IReadOnlyList<Expr> xs, Func<T> k)
    {
        if (!Config.Contextual)
        {
            return k();
        }
        var savedCache = _cache;
        var savedTheorems = _theorems;
        _cache = [];
        try
        {
            SimpTheorems? local = null;
            foreach (var x in xs)
            {
                if (m.IsProof(x))
                {
                    local ??= new SimpTheorems();
                    local.AddRange(m.MkSimpTheoremsFromProof(x));
                }
            }
            if (local is not null)
            {
                _theorems = _theorems.Insert(0, local);
            }
            return k();
        }
        finally
        {
            _cache = savedCache;
            _theorems = savedTheorems;
        }
    }

    private SimpResult SimpProj(Expr e)
    {
        if (WithMetaConfig(() => m.ReduceProj(e)) is { } reduced)
        {
            return new(reduced);
        }
        var proj = (ProjExpr)e;
        var s = proj.Struct;
        var motive = m.WithLocalDeclD(Name.From("s"), m.InferType(s), x =>
        {
            var p = proj.UpdateProj(x);
            if (ExprOps.Find(m.InferType(p), (y, _) => y == x) is not null)
            {
                return null;
            }
            var mot = m.MkLambdaFVars([x], m.MkEq(e, p));
            return m.IsTypeCorrect(mot) ? mot : null;
        });
        if (motive is null)
        {
            return new(Dsimp(e));
        }
        var r = Simp(s);
        var eNew = proj.UpdateProj(r.Expr);
        return r.Proof is { } h ? new(eNew, m.MkEqNDRec(motive, m.MkEqRefl(e), h)) : new(eNew);
    }

    private SimpResult SimpLambda(Expr e) =>
        m.LambdaTelescope(e, (xs, body) => WithNewLemmas(xs, () => AddLambdas(Simp(body), xs)));

    // Lean's Result.addLambdas.
    private SimpResult AddLambdas(SimpResult r, IReadOnlyList<Expr> xs)
    {
        var eNew = m.MkLambdaFVars(xs, r.Expr);
        if (r.Proof is not { } h)
        {
            return new(eNew);
        }
        for (int i = xs.Count - 1; i >= 0; i--)
        {
            h = m.MkFunExt(m.MkLambdaFVars([xs[i]], h));
        }
        return new(eNew, h);
    }

    // Lean's mkImpCongr over results.
    private SimpResult MkImpCongr(ForallExpr src, SimpResult r1, SimpResult r2)
    {
        var e = src.UpdateBinding(r1.Expr, r2.Expr);
        return r1.Proof is null && r2.Proof is null ? new(e) : new(e, m.MkImpCongr(r1.GetProof(m), r2.GetProof(m)));
    }

    private SimpResult SimpArrow(ForallExpr e)
    {
        var p = e.BinderType;
        var q = e.Body;
        var rp = Simp(p);
        if (Config.Contextual && m.IsProp(p) && m.IsProp(q))
        {
            return m.WithLocalDeclD(e.BinderName, rp.Expr, h => WithNewLemmas([h], () =>
            {
                var rq = Simp(q);
                if (rq.Proof is not { } hq)
                {
                    return MkImpCongr(e, rp, rq);
                }
                hq = m.MkLambdaFVars([h], hq);
                if (ExprOps.Find(rq.Expr, (x, _) => x == h) is not null)
                {
                    return new SimpResult(m.MkForallFVars([h], rq.Expr), m.WithDefault(() => m.MkImpDepCongrCtx(rp.GetProof(m), hq)));
                }
                return new SimpResult(e.UpdateBinding(rp.Expr, rq.Expr), m.WithDefault(() => m.MkImpCongrCtx(rp.GetProof(m), hq)));
            }));
        }
        return MkImpCongr(e, rp, Simp(q));
    }

    private SimpResult SimpForall(Expr e)
    {
        var f = (ForallExpr)e;
        if (!f.Body.HasLooseBVars)
        {
            return SimpArrow(f);
        }
        if (!m.IsProp(e))
        {
            return new(Dsimp(e));
        }
        var domain = f.BinderType;
        if (m.IsProp(domain))
        {
            var rd = Simp(domain);
            if (rd.Proof is { } h1)
            {
                // forall_prop_domain_congr {p₁ p₂} {q₁ q₂} (h₁ : p₁ = p₂) (h₂ : ∀ a : p₂, q₁ (h₁.substr a) = q₂ a)
                var p1 = domain;
                var p2 = rd.Expr;
                var q1 = Expr.Lam(f.BinderName, p1, f.Body, f.BinderInfo);
                return m.WithLocalDecl(f.BinderName, f.BinderInfo, p2, a => WithNewLemmas([a], () =>
                {
                    var prop = Expr.Prop;
                    var substr = Expr.App(Expr.Const(SimpNames.EqSubstr, Level.One), prop, Expr.Lam(Name.From("x"), prop, Expr.BVar(0)), p2, p1, h1, a);
                    var rb = Simp(ExprOps.Instantiate(f.Body, substr));
                    var h2 = m.MkLambdaFVars([a], rb.GetProof(m));
                    var q2 = m.MkLambdaFVars([a], rb.Expr);
                    var result = m.MkForallFVars([a], rb.Expr);
                    var proof = Expr.App(Expr.Const(SimpNames.ForallPropDomainCongr), p1, p2, q1, q2, h1, h2);
                    return new SimpResult(result, proof);
                }));
            }
        }
        return m.WithLocalDecl(f.BinderName, f.BinderInfo, Dsimp(domain), x => WithNewLemmas([x], () =>
        {
            var rb = Simp(ExprOps.Instantiate(f.Body, x));
            var eNew = m.MkForallFVars([x], rb.Expr);
            return rb.Proof is { } h ? new SimpResult(eNew, m.MkForallCongr(m.MkLambdaFVars([x], h))) : new SimpResult(eNew);
        }));
    }
}
