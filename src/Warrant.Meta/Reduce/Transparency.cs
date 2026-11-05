using Warrant.Cic;

namespace Warrant.Meta;

/// <summary>
/// Lean 4.35.0's <c>TransparencyMode</c> (Init/MetaTypes.lean 113), declared in the order of
/// <c>TransparencyMode.lt</c> (Lean/Meta/TransparencyMode.lean 37): <c>none &lt; reducible &lt;
/// instances &lt; implicit &lt; default &lt; all</c> (KTD5, docs/m5a/02 "Transparency").
/// </summary>
public enum TransparencyMode
{
    /// <summary>Unfolds nothing.</summary>
    None,

    /// <summary>Unfolds only <c>@[reducible]</c> constants; <c>simp</c> and discrimination trees.</summary>
    Reducible,

    /// <summary>Also unfolds <c>@[instance_reducible]</c> constants; instance resolution.</summary>
    Instances,

    /// <summary>Also unfolds <c>@[implicit_reducible]</c> constants; implicit arguments in unification.</summary>
    Implicit,

    /// <summary>Unfolds everything but <c>@[irreducible]</c> constants and theorems; <c>apply</c> and <c>exact</c>.</summary>
    Default,

    /// <summary>Unfolds every definition (never a theorem).</summary>
    All,
}

/// <summary>Lean's <c>ProjReductionKind</c>: how <c>whnfCore</c> reduces a projection's structure.</summary>
public enum ProjReductionKind
{
    /// <summary>Projections are not reduced.</summary>
    No,

    /// <summary>The structure is reduced with <c>whnfCore</c>.</summary>
    Yes,

    /// <summary>The structure is reduced with <c>whnf</c>.</summary>
    YesWithDelta,

    /// <summary>The structure is reduced with <c>whnfAtMostI</c>.</summary>
    YesWithDeltaI,
}

/// <summary>Lean's <c>EtaStructMode</c>: for which structures eta is used.</summary>
public enum EtaStructMode
{
    /// <summary>Every non-recursive structure.</summary>
    All,

    /// <summary>Non-recursive structures that are not classes.</summary>
    NotClasses,

    /// <summary>Never.</summary>
    None,
}

/// <summary>Helpers on <see cref="TransparencyMode"/>.</summary>
public static class TransparencyModeExtensions
{
    /// <summary>Lean's <c>TransparencyMode.lt</c>, a strict linear order matching the enum's.</summary>
    public static bool Lt(this TransparencyMode a, TransparencyMode b) => a < b;

    /// <summary>Lean's <c>TransparencyMode.toString</c>.</summary>
    public static string ToLeanString(this TransparencyMode m) => m switch
    {
        TransparencyMode.None => "none",
        TransparencyMode.Reducible => "reducible",
        TransparencyMode.Instances => "instances",
        TransparencyMode.Implicit => "implicit",
        TransparencyMode.Default => "default",
        _ => "all",
    };
}

// The reduction and unification fields of Lean's Meta.Config (Lean/Meta/Basic.lean 106-216), with
// Lean's defaults. Unification hints and context approximation are not ported, so their flags are
// absent.
public sealed partial record MetaConfig
{
    /// <summary>First-order approximation of <c>?m a₁ … aₙ =?= f b₁ … bₖ</c> (Lean's <c>foApprox</c>).</summary>
    public bool FoApprox { get; init; }

    /// <summary>Ignore condition 2 of the pattern check (Lean's <c>quasiPatternApprox</c>).</summary>
    public bool QuasiPatternApprox { get; init; }

    /// <summary>Solve <c>?m t =?= c</c> with <c>?m := fun _ => c</c> (Lean's <c>constApprox</c>).</summary>
    public bool ConstApprox { get; init; }

    /// <summary>Throw a stuck exception on <c>?m … =?= t</c> with a read-only <c>?m</c> (Lean's <c>isDefEqStuckEx</c>).</summary>
    [System.Diagnostics.CodeAnalysis.SuppressMessage("Naming", "CA1711:Identifiers should not have incorrect suffix", Justification = "Lean's name.")]
    public bool IsDefEqStuckEx { get; init; }

    /// <summary>Proof irrelevance in unification (Lean's <c>proofIrrelevance</c>).</summary>
    public bool ProofIrrelevance { get; init; } = true;

    /// <summary>Offset constraints such as <c>?x + 1 =?= e</c> (Lean's <c>offsetCnstrs</c>).</summary>
    public bool OffsetCnstrs { get; init; } = true;

    /// <summary>Which constants <c>whnf</c> and <c>isDefEq</c> may unfold (Lean's <c>transparency</c>).</summary>
    public TransparencyMode Transparency { get; init; } = TransparencyMode.Default;

    /// <summary>Eta for structures (Lean's <c>etaStruct</c>).</summary>
    public EtaStructMode EtaStruct { get; init; } = EtaStructMode.All;

    /// <summary>Approximations when solving postponed universe constraints (Lean's <c>univApprox</c>).</summary>
    public bool UnivApprox { get; init; } = true;

    /// <summary>Reduce recursor and matcher applications (Lean's <c>iota</c>).</summary>
    public bool Iota { get; init; } = true;

    /// <summary>Beta-reduce (Lean's <c>beta</c>).</summary>
    public bool Beta { get; init; } = true;

    /// <summary>Projection reduction in <c>whnfCore</c> (Lean's <c>proj</c>).</summary>
    public ProjReductionKind Proj { get; init; } = ProjReductionKind.YesWithDelta;

    /// <summary>Zeta-reduce <c>let</c> and <c>have</c> (Lean's <c>zeta</c>).</summary>
    public bool Zeta { get; init; } = true;

    /// <summary>Unfold let-variables of the local context (Lean's <c>zetaDelta</c>).</summary>
    public bool ZetaDelta { get; init; } = true;

    /// <summary>Drop unused <c>let</c>s (Lean's <c>zetaUnused</c>).</summary>
    public bool ZetaUnused { get; init; } = true;

    /// <summary>With <see cref="Zeta"/>, also zeta-reduce <c>have</c>s (Lean's <c>zetaHave</c>).</summary>
    public bool ZetaHave { get; init; } = true;

    /// <summary>Use <c>canUnfoldAtMatcher</c> instead of <c>canUnfoldDefault</c> (Lean's <c>canUnfoldPredicateConfig</c>).</summary>
    public bool CanUnfoldAtMatcher { get; init; }

    /// <summary>The bits of the configuration that reduction and unification results depend on (Lean's <c>Config.toKey</c>), for cache keys.</summary>
    internal ulong Key =>
        (ulong)Transparency
        | (B(FoApprox) << 3)
        | (B(QuasiPatternApprox) << 5)
        | (B(ConstApprox) << 6)
        | (B(IsDefEqStuckEx) << 7)
        | (B(ProofIrrelevance) << 9)
        | (B(AssignSyntheticOpaque) << 10)
        | (B(OffsetCnstrs) << 11)
        | (B(Iota) << 12)
        | (B(Beta) << 13)
        | (B(Zeta) << 14)
        | (B(ZetaDelta) << 15)
        | (B(UnivApprox) << 16)
        | ((ulong)EtaStruct << 17)
        | ((ulong)Proj << 19)
        | (B(ZetaHave) << 21)
        | (B(ZetaUnused) << 22)
        | (B(CanUnfoldAtMatcher) << 23);

    private static ulong B(bool b) => b ? 1UL : 0UL;
}

// Transparency scopes and the unfolding predicates (Lean/Meta/Basic.lean 1306-1345,
// Lean/Meta/GetUnfoldableConst.lean).
public sealed partial class MetaM
{
    // Lean 4.35.0's @[match_pattern] declarations in Init (canUnfoldAtMatcher's first clause). The
    // attribute is not in the sidecar; this is the closed set the bundle's Init carries.
    private static readonly HashSet<Name> MatchPatternNames =
    [
        .. new[]
        {
            "Nat.add", "Add.add", "HAdd.hAdd", "Neg.neg", "Mul.mul", "HMul.hMul", "Inv.inv",
            "Nat.cast", "Int.cast", "Unit.unit", "rfl", "HEq.rfl", "Decidable.isFalse", "Decidable.isTrue",
            "BitVec.ofNatLT", "BitVec.ofNat", "Char.ofNat", "List.toArray",
        }.Select(Name.Parse),
    ];

    // canUnfoldAtMatcher's fixed list (Lean/Meta/GetUnfoldableConst.lean 42-55).
    private static readonly HashSet<Name> UnfoldAtMatcherNames =
    [
        .. new[]
        {
            "OfNat.ofNat", "NatCast.natCast", "Zero.zero", "One.one", "decEq", "Nat.decEq",
            "Char.ofNat", "Char.ofNatAux", "String.decEq", "List.hasDecEq", "Fin.ofNat",
            "UInt8.ofNat", "UInt8.decEq", "UInt16.ofNat", "UInt16.decEq", "UInt32.ofNat", "UInt32.decEq",
            "UInt64.ofNat", "UInt64.decEq", "HMod.hMod", "Mod.mod",
        }.Select(Name.Parse),
    ];

    /// <summary>The current transparency (Lean's <c>getTransparency</c>).</summary>
    public TransparencyMode GetTransparency() => Config.Transparency;

    /// <summary>Whether the transparency is <c>all</c> (Lean's <c>shouldReduceAll</c>).</summary>
    public bool ShouldReduceAll() => Config.Transparency == TransparencyMode.All;

    /// <summary>Whether the transparency is <c>reducible</c> (Lean's <c>shouldReduceReducibleOnly</c>).</summary>
    public bool ShouldReduceReducibleOnly() => Config.Transparency == TransparencyMode.Reducible;

    /// <summary>Runs <paramref name="k"/> at <paramref name="mode"/> (Lean's <c>withTransparency</c>).</summary>
    public T WithTransparency<T>(TransparencyMode mode, Func<T> k) =>
        Config.Transparency == mode ? k() : WithConfig(c => c with { Transparency = mode }, k);

    /// <summary>Runs <paramref name="k"/> at <c>default</c> (Lean's <c>withDefault</c>).</summary>
    public T WithDefault<T>(Func<T> k) => WithTransparency(TransparencyMode.Default, k);

    /// <summary>Runs <paramref name="k"/> at <c>reducible</c> (Lean's <c>withReducible</c>).</summary>
    public T WithReducible<T>(Func<T> k) => WithTransparency(TransparencyMode.Reducible, k);

    /// <summary>Runs <paramref name="k"/> at <c>instances</c> (Lean's <c>withReducibleAndInstances</c>).</summary>
    public T WithReducibleAndInstances<T>(Func<T> k) => WithTransparency(TransparencyMode.Instances, k);

    /// <summary>Runs <paramref name="k"/> at <c>implicit</c> (Lean's <c>withImplicit</c>).</summary>
    public T WithImplicit<T>(Func<T> k) => WithTransparency(TransparencyMode.Implicit, k);

    /// <summary>Runs <paramref name="k"/> at a transparency of at least <paramref name="mode"/> (Lean's <c>withAtLeastTransparency</c>).</summary>
    public T WithAtLeastTransparency<T>(TransparencyMode mode, Func<T> k) =>
        Config.Transparency.Lt(mode) ? WithConfig(c => c with { Transparency = mode }, k) : k();

    /// <summary>
    /// Runs <paramref name="k"/> with a configuration strong enough to infer types: at least
    /// <c>default</c>, with beta, iota, zeta, zeta-delta, projections and eta for structures (Lean's
    /// <c>withInferTypeConfig</c>, Lean/Meta/InferType.lean 228).
    /// </summary>
    public T WithInferTypeConfig<T>(Func<T> k) => WithAtLeastTransparency(TransparencyMode.Default, () =>
    {
        var cfg = Config;
        if (cfg is { Beta: true, Iota: true, Zeta: true, ZetaHave: true, ZetaDelta: true, Proj: ProjReductionKind.YesWithDelta, EtaStruct: EtaStructMode.All })
        {
            return k();
        }
        return WithConfig(c => c with { Beta = true, Iota = true, Zeta = true, ZetaHave = true, ZetaDelta = true, Proj = ProjReductionKind.YesWithDelta, EtaStruct = EtaStructMode.All }, k);
    });

    /// <summary>
    /// Runs <paramref name="k"/> at a transparency of at least <c>implicit</c>, with the reductions
    /// type checking needs (Lean's <c>withImplicitConfig</c>, Lean/Meta/ExprDefEq.lean 323).
    /// </summary>
    public T WithImplicitConfig<T>(Func<T> k) => WithAtLeastTransparency(TransparencyMode.Implicit, () => WithCheckingReductions(k));

    /// <summary>Like <see cref="WithImplicitConfig{T}"/> at exactly <c>instances</c> (Lean's <c>withExactInstancesConfig</c>).</summary>
    public T WithExactInstancesConfig<T>(Func<T> k) => WithTransparency(TransparencyMode.Instances, () => WithCheckingReductions(k));

    private T WithCheckingReductions<T>(Func<T> k)
    {
        var cfg = Config;
        if (cfg is { Beta: true, Iota: true, Zeta: true, ZetaHave: true, ZetaDelta: true, Proj: ProjReductionKind.YesWithDelta })
        {
            return k();
        }
        return WithConfig(c => c with { Beta = true, Iota = true, Zeta = true, ZetaHave = true, ZetaDelta = true, Proj = ProjReductionKind.YesWithDelta }, k);
    }

    /// <summary>
    /// Lean's <c>canUnfoldDefault</c> (Lean/Meta/GetUnfoldableConst.lean 17): the transparency ×
    /// reducibility-status table. <c>none</c> unfolds nothing, <c>all</c> everything, <c>default</c>
    /// all but irreducible constants; the other modes unfold reducible constants, plus
    /// instance-reducible ones at <c>instances</c> and <c>implicit</c>, plus implicit-reducible ones at
    /// <c>implicit</c>.
    /// </summary>
    public bool CanUnfoldDefault(MetaConfig cfg, ConstantInfo info)
    {
        ArgumentNullException.ThrowIfNull(cfg);
        ArgumentNullException.ThrowIfNull(info);
        switch (cfg.Transparency)
        {
            case TransparencyMode.None:
                return false;
            case TransparencyMode.All:
                return true;
            case TransparencyMode.Default:
                return !IsIrreducible(info.Name);
            default:
                var m = cfg.Transparency;
                var status = GetReducibilityStatus(info.Name);
                return status == ReducibilityStatus.Reducible
                    || (status == ReducibilityStatus.InstanceReducible && m is TransparencyMode.Instances or TransparencyMode.Implicit)
                    || (status == ReducibilityStatus.ImplicitReducible && m == TransparencyMode.Implicit);
        }
    }

    /// <summary>
    /// Lean's <c>canUnfoldAtMatcher</c>: <see cref="CanUnfoldDefault"/>, plus the
    /// <c>@[match_pattern]</c> declarations and a fixed list (<c>OfNat.ofNat</c>, <c>HMod.hMod</c>,
    /// <c>decEq</c>, …) needed to expose constructors in match discriminants.
    /// </summary>
    public bool CanUnfoldAtMatcher(MetaConfig cfg, ConstantInfo info)
    {
        ArgumentNullException.ThrowIfNull(info);
        return CanUnfoldDefault(cfg, info) || MatchPatternNames.Contains(info.Name) || UnfoldAtMatcherNames.Contains(info.Name);
    }

    /// <summary>Lean's <c>canUnfold</c>: the predicate the configuration selects.</summary>
    public bool CanUnfold(ConstantInfo info) =>
        Config.CanUnfoldAtMatcher ? CanUnfoldAtMatcher(Config, info) : CanUnfoldDefault(Config, info);

    /// <summary>
    /// The definition <paramref name="constName"/>, if the transparency lets it unfold; theorems
    /// never unfold (Lean's <c>getUnfoldableConst?</c>).
    /// </summary>
    /// <exception cref="MetaException">The constant is unknown.</exception>
    public ConstantInfo? GetUnfoldableConst(Name constName)
    {
        var info = GetConstInfo(constName);
        return info is DefinitionInfo && CanUnfold(info) ? info : null;
    }

    /// <summary>Like <see cref="GetUnfoldableConst"/>, but null for an unknown constant (Lean's <c>getUnfoldableConstNoEx?</c>).</summary>
    [System.Diagnostics.CodeAnalysis.SuppressMessage("Naming", "CA1711:Identifiers should not have incorrect suffix", Justification = "Lean's name.")]
    public ConstantInfo? GetUnfoldableConstNoEx(Name constName) =>
        Env.Find(constName) is DefinitionInfo info && CanUnfold(info) ? info : null;

    /// <summary>Lean's <c>useEtaStruct</c>: whether eta for structures applies to <paramref name="inductName"/>.</summary>
    public bool UseEtaStruct(Name inductName) => Config.EtaStruct switch
    {
        EtaStructMode.None => false,
        EtaStructMode.All => true,
        _ => !Attributes.IsClass(inductName),
    };
}
