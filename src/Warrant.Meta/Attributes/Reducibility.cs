using Warrant.Cic;

namespace Warrant.Meta;

/// <summary>
/// Lean 4.35.0's <c>ReducibilityStatus</c> (Lean/ReducibilityAttrs.lean 40-42), in Lean's order: how
/// far Meta may see through a definition at each transparency (KTD5, docs/m5a/02 "Transparency").
/// </summary>
/// <remarks>
/// The bundle does not carry statuses; they come from the attribute sidecar (KTD9), and a constant
/// without an entry is <see cref="Semireducible"/>.
/// </remarks>
public enum ReducibilityStatus
{
    /// <summary><c>@[reducible]</c>: unfolded at every transparency from <c>reducible</c> up.</summary>
    Reducible,

    /// <summary>The default status of a definition.</summary>
    Semireducible,

    /// <summary><c>@[irreducible]</c>: unfolded only at <c>all</c>.</summary>
    Irreducible,

    /// <summary><c>@[implicit_reducible]</c> (for example <c>Int.bmod</c>).</summary>
    ImplicitReducible,

    /// <summary><c>@[instance_reducible]</c>: set by the <c>instance</c> command and on subobject class projections.</summary>
    InstanceReducible,
}

// The attributes Meta reads (Lean's MonadEnv queries on attribute extensions).
public sealed partial class MetaM
{
    /// <summary>
    /// The attributes of the environment's constants: the sidecar, or a fork of it carrying the
    /// engine's entries for translated declarations. Without one, every constant is semireducible
    /// and there are no instances, simp entries or matchers.
    /// </summary>
    public Sidecar Attributes { get; init; } = Sidecar.Empty;

    /// <summary>Lean's <c>getReducibilityStatus</c>: the status of <paramref name="declName"/>, <see cref="ReducibilityStatus.Semireducible"/> by default.</summary>
    public ReducibilityStatus GetReducibilityStatus(Name declName) => Attributes.GetReducibilityStatus(declName);

    /// <summary>Lean's <c>isReducible</c>: whether <paramref name="declName"/> is <c>@[reducible]</c>.</summary>
    public bool IsReducible(Name declName) => GetReducibilityStatus(declName) == ReducibilityStatus.Reducible;

    /// <summary>Lean's <c>isIrreducible</c>: whether <paramref name="declName"/> is <c>@[irreducible]</c>.</summary>
    public bool IsIrreducible(Name declName) => GetReducibilityStatus(declName) == ReducibilityStatus.Irreducible;

    /// <summary>Lean's <c>isImplicitReducible</c>.</summary>
    public bool IsImplicitReducible(Name declName) => GetReducibilityStatus(declName) == ReducibilityStatus.ImplicitReducible;

    /// <summary>Lean's <c>isInstanceReducible</c>.</summary>
    public bool IsInstanceReducible(Name declName) => GetReducibilityStatus(declName) == ReducibilityStatus.InstanceReducible;

    /// <summary>Lean's <c>getMatcherInfo?</c>: the matcher info of <paramref name="declName"/>, or <see langword="null"/> if it is not a matcher.</summary>
    public MatcherInfo? GetMatcherInfo(Name declName) => Attributes.GetMatcherInfo(declName);
}
