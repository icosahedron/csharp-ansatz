using System.Collections.Immutable;
using Warrant.Kernel;
using Warrant.Vir;

namespace Warrant.Engine;

/// <summary>A unit handed to the engine: VIR, with what messages and reports need but no hash covers.</summary>
/// <param name="Unit">The VIR unit.</param>
/// <param name="DisplayName">The C# display name (KTD6); null to fall back to one derived from the key.</param>
/// <param name="Spans">The unit's span table, by pre-order node ID; null when spans are not available.</param>
public sealed record EngineUnit(VirUnit Unit, string? DisplayName = null, SpanTable? Spans = null);

/// <summary>Which of the two fixed proof terms the kernel accepted (docs/m4/06).</summary>
public enum ProofKind
{
    /// <summary><c>@Eq.refl T a</c>, for an equation <c>@Eq T a b</c>.</summary>
    Rfl,

    /// <summary><c>@of_decide_eq_true P D (@Eq.refl Bool Bool.true)</c>.</summary>
    Decide,
}

/// <summary>An assumption a unit's outcome relies on, and the unit it comes from.</summary>
/// <param name="UnitKey">The key of the unit whose VIR records the assumption: the unit itself, or one it depends on.</param>
/// <param name="Assumption">The assumption.</param>
public sealed record UnitAssumption(string UnitKey, VirAssumption Assumption);

/// <summary>
/// The outcome of one unit. Each unit ends in exactly one: <see cref="TranslatedOutcome"/>, <see cref="ProvedOutcome"/>,
/// <see cref="FalseOutcome"/>, <see cref="UndecidedOutcome"/>, <see cref="FailedOutcome"/> or <see cref="SkippedOutcome"/>.
/// </summary>
/// <param name="Key">The unit's documentation-comment ID.</param>
/// <param name="UnitKind">What the unit is.</param>
/// <param name="DisplayName">The C# display name.</param>
/// <param name="Assumptions">
/// The unit's own VIR assumptions; a theorem also inherits those of every unit it depends on, transitively (docs/m4/07).
/// </param>
public abstract record UnitOutcome(string Key, VirUnitKind UnitKind, string DisplayName, ImmutableArray<UnitAssumption> Assumptions);

/// <summary>A function or type unit whose declarations the kernel admitted.</summary>
/// <param name="Key">The unit's key.</param>
/// <param name="UnitKind">What the unit is.</param>
/// <param name="DisplayName">The C# display name.</param>
/// <param name="Assumptions">The unit's assumptions.</param>
/// <param name="Declarations">The admitted declarations, in admission order.</param>
public sealed record TranslatedOutcome(
    string Key, VirUnitKind UnitKind, string DisplayName, ImmutableArray<UnitAssumption> Assumptions, ImmutableArray<KernelDeclaration> Declarations)
    : UnitOutcome(Key, UnitKind, DisplayName, Assumptions);

/// <summary>A theorem the kernel admitted with exactly the name and type translation built (KTD22).</summary>
/// <param name="Key">The unit's key.</param>
/// <param name="UnitKind">What the unit is.</param>
/// <param name="DisplayName">The C# display name.</param>
/// <param name="Assumptions">The theorem's assumptions, with those of the units it depends on.</param>
/// <param name="By">The proof the kernel accepted.</param>
/// <param name="Certificate">The admitted declaration, which NDJSON export writes for Lean to re-check.</param>
public sealed record ProvedOutcome(
    string Key, VirUnitKind UnitKind, string DisplayName, ImmutableArray<UnitAssumption> Assumptions, ProofKind By, TheoremDecl Certificate)
    : UnitOutcome(Key, UnitKind, DisplayName, Assumptions);

/// <summary>A theorem whose claim the kernel computes to <c>false</c> (WRT0001).</summary>
/// <param name="Key">The unit's key.</param>
/// <param name="UnitKind">What the unit is.</param>
/// <param name="DisplayName">The C# display name.</param>
/// <param name="Assumptions">The theorem's assumptions, with those of the units it depends on.</param>
/// <param name="Sides">
/// For a claim that is a single <c>==</c>, <c>&lt;</c>, <c>&lt;=</c>, <c>&gt;</c> or <c>&gt;=</c>, its left and right
/// operands in source order with their values; empty for any other claim.
/// </param>
public sealed record FalseOutcome(
    string Key, VirUnitKind UnitKind, string DisplayName, ImmutableArray<UnitAssumption> Assumptions, ImmutableArray<ReadBackSide> Sides)
    : UnitOutcome(Key, UnitKind, DisplayName, Assumptions)
{
    /// <summary>The diagnostic code: the claim is false.</summary>
    public const string Code = "WRT0001";
}

/// <summary>
/// A theorem neither proof proves and whose <c>decide</c> does not compute to <c>Bool.false</c> within the fuel limit
/// (WRT0006). Running out of fuel is never success.
/// </summary>
/// <param name="Key">The unit's key.</param>
/// <param name="UnitKind">What the unit is.</param>
/// <param name="DisplayName">The C# display name.</param>
/// <param name="Assumptions">The theorem's assumptions, with those of the units it depends on.</param>
/// <param name="Reason">Why it is undecided, for people.</param>
public sealed record UndecidedOutcome(
    string Key, VirUnitKind UnitKind, string DisplayName, ImmutableArray<UnitAssumption> Assumptions, string Reason)
    : UnitOutcome(Key, UnitKind, DisplayName, Assumptions)
{
    /// <summary>The diagnostic code: the claim was not decided.</summary>
    public const string Code = "WRT0006";
}

/// <summary>
/// A unit that translation could not translate, whose declaration the kernel rejected, or a theorem the kernel admitted
/// with a type other than its statement.
/// </summary>
/// <param name="Key">The unit's key.</param>
/// <param name="UnitKind">What the unit is.</param>
/// <param name="DisplayName">The C# display name.</param>
/// <param name="Assumptions">The unit's assumptions.</param>
/// <param name="Reason">The translation or kernel error.</param>
public sealed record FailedOutcome(
    string Key, VirUnitKind UnitKind, string DisplayName, ImmutableArray<UnitAssumption> Assumptions, string Reason)
    : UnitOutcome(Key, UnitKind, DisplayName, Assumptions);

/// <summary>A unit not attempted because a unit it depends on failed or was skipped.</summary>
/// <param name="Key">The unit's key.</param>
/// <param name="UnitKind">What the unit is.</param>
/// <param name="DisplayName">The C# display name.</param>
/// <param name="Assumptions">The unit's assumptions.</param>
/// <param name="Dependency">The key of the dependency that failed or was skipped.</param>
/// <param name="Reason">A message for people.</param>
public sealed record SkippedOutcome(
    string Key, VirUnitKind UnitKind, string DisplayName, ImmutableArray<UnitAssumption> Assumptions, string Dependency, string Reason)
    : UnitOutcome(Key, UnitKind, DisplayName, Assumptions);

/// <summary>One side of a false comparison.</summary>
/// <param name="NodeId">The side's VIR node ID (pre-order, docs/m4/04).</param>
/// <param name="Span">The node's source span, when the unit came with spans.</param>
/// <param name="Value">The value the kernel computes for it.</param>
public sealed record ReadBackSide(int NodeId, VirSpan? Span, ReadBackValue Value);
