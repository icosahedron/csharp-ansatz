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

    /// <summary>The term the theorem's proof script built (M5a KTD6).</summary>
    Script,
}

/// <summary>An assumption a unit's outcome relies on, and the unit it comes from.</summary>
/// <param name="UnitKey">The key of the unit whose VIR records the assumption: the unit itself, or one it depends on.</param>
/// <param name="Assumption">The assumption.</param>
public sealed record UnitAssumption(string UnitKey, VirAssumption Assumption);

/// <summary>
/// The outcome of one unit. Each unit ends in exactly one: <see cref="TranslatedOutcome"/>, <see cref="ProvedOutcome"/>,
/// <see cref="FalseOutcome"/>, <see cref="NotProvedOutcome"/>, <see cref="UndecidedOutcome"/>,
/// <see cref="InternalErrorOutcome"/>, <see cref="FailedOutcome"/> or <see cref="SkippedOutcome"/>.
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
/// A theorem whose proof script did not close its goal: a tactic failed or is not available yet, or goals remained
/// (WRT0001, M5a R2). It says the claim was not proved, never that it is false; a counterexample, when the search finds
/// one, is what shows that (KTD25).
/// </summary>
/// <param name="Key">The unit's key.</param>
/// <param name="UnitKind">What the unit is.</param>
/// <param name="DisplayName">The C# display name.</param>
/// <param name="Assumptions">The theorem's assumptions, with those of the units it depends on.</param>
/// <param name="Message">
/// What went wrong, in Lean's wording: <c>unsolved goals</c>, <c>Tactic `x` failed: …</c> or <c>Tactic `x` is not
/// available yet</c>. Its first line is complete on its own; later lines give details such as the types of a mismatch.
/// </param>
/// <param name="Goals">The goals, printed in Lean's layout with C# names and separated by blank lines; empty when none.</param>
/// <param name="TacticNode">
/// The VIR node ID (pre-order, docs/m4/04) of the <c>Tactic.X(...)</c> call that failed; null when goals remained at the
/// end. Rendering maps it through the current extraction's <see cref="SpanTable"/> (KTD7).
/// </param>
/// <param name="Counterexample">Parameter values that falsify the claim, in parameter order; empty when none was found.</param>
public sealed record NotProvedOutcome(
    string Key,
    VirUnitKind UnitKind,
    string DisplayName,
    ImmutableArray<UnitAssumption> Assumptions,
    string Message,
    string Goals,
    int? TacticNode,
    ImmutableArray<CounterexampleValue> Counterexample)
    : UnitOutcome(Key, UnitKind, DisplayName, Assumptions)
{
    /// <summary>The diagnostic code: the claim was not proved.</summary>
    public const string Code = "WRT0001";

    /// <summary>
    /// For a recursive method, the recursive call whose decrease obligation was not proved (M5a KTD15); null for a theorem.
    /// The goals are that obligation's, and <see cref="TacticNode"/> is the call's node.
    /// </summary>
    public DecreaseFailure? Decrease { get; init; }
}

/// <summary>A recursive call whose decrease obligation <c>f.$dec_k</c> was not proved (M5a KTD15, docs/m5a/03).</summary>
/// <param name="Index">The call's number among the method's recursive calls, from 1, in source order.</param>
/// <param name="CallNode">The call's VIR node ID (pre-order, docs/m4/04); null if the call is not among the unit's nodes.</param>
/// <param name="MeasureNode">
/// The VIR node ID of <c>Spec.Decreases</c>'s argument; null if it is not among the unit's nodes.
/// </param>
public sealed record DecreaseFailure(int Index, int? CallNode, int? MeasureNode);

/// <summary>One parameter's value in a counterexample.</summary>
/// <param name="Parameter">The C# parameter's name.</param>
/// <param name="Value">The value as C# would write it: <c>2147483647</c>, <c>true</c>, <c>Light.Red</c>.</param>
public sealed record CounterexampleValue(string Parameter, string Value);

/// <summary>
/// A theorem Warrant could not finish checking because it built a term its own kernel rejected, or because Meta failed
/// in a way no tactic should (WRT0010, KTD19). This is a bug in Warrant, never a verdict on the claim.
/// </summary>
/// <param name="Key">The unit's key.</param>
/// <param name="UnitKind">What the unit is.</param>
/// <param name="DisplayName">The C# display name.</param>
/// <param name="Assumptions">The theorem's assumptions, with those of the units it depends on.</param>
/// <param name="Reason">The kernel's or Meta's message.</param>
public sealed record InternalErrorOutcome(
    string Key, VirUnitKind UnitKind, string DisplayName, ImmutableArray<UnitAssumption> Assumptions, string Reason)
    : UnitOutcome(Key, UnitKind, DisplayName, Assumptions)
{
    /// <summary>The diagnostic code: an internal error.</summary>
    public const string Code = "WRT0010";
}

/// <summary>
/// A unit that ran out of a budget: kernel fuel, tactic fuel or the time limit (WRT0006, M5a R13, M5b R5), whether it is a
/// theorem or a definition with its decrease proofs and equation lemma; or a theorem without a script
/// that neither fixed proof proves and whose <c>decide</c> does not compute to <c>Bool.false</c> within the fuel limit.
/// Running out of a budget is never success.
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
/// <param name="Value">The value the kernel computes for it.</param>
public sealed record ReadBackSide(int NodeId, ReadBackValue Value);
