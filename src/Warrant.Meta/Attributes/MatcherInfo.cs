using System.Collections.Immutable;
using Warrant.Cic;

namespace Warrant.Meta;

/// <summary>
/// Lean's <c>Match.AltParamInfo</c> (Lean/Meta/Match/MatcherInfo.lean): the parameters of one
/// alternative of a matcher.
/// </summary>
/// <param name="NumFields">The alternative's fields, not counting discriminant equations.</param>
/// <param name="NumOverlaps">Overlap assumptions (splitters only).</param>
/// <param name="HasUnitThunk">Whether the alternative takes an artificial <c>Unit</c> parameter.</param>
public sealed record MatcherAltInfo(int NumFields, int NumOverlaps, bool HasUnitThunk);

/// <summary>
/// Lean's <c>Match.MatcherInfo</c> (Lean/Meta/Match/MatcherInfo.lean) for a compiled <c>match</c>
/// function, which Meta needs to reduce applications of it (<c>reduceMatcher?</c>). A matcher's
/// arguments are its parameters, the motive, the discriminants and the alternatives, in that order.
/// </summary>
/// <param name="Name">The matcher.</param>
/// <param name="NumParams">The number of parameters.</param>
/// <param name="NumDiscrs">The number of discriminants.</param>
/// <param name="Alts">Each alternative's parameter structure.</param>
/// <param name="UElimPos">
/// The position of the universe level parameter that is the elimination universe, or
/// <see langword="null"/> if the matcher eliminates only into <c>Prop</c>.
/// </param>
/// <param name="DiscrNames">For each discriminant, the <c>h</c> of an <c>h :</c> annotation, or <see langword="null"/>.</param>
/// <param name="Overlaps">Pairs (overlapping, overlapped) of alternatives that may overlap (a conservative approximation), sorted.</param>
public sealed record MatcherInfo(
    Name Name,
    int NumParams,
    int NumDiscrs,
    ImmutableArray<MatcherAltInfo> Alts,
    int? UElimPos,
    ImmutableArray<Name?> DiscrNames,
    ImmutableArray<(int Overlapping, int Overlapped)> Overlaps)
{
    /// <summary>Lean's <c>numAlts</c>.</summary>
    public int NumAlts => Alts.Length;

    /// <summary>Lean's <c>arity</c>: parameters, motive, discriminants and alternatives.</summary>
    public int Arity => NumParams + 1 + NumDiscrs + NumAlts;

    /// <summary>Lean's <c>getMotivePos</c>.</summary>
    public int MotivePos => NumParams;

    /// <summary>Lean's <c>getFirstDiscrPos</c>.</summary>
    public int FirstDiscrPos => NumParams + 1;

    /// <summary>Lean's <c>getFirstAltPos</c>.</summary>
    public int FirstAltPos => NumParams + 1 + NumDiscrs;

    /// <summary>Lean's <c>getNumDiscrEqs</c>: the number of discriminants annotated with <c>h :</c>.</summary>
    public int NumDiscrEqs => DiscrNames.Count(n => n is not null);

    /// <summary>Lean's <c>altNumParams</c>: each alternative's fields, overlaps, unit thunk and discriminant equations.</summary>
    public ImmutableArray<int> AltNumParams =>
        [.. Alts.Select(a => a.NumFields + a.NumOverlaps + (a.HasUnitThunk ? 1 : 0) + NumDiscrEqs)];
}
