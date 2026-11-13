using Warrant.Cic;
using Warrant.Meta;
using Warrant.Semantics;

namespace Warrant.Engine.Contracts;

/// <summary>
/// The VC simp set (plan M6 KTD14): the one-state assertion lemmas, the predicate transformers' equations and the
/// equations of <c>ClrExn.Allowed</c> and <c>ClrExn.External</c>, besides Warrant's default set. It is kept apart from <c>Tactic.Simp()</c>'s default
/// set, as omega-prep is, so existing scripts do not change. U3's checkpoint used exactly this list
/// (<c>EffectCheckpointTests.VcSimpLemmas</c>).
/// </summary>
internal static class VcSimpSet
{
    /// <summary>The lemmas added to the default set.</summary>
    public static IReadOnlyList<Name> Lemmas { get; } =
    [
        .. new[]
        {
            "Std.Do.SPred.entails_1", "Std.Do.SPred.apply_pure_cons", "Std.Do.SPred.down_pure_nil",
            "Std.Do.SPred.and_cons", "Std.Do.SPred.and_nil", "Std.Do.SPred.or_cons", "Std.Do.SPred.or_nil",
            "Std.Do.PredTrans.apply_Pure_pure", "Std.Do.PredTrans.apply_pure", "Std.Do.PredTrans.apply_Functor_map",
            "Std.Do.PredTrans.apply_bind", "Std.Do.PredTrans.apply_Bind_bind", "Std.Do.PredTrans.apply_Seq_seq",
            "Std.Do.PredTrans.apply_const", "Std.Do.PredTrans.apply_throw", "Std.Do.PredTrans.apply_pushArg",
            "Std.Do.PredTrans.apply_pushExcept", "Std.Do.PredTrans.apply_dite", "Std.Do.PredTrans.apply_ite",
        }.Select(Name.Parse),
        // ClrExn.Allowed, and ClrExn.External, Spec.NoThrow's exception postcondition (#182), at each constructor.
        .. ClrExnNames.Constructors.Select(c => ClrExnNames.Equation(ClrExnNames.Allowed, c)),
        .. ClrExnNames.Constructors.Select(c => ClrExnNames.Equation(ClrExnNames.External, c)),
        .. new[]
        {
            // A dependency's Spec.Ensures over a nullable result (M6 U20) meets the walk's case `r = some v`: a null test
            // and ?? on a constructor, and the impossible case `some v = none`.
            "Option.isNone_some", "Option.isNone_none", "Warrant.Nullable.some_eq_none", "Bool.false_eq_true", "Bool.true_eq_false",
            "Warrant.Nullable.coalesce_some", "Warrant.Nullable.coalesce_none",
        }.Select(Name.Parse),
    ];

    /// <summary>
    /// The lemmas of the walker's light reduction between rules: a one-state assertion read at a world, <c>(⌜p⌝ s).down</c>,
    /// is <c>p</c>. Both are <c>rfl</c> lemmas, so the step changes no proposition, only its spelling.
    /// </summary>
    private static readonly Name[] LightLemmas = [Name.Parse("Std.Do.SPred.apply_pure_cons"), Name.Parse("Std.Do.SPred.down_pure_nil")];

    /// <summary>The VC simp set's context: the default set with <see cref="Lemmas"/>.</summary>
    public static SimpContext Context(MetaM meta) =>
        DefaultSimpSet.Context(meta, SimpConfig.Default with { FailIfUnchanged = false }, Theorems(meta, Lemmas));

    /// <summary>
    /// The context of the walker's light reduction: β, projections and <c>let</c>s (Lean's <c>dsimp only</c>, #212), and a
    /// one-state assertion read at a world; nothing of the default set, so the walker's next rule still matches.
    /// </summary>
    public static SimpContext Light(MetaM meta) =>
        new(SimpConfig.Default, [Theorems(meta, LightLemmas)], SimpContext.CongrTheoremsOf(meta.Attributes));

    private static SimpTheorems Theorems(MetaM meta, IEnumerable<Name> names)
    {
        var theorems = new SimpTheorems();
        foreach (var name in names)
        {
            theorems.AddRange(meta.MkSimpTheoremsFromConst(name));
        }
        return theorems;
    }
}
