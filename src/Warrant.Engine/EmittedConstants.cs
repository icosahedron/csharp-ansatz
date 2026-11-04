using Warrant.Cic;
using Warrant.Meta;

namespace Warrant.Engine;

/// <summary>
/// Every Init constant the engine and its tactics can put into a proof (M5a KTD29). Each must be a root of the semantics
/// bundle (<c>lean/bundle-roots.txt</c>), and a test checks that it is, as M4's test does for the translator's constants: a
/// constant missing from the bundle would otherwise fail only when a goal first needs it, and a certificate naming it
/// would fail Lean's re-check with "unknown constant". A tactic that emits a new constant adds it here.
/// </summary>
public static class EmittedConstants
{
    /// <summary>The constants.</summary>
    public static IReadOnlyList<Name> All { get; } =
    [
        // ProofTerms' rfl and decide (docs/m4/06), and Refl: @Eq.refl α a, of_decide_eq_true P D (@Eq.refl Bool true).
        TacticNames.EqRefl,
        Name.Parse("of_decide_eq_true"),
        Name.Parse("Bool"),
        Name.Parse("Bool.true"),

        // Unfold's definitional change and every replaceTargetDefEq: @id T e.
        TacticNames.Id,

        // simp's proofs (Lean's Simp/Main, Types, Rewrite, AppBuilder, reduceIte and reduceDIte; docs/m5a/05), its
        // @[congr] lemmas, and the lemmas of the default set, whose proofs it puts into the term. simp also emits True,
        // Decidable and instOfNatNat (an orphan literal folded into OfNat.ofNat), which are not roots but are in the
        // bundle as the types of the roots True.intro and Decidable.decide and through the Nat literal lemmas; and the
        // instances instance resolution finds, which are sidecar entries and so in the bundle (KTD9).
        .. SimpNames.ProofConstants,
        Name.Parse("ite_congr"),
        Name.Parse("dite_congr"),
        .. DefaultSimpSet.CuratedLemmas,
        .. DefaultSimpSet.WarrantLemmas,
    ];
}
