import Warrant.Effect

/-!
The rules of the VC walker (plan M6 KTD13, U11), stated at `ClrM σ` with the `WP` instance instance resolution finds for
it, the one a contract's triple states (U3, #211).

The walker proves a contract obligation `⦃⌜Requires⌝⦄ prog ⦃Q⦄` by moving its precondition into the context
(`Vc.pre`) and then walking `prog` with the precondition `⌜True⌝`: every fact a step learns (a branch's condition, a
model operation's case, a callee's `Ensures`) is a hypothesis of the goals after it, so the leftover VCs are plain
propositions that the VC simp set and omega read (KTD14). A model operation's `@[spec]` lemma states its precondition as
one proposition at each world (`lean/Warrant/Checked.lean`); `Vc.spec` asks for it at every world, and where that
proposition reaches the rest of the program, `wp⟦k⟧ Q s`, `Vc.resume` turns it back into a triple for `k`. Each rule
is `Std.Do`'s, re-stated so the walker can apply it with Warrant's `Apply` (#212): none of them needs a reduction step
between it and the next one beyond β and projections.

These are proved in Lean and re-checked by the kernel like every bundle theorem; the walker that applies them is
untrusted (design D11).
-/
namespace Warrant

namespace Vc

open Std.Do

/-- A postcondition of a `ClrM σ` program. -/
abbrev Post (σ α : Type) : Type := PostCond α (.except ClrExn (.arg σ .pure))

variable {σ α β : Type}

/-- The precondition as a hypothesis: the walker proves the rest under `p` with the precondition `⌜True⌝`. -/
theorem pre {x : ClrM σ α} {p : Prop} {Q : Post σ α} (h : p → ⦃⌜True⌝⦄ x ⦃Q⦄) : ⦃⌜p⌝⦄ x ⦃Q⦄ := by
  intro s hp
  exact h hp s True.intro

/-- A spec lemma `⦃P⦄ x ⦃Q⦄` whose precondition holds at every world proves `x` from `⌜True⌝`. -/
theorem spec {x : ClrM σ α} {P : Assertion (.except ClrExn (.arg σ .pure))} {Q : Post σ α}
    (hx : ⦃P⦄ x ⦃Q⦄) (h : ∀ s, (P s).down) : ⦃⌜True⌝⦄ x ⦃Q⦄ := by
  intro s _
  exact hx s (h s)

/-- Where a spec lemma's precondition reaches the rest of the program, a triple for it proves its weakest precondition. -/
theorem resume {x : ClrM σ α} {Q : Post σ α} (s : σ) (h : ⦃⌜True⌝⦄ x ⦃Q⦄) : (wp⟦x⟧ Q s).down :=
  h s True.intro

/-- `x >>= f`: `x` with the postcondition `f`'s weakest precondition (`Std.Do.Spec.bind`). -/
theorem bind {x : ClrM σ α} {f : α → ClrM σ β} {Q : Post σ β}
    (h : ⦃⌜True⌝⦄ x ⦃(fun a => wp⟦f a⟧ Q, Q.2)⦄) : ⦃⌜True⌝⦄ (x >>= f) ⦃Q⦄ :=
  Spec.bind' h

/-- `pure a`: the normal postcondition at `a` (`Std.Do.Spec.pure`). -/
theorem pure {a : α} {Q : Post σ α} (h : ∀ s, (Q.1 a s).down) : ⦃⌜True⌝⦄ (Pure.pure a : ClrM σ α) ⦃Q⦄ :=
  spec Spec.pure h

/-- `throw e`: the exception postcondition at `e` (`Warrant.ClrM.throw_spec`, #211). -/
theorem throw {e : ClrExn} {Q : Post σ α} (h : ∀ s, (Q.2.1 e s).down) : ⦃⌜True⌝⦄ (ClrM.throw e : ClrM σ α) ⦃Q⦄ :=
  spec ClrM.throw_spec h

/-- `Spec.Assert(c)`'s check node (KTD16): `c` is a VC, and the rest is proved knowing it. -/
theorem assert {c : Prop} [h : Decidable c] {t e : ClrM σ α} {Q : Post σ α}
    (hc : c) (ht : c → ⦃⌜True⌝⦄ t ⦃Q⦄) : ⦃⌜True⌝⦄ (if c then t else e) ⦃Q⦄ := by
  cases h with
  | isTrue _ => exact ht hc
  | isFalse hn => exact absurd hc hn

/-- `match o with | none => n | some v => s v`, as the monadic translation emits it: one goal per case. -/
theorem optionRec {γ : Type} {o : Option γ} {n : ClrM σ α} {s : γ → ClrM σ α} {Q : Post σ α}
    (hn : o = none → ⦃⌜True⌝⦄ n ⦃Q⦄) (hs : ∀ v, o = some v → ⦃⌜True⌝⦄ s v ⦃Q⦄) :
    ⦃⌜True⌝⦄ (Option.rec (motive := fun _ => ClrM σ α) n s o) ⦃Q⦄ := by
  cases o with
  | none => exact hn rfl
  | some v => exact hs v rfl

/-- A verified callee's proved contract (KTD12) at its call: its `Requires` is a VC, its `Ensures` a hypothesis of the
rest, and an exception it may raise is one the caller's contract allows too. -/
theorem call {x : ClrM σ α} {p : Prop} {ok : α → Prop} {Q : Post σ α}
    (hx : ⦃⌜p⌝⦄ x ⦃(fun r => ⌜ok r⌝, fun e => ⌜ClrExn.Allowed e⌝, ())⦄) (hp : p)
    (hok : ∀ r, ok r → ∀ s, (Q.1 r s).down) (he : ∀ e, ClrExn.Allowed e → ∀ s, (Q.2.1 e s).down) :
    ⦃⌜True⌝⦄ x ⦃Q⦄ := by
  apply Triple.entails_wp_of_pre_post hx
  · intro _ _
    exact hp
  · apply PostCond.entails.mk
    · intro r s h
      exact hok r h s
    · exact ⟨fun e s h => he e h s, True.intro⟩

end Vc

end Warrant
