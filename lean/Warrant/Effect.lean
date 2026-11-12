import Std.Do.Triple.Basic
import Std.Do.Triple.SpecLemmas
import Std.Do.WP.Monad
import Std.Do.WP.SimpLemmas

/-!
The effect monad of M6's raising code (plan M6 KTD4) and the statement and proof vocabulary of its contracts: Lean's
`Std.Do` triples, weakest preconditions and `@[spec]` lemmas (KTD1, KTD2).

A C# method that can raise (KTD11) is a program in `ClrM σ α := ExceptT ClrExn (StateM σ) α`. The world `σ` is opaque:
every obligation quantifies over it, model operations leave it unchanged, and an external operation may read and change
it, so two calls of one dependency are unrelated unless a contract relates them. Because `ClrM` is an abbreviation over
Lean's transformers, `Std.Do`'s `WP` and `WPMonad` instances and `@[spec]` lemmas apply to it as they are.

Only the constants `lean/bundle-roots.txt` names enter the bundle, with their closure (KTD2). The attribute sidecar
exports the `@[spec]` attribute of every bundle constant that has one (KTD15). Nothing here carries `@[simp]`: the
semantics library's `@[simp]` lemmas join the default simp set, and these are for the VC simp set (KTD14) only.
-/
namespace Warrant

open Std.Do

/-- The exceptions a `ClrM` program raises (KTD4): one constructor per exception a model operation raises, the thrown
type's key for an explicit `throw`, and an exception propagated from a dependency. -/
inductive ClrExn where
  /-- `System.OverflowException`: checked arithmetic or narrowing, and `MinValue / -1` and `MinValue % -1` (KTD6). -/
  | overflow
  /-- `System.DivideByZeroException`: `/` or `%` with a zero divisor (KTD6). -/
  | divideByZero
  /-- `System.NullReferenceException`: a null dereference, or a null where a non-null value is required (KTD5). -/
  | nullReference
  /-- `System.InvalidOperationException`: `Value` of a null `Nullable<T>` (KTD5). -/
  | invalidOperation
  /-- A failed `Spec.Assert` (KTD16). -/
  | assertFailed
  /-- An explicit `throw`, with the thrown type's key, e.g. `T:System.ArgumentException`. -/
  | thrown (type : String)
  /-- An exception propagated from a dependency (KTD9). -/
  | external

/-- A C# computation that may raise, over an opaque world `σ` (KTD4). -/
abbrev ClrM (σ α : Type) : Type := ExceptT ClrExn (StateM σ) α

/-- Raises `e`: `MonadExceptOf.throw` of `ExceptT`, the form `Std.Do.Spec.throw_ExceptT` states. -/
abbrev ClrM.throw {σ α : Type} (e : ClrExn) : ClrM σ α := MonadExceptOf.throw e

/-- `ClrM.throw e` raises `e` and leaves the world unchanged: afterwards the exception postcondition holds at `e` exactly
when it held before. `Std.Do.Spec.throw_ExceptT` states this for every `ExceptT`, but its `WP` instance is the one a
`WPMonad` instance gives, and neither Lean's `apply` nor Warrant's unifies that with the `WP` instance instance
resolution finds for `ClrM σ` (`Std.Do.State.instWP` under `ExceptT.instWP`), which a contract's triple states. So
this, at that instance, is the rule the VC walker applies at a `throw` (KTD13). -/
@[spec] theorem ClrM.throw_spec {σ α : Type} {e : ClrExn} {Q : PostCond α (.except ClrExn (.arg σ .pure))} :
    @Triple (ClrM σ) (.except ClrExn (.arg σ .pure)) _ α (ClrM.throw e) (Q.2.1 e) Q := by
  intro s h
  exact h

/-- The exceptions a contract's exception postcondition allows (KTD12): an explicit `throw` and an exception
propagated from a dependency. Every other one is an implicit runtime exception, which the obligation excludes. -/
def ClrExn.Allowed : ClrExn → Prop
  | .thrown _ => True
  | .external => True
  | _ => False

/-! `ClrExn.Allowed` at each constructor, for the VC simp set (KTD14). -/

theorem ClrExn.allowed_overflow : ClrExn.Allowed .overflow = False := rfl
theorem ClrExn.allowed_divideByZero : ClrExn.Allowed .divideByZero = False := rfl
theorem ClrExn.allowed_nullReference : ClrExn.Allowed .nullReference = False := rfl
theorem ClrExn.allowed_invalidOperation : ClrExn.Allowed .invalidOperation = False := rfl
theorem ClrExn.allowed_assertFailed : ClrExn.Allowed .assertFailed = False := rfl
theorem ClrExn.allowed_thrown (type : String) : ClrExn.Allowed (.thrown type) = True := rfl
theorem ClrExn.allowed_external : ClrExn.Allowed .external = True := rfl

/-- The exceptions the contract of a method with `Spec.NoThrow` allows (#182): only an exception propagated from a
dependency. An explicit `throw` is excluded too, so the proof must show none is reachable under `Requires`. -/
def ClrExn.External : ClrExn → Prop
  | .external => True
  | _ => False

/-! `ClrExn.External` at each constructor, for the VC simp set (KTD14). -/

theorem ClrExn.external_overflow : ClrExn.External .overflow = False := rfl
theorem ClrExn.external_divideByZero : ClrExn.External .divideByZero = False := rfl
theorem ClrExn.external_nullReference : ClrExn.External .nullReference = False := rfl
theorem ClrExn.external_invalidOperation : ClrExn.External .invalidOperation = False := rfl
theorem ClrExn.external_assertFailed : ClrExn.External .assertFailed = False := rfl
theorem ClrExn.external_thrown (type : String) : ClrExn.External (.thrown type) = False := rfl
theorem ClrExn.external_external : ClrExn.External .external = True := rfl

/-- An exception a `Spec.NoThrow` contract allows is one every contract allows: a caller without `Spec.NoThrow` uses
the contract of a callee with it by consequence (#182). -/
theorem ClrExn.allowed_of_external {e : ClrExn} (h : ClrExn.External e) : ClrExn.Allowed e := by
  cases e with
  | external => exact True.intro
  | _ => exact h.elim

/-! Triple rules for branches (KTD13): `Std.Do` has none. The walker applies them at `ite` and `dite` and gets one
goal per branch, with the condition or its negation as a hypothesis. -/

universe u v

/-- A triple for `if c then t else e` from one for each branch under its condition. -/
theorem Triple.ite {m : Type u → Type v} {ps : PostShape.{u}} [WP m ps] {α : Type u} {c : Prop} [h : Decidable c]
    {t e : m α} {P : Assertion ps} {Q : PostCond α ps}
    (ht : c → Triple t P Q) (he : ¬c → Triple e P Q) : Triple (if c then t else e) P Q := by
  cases h with
  | isTrue hc => exact ht hc
  | isFalse hc => exact he hc

/-- A triple for `if h : c then t h else e h` from one for each branch under its condition. -/
theorem Triple.dite {m : Type u → Type v} {ps : PostShape.{u}} [WP m ps] {α : Type u} {c : Prop} [h : Decidable c]
    {t : c → m α} {e : ¬c → m α} {P : Assertion ps} {Q : PostCond α ps}
    (ht : ∀ hc : c, Triple (t hc) P Q) (he : ∀ hc : ¬c, Triple (e hc) P Q) : Triple (dite c t e) P Q := by
  cases h with
  | isTrue hc => exact ht hc
  | isFalse hc => exact he hc

end Warrant
