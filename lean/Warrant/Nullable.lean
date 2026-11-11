import Warrant.Effect

/-!
C#'s nullable values in `ClrM` (plan M6 U16, KTD5). Null is a value, not an effect: `int?`, `long?` and a nullable
reference to a record or closed class are `Option T`, `null` is `none`, and converting a `T` to `T?` is `some`.

Two reads raise, and each is a model operation here:

- `Value` of a `Nullable<T>`, and the explicit conversion `(T)x` from it, raise `InvalidOperationException` on null
  (`Nullable.value`);
- a value of static type `T?` used where a non-nullable `T` is required (a call argument, a returned value, the
  receiver of a member access such as `p.Id`) raises `NullReferenceException` on null (`Nullable.nonNull`), which is
  the unwrap check node of KTD5.

`??` and `GetValueOrDefault()` never raise: `Nullable.coalesce x d` is `x`'s value, or `d` when `x` is null.
`GetValueOrDefault()` is `coalesce x 0` on `int?` and `long?`.

Each raising model has an `@[spec]` lemma in the shape of `lean/Warrant/Checked.lean`'s: its precondition at world `s`
is one proposition stating the exception condition for the raising case and the normal postcondition for the value
otherwise, at the unchanged world. `coalesce` is pure and has its two equations instead. Agreement with the CLR is
tested in `ClrAgreementTests` (R5).
-/
namespace Warrant

namespace Nullable

open Std.Do

/-- `x.Value`, or `(T)x`, on a `Nullable<T>`: `invalidOperation` on null. -/
def value {σ α : Type} (x : Option α) : ClrM σ α :=
  match x with
  | some v => pure v
  | none => ClrM.throw .invalidOperation

@[spec] theorem value_spec {σ α : Type} (x : Option α) {Q : PostCond α (.except ClrExn (.arg σ .pure))} :
    Triple (value x : ClrM σ α)
      (fun s => ⟨(x = none → (Q.2.1 .invalidOperation s).down) ∧ (∀ v, x = some v → (Q.1 v s).down)⟩) Q := by
  intro s h
  cases x with
  | none => exact h.1 rfl
  | some v => exact h.2 v rfl

/-- A `T?` used where a non-nullable `T` is required, including the receiver of a member access: `nullReference` on
null (KTD5). -/
def nonNull {σ α : Type} (x : Option α) : ClrM σ α :=
  match x with
  | some v => pure v
  | none => ClrM.throw .nullReference

@[spec] theorem nonNull_spec {σ α : Type} (x : Option α) {Q : PostCond α (.except ClrExn (.arg σ .pure))} :
    Triple (nonNull x : ClrM σ α)
      (fun s => ⟨(x = none → (Q.2.1 .nullReference s).down) ∧ (∀ v, x = some v → (Q.1 v s).down)⟩) Q := by
  intro s h
  cases x with
  | none => exact h.1 rfl
  | some v => exact h.2 v rfl

/-- `x ?? d`, and `x.GetValueOrDefault(d)`: `x`'s value, or `d` when `x` is null. -/
def coalesce {α : Type} (x : Option α) (d : α) : α :=
  match x with
  | some v => v
  | none => d

theorem coalesce_some {α : Type} (v d : α) : coalesce (some v) d = v := rfl

theorem coalesce_none {α : Type} (d : α) : coalesce none d = d := rfl

end Nullable

end Warrant
