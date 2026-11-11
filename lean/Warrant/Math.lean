import Warrant.Effect

/-!
The modelled `System.Math` members (plan M6 U16, KTD23): `Math.Min`, `Math.Max` and `Math.Abs` on `int` and `long`.

`Math.Min(a, b)` is `a <= b ? a : b` and `Math.Max(a, b)` is `a >= b ? a : b`, as .NET defines them. Neither raises,
so both are pure, and their equations (`min_def`, `max_def`) are what the VC simp set unfolds. `Math.Abs(a)` raises
`OverflowException` for `MinValue`, whose negation does not fit, in any context; it is a `ClrM` model with an `@[spec]`
lemma in the shape of `lean/Warrant/Checked.lean`'s. Agreement with the CLR is tested in `ClrAgreementTests` (R4, R5).
-/
namespace Warrant

open Std.Do

namespace Int32

/-- `Math.Min(a, b)` on `int`. -/
def min (a b : _root_.Int32) : _root_.Int32 := if a ≤ b then a else b

theorem min_def (a b : _root_.Int32) : min a b = if a ≤ b then a else b := rfl

/-- `Math.Max(a, b)` on `int`. -/
def max (a b : _root_.Int32) : _root_.Int32 := if b ≤ a then a else b

theorem max_def (a b : _root_.Int32) : max a b = if b ≤ a then a else b := rfl

/-- `Math.Abs(a)` on `int`: `overflow` for `int.MinValue`. -/
def abs {σ : Type} (a : _root_.Int32) : ClrM σ _root_.Int32 :=
  if a = _root_.Int32.minValue then ClrM.throw .overflow else pure (if a < 0 then -a else a)

@[spec] theorem abs_spec {σ : Type} (a : _root_.Int32) {Q : PostCond _root_.Int32 (.except ClrExn (.arg σ .pure))} :
    Triple (abs a)
      (fun s => ⟨(a = _root_.Int32.minValue → (Q.2.1 .overflow s).down) ∧
        (¬a = _root_.Int32.minValue → (Q.1 (if a < 0 then -a else a) s).down)⟩) Q := by
  intro s h
  unfold abs
  split
  · exact h.1 ‹_›
  · exact h.2 ‹_›

end Int32

namespace Int64

/-- `Math.Min(a, b)` on `long`. -/
def min (a b : _root_.Int64) : _root_.Int64 := if a ≤ b then a else b

theorem min_def (a b : _root_.Int64) : min a b = if a ≤ b then a else b := rfl

/-- `Math.Max(a, b)` on `long`. -/
def max (a b : _root_.Int64) : _root_.Int64 := if b ≤ a then a else b

theorem max_def (a b : _root_.Int64) : max a b = if b ≤ a then a else b := rfl

/-- `Math.Abs(a)` on `long`: `overflow` for `long.MinValue`. -/
def abs {σ : Type} (a : _root_.Int64) : ClrM σ _root_.Int64 :=
  if a = _root_.Int64.minValue then ClrM.throw .overflow else pure (if a < 0 then -a else a)

@[spec] theorem abs_spec {σ : Type} (a : _root_.Int64) {Q : PostCond _root_.Int64 (.except ClrExn (.arg σ .pure))} :
    Triple (abs a)
      (fun s => ⟨(a = _root_.Int64.minValue → (Q.2.1 .overflow s).down) ∧
        (¬a = _root_.Int64.minValue → (Q.1 (if a < 0 then -a else a) s).down)⟩) Q := by
  intro s h
  unfold abs
  split
  · exact h.1 ‹_›
  · exact h.2 ‹_›

end Int64

end Warrant
