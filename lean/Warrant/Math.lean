import Warrant.Effect
import Warrant.Decimal

/-!
The modelled `System.Math` members (plan M6 U16, U4, KTD23): `Math.Min`, `Math.Max` and `Math.Abs` on `int`, `long`
and `decimal`.

`Math.Min(a, b)` is `a <= b ? a : b` and `Math.Max(a, b)` is `a >= b ? a : b`, as .NET defines them. Neither raises,
so both are pure, and their equations (`min_def`, `max_def`) are what the VC simp set unfolds. `Math.Abs(a)` raises
`OverflowException` for `MinValue`, whose negation does not fit, in any context; it is a `ClrM` model with an `@[spec]`
lemma in the shape of `lean/Warrant/Checked.lean`'s.

On `decimal` (M6 U4), `Math.Min` and `Math.Max` compare values (`lean/Warrant/Decimal.lean`) and return an operand
unchanged: on equal values with different scales, `Math.Min(1.0m, 1.00m)` is the second, `1.00m`, and
`Math.Max(1.0m, 1.00m)` the first, `1.0m`, as .NET's `decimal.Min` (`x < y ? x : y`) and `decimal.Max`
(`x >= y ? x : y`) do. `Math.Abs` clears the sign, negative zero included, and never raises. These definitions are
trusted, as the decimal model's are. Agreement with the CLR is tested in `ClrAgreementTests` (R4, R5).
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

namespace Decimal

/-- `Math.Min(a, b)` on `decimal`: `a < b ? a : b` by value, so `b` on equal values. -/
def min (a b : Decimal) : Decimal := if a < b then a else b

theorem min_def (a b : Decimal) : min a b = if a < b then a else b := rfl

/-- `Math.Max(a, b)` on `decimal`: `a >= b ? a : b` by value, so `a` on equal values. -/
def max (a b : Decimal) : Decimal := if b ≤ a then a else b

theorem max_def (a b : Decimal) : max a b = if b ≤ a then a else b := rfl

/-- `Math.Abs(a)` on `decimal`: the sign cleared, with mantissa and scale unchanged. -/
def abs (a : Decimal) : Decimal := { a with negative := false }

theorem units_abs (a : Decimal) : (abs a).units = if a.units < 0 then -a.units else a.units := by
  cases a with
  | mk negative m s hm hs =>
    cases negative
    · show (m : Int) * ((10 ^ (28 - s) : Nat) : Int) =
        if (m : Int) * ((10 ^ (28 - s) : Nat) : Int) < 0 then -((m : Int) * ((10 ^ (28 - s) : Nat) : Int))
        else (m : Int) * ((10 ^ (28 - s) : Nat) : Int)
      rw [← Int.natCast_mul]
      split <;> omega
    · show (m : Int) * ((10 ^ (28 - s) : Nat) : Int) =
        if -(m : Int) * ((10 ^ (28 - s) : Nat) : Int) < 0 then -(-(m : Int) * ((10 ^ (28 - s) : Nat) : Int))
        else -(m : Int) * ((10 ^ (28 - s) : Nat) : Int)
      rw [Int.neg_mul, ← Int.natCast_mul]
      split <;> omega

end Decimal

end Warrant
