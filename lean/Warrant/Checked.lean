import Warrant.Effect

/-!
C#'s `/` and `%` on `int` and `long` (plan M6 KTD6). Both truncate toward zero, as Lean's `Int32`/`Int64`
division and remainder (`BitVec.sdiv`, `BitVec.srem`) do. Init states their integer values with `Int.tdiv` and
`Int.tmod` (`Int32.toInt_div_of_ne_left`, `toInt_div_of_ne_right`, `toInt_mod`), which Warrant's `omega` does not
read, nor `Int.sign` or `Int.natAbs`. The bridges here state them with `Int.ediv`/`Int.emod`, which `omega` reads
when the divisor is a literal, and `Int`-valued `if`s on the dividend's sign and on `MinValue / -1`, which `omega`
splits. They hold without side conditions, so the omega-prep set (docs/m5a/06) rewrites with them unconditionally:

- `x / 0` is `0` and `x % 0` is `x` in Lean; the CLR throws, and U3's model raises `divideByZero` before it calls
  Lean's operation (KTD6);
- `MinValue / -1` wraps to `MinValue` in Lean; the CLR throws, and U3's model raises `overflow` first.

None of these carries `@[simp]`; every name is a bundle root (`lean/bundle-roots.txt`).

The second half of the file is the models of C#'s raising integer operations in `ClrM` (M6 U3, KTD4, KTD6), below,
and of default-context arithmetic in a verified method that can raise, which must not overflow (#244).
-/
namespace Warrant

namespace Int32

/-- The integer value of `a / b`: truncating division, with `MinValue / -1` wrapping to `MinValue`. -/
theorem toInt_div (a b : _root_.Int32) :
    (a / b).toInt =
      if a.toInt = -2147483648 ∧ b.toInt = -1 then -2147483648
      else if 0 ≤ a.toInt then a.toInt / b.toInt else -(-a.toInt / b.toInt) := by
  split
  · next h =>
    have ha : a = _root_.Int32.minValue := _root_.Int32.toInt_inj.mp (by rw [h.1]; decide)
    have hb : b = -1 := _root_.Int32.toInt_inj.mp (by rw [h.2]; decide)
    subst ha hb
    decide
  · next h =>
    have hd : (a / b).toInt = a.toInt.tdiv b.toInt := by
      by_cases ha : a = _root_.Int32.minValue
      · apply _root_.Int32.toInt_div_of_ne_right
        intro hb
        apply h
        subst ha hb
        decide
      · exact _root_.Int32.toInt_div_of_ne_left a b ha
    rw [hd]
    split
    · exact Int.tdiv_eq_ediv_of_nonneg (by assumption)
    · rw [← Int.neg_neg a.toInt, Int.neg_tdiv, Int.neg_neg, Int.tdiv_eq_ediv_of_nonneg (by omega)]

/-- The integer value of `a % b`: the remainder takes the dividend's sign. -/
theorem toInt_mod (a b : _root_.Int32) :
    (a % b).toInt = if 0 ≤ a.toInt then a.toInt % b.toInt else -(-a.toInt % b.toInt) := by
  rw [_root_.Int32.toInt_mod]
  split
  · exact Int.tmod_eq_emod_of_nonneg (by assumption)
  · rw [← Int.neg_neg a.toInt, Int.neg_tmod, Int.neg_neg, Int.tmod_eq_emod_of_nonneg (by omega)]

end Int32

namespace Int64

/-- The integer value of `a / b`: truncating division, with `MinValue / -1` wrapping to `MinValue`. -/
theorem toInt_div (a b : _root_.Int64) :
    (a / b).toInt =
      if a.toInt = -9223372036854775808 ∧ b.toInt = -1 then -9223372036854775808
      else if 0 ≤ a.toInt then a.toInt / b.toInt else -(-a.toInt / b.toInt) := by
  split
  · next h =>
    have ha : a = _root_.Int64.minValue := _root_.Int64.toInt_inj.mp (by rw [h.1]; decide)
    have hb : b = -1 := _root_.Int64.toInt_inj.mp (by rw [h.2]; decide)
    subst ha hb
    decide
  · next h =>
    have hd : (a / b).toInt = a.toInt.tdiv b.toInt := by
      by_cases ha : a = _root_.Int64.minValue
      · apply _root_.Int64.toInt_div_of_ne_right
        intro hb
        apply h
        subst ha hb
        decide
      · exact _root_.Int64.toInt_div_of_ne_left a b ha
    rw [hd]
    split
    · exact Int.tdiv_eq_ediv_of_nonneg (by assumption)
    · rw [← Int.neg_neg a.toInt, Int.neg_tdiv, Int.neg_neg, Int.tdiv_eq_ediv_of_nonneg (by omega)]

/-- The integer value of `a % b`: the remainder takes the dividend's sign. -/
theorem toInt_mod (a b : _root_.Int64) :
    (a % b).toInt = if 0 ≤ a.toInt then a.toInt % b.toInt else -(-a.toInt % b.toInt) := by
  rw [_root_.Int64.toInt_mod]
  split
  · exact Int.tmod_eq_emod_of_nonneg (by assumption)
  · rw [← Int.neg_neg a.toInt, Int.neg_tmod, Int.neg_neg, Int.tmod_eq_emod_of_nonneg (by omega)]

end Int64

/-!
## C#'s raising integer operations in `ClrM` (M6 U3, KTD4, KTD6)

Each model tests its throwing cases and then calls Lean's operation, and leaves the world unchanged. Checked `+`, `-`,
`*` and unary `-` (in a `checked` context) and checked `long` to `int` narrowing raise `overflow` when the exact
integer result is outside the target type's range. `/` and `%` raise `divideByZero` for a zero divisor first, then
`overflow` for `MinValue / -1` and `MinValue % -1`, which the CLR throws even in unchecked code (KTD6), and otherwise
truncate as C# does.

Each model has an `@[spec]` lemma, which the sidecar exports and the VC walker looks up by head constant (KTD15). Its
precondition, at world `s`, is one proposition that states, for each throwing case, that the postcondition's
exception condition holds for that exception at the unchanged world, and otherwise that the normal postcondition holds
for Lean's result at the unchanged world. A proposition, rather than an `if` over assertions, is what the VC simp set
reduces to a goal `omega` reads (KTD14). Agreement with the CLR is tested in `ClrAgreementTests` (R5).
-/

open Std.Do

namespace Int32

/-- C#'s checked `a + b` on `int`: `overflow` when the exact result is out of range. -/
def addChecked {σ : Type} (a b : _root_.Int32) : ClrM σ _root_.Int32 :=
  if a.toInt + b.toInt < -2147483648 ∨ 2147483647 < a.toInt + b.toInt then ClrM.throw .overflow else pure (a + b)

@[spec] theorem addChecked_spec {σ : Type} (a b : _root_.Int32) {Q : PostCond _root_.Int32 (.except ClrExn (.arg σ .pure))} :
    Triple (addChecked a b)
      (fun s => ⟨(a.toInt + b.toInt < -2147483648 ∨ 2147483647 < a.toInt + b.toInt → (Q.2.1 .overflow s).down) ∧
        (¬(a.toInt + b.toInt < -2147483648 ∨ 2147483647 < a.toInt + b.toInt) → (Q.1 (a + b) s).down)⟩) Q := by
  intro s h
  unfold addChecked
  split
  · exact h.1 ‹_›
  · exact h.2 ‹_›

/-- C#'s checked `a - b` on `int`: `overflow` when the exact result is out of range. -/
def subChecked {σ : Type} (a b : _root_.Int32) : ClrM σ _root_.Int32 :=
  if a.toInt - b.toInt < -2147483648 ∨ 2147483647 < a.toInt - b.toInt then ClrM.throw .overflow else pure (a - b)

@[spec] theorem subChecked_spec {σ : Type} (a b : _root_.Int32) {Q : PostCond _root_.Int32 (.except ClrExn (.arg σ .pure))} :
    Triple (subChecked a b)
      (fun s => ⟨(a.toInt - b.toInt < -2147483648 ∨ 2147483647 < a.toInt - b.toInt → (Q.2.1 .overflow s).down) ∧
        (¬(a.toInt - b.toInt < -2147483648 ∨ 2147483647 < a.toInt - b.toInt) → (Q.1 (a - b) s).down)⟩) Q := by
  intro s h
  unfold subChecked
  split
  · exact h.1 ‹_›
  · exact h.2 ‹_›

/-- C#'s checked `a * b` on `int`: `overflow` when the exact result is out of range. -/
def mulChecked {σ : Type} (a b : _root_.Int32) : ClrM σ _root_.Int32 :=
  if a.toInt * b.toInt < -2147483648 ∨ 2147483647 < a.toInt * b.toInt then ClrM.throw .overflow else pure (a * b)

@[spec] theorem mulChecked_spec {σ : Type} (a b : _root_.Int32) {Q : PostCond _root_.Int32 (.except ClrExn (.arg σ .pure))} :
    Triple (mulChecked a b)
      (fun s => ⟨(a.toInt * b.toInt < -2147483648 ∨ 2147483647 < a.toInt * b.toInt → (Q.2.1 .overflow s).down) ∧
        (¬(a.toInt * b.toInt < -2147483648 ∨ 2147483647 < a.toInt * b.toInt) → (Q.1 (a * b) s).down)⟩) Q := by
  intro s h
  unfold mulChecked
  split
  · exact h.1 ‹_›
  · exact h.2 ‹_›

/-- C#'s checked `-a` on `int`: `overflow` when the exact result is out of range. -/
def negChecked {σ : Type} (a : _root_.Int32) : ClrM σ _root_.Int32 :=
  if -a.toInt < -2147483648 ∨ 2147483647 < -a.toInt then ClrM.throw .overflow else pure (-a)

@[spec] theorem negChecked_spec {σ : Type} (a : _root_.Int32) {Q : PostCond _root_.Int32 (.except ClrExn (.arg σ .pure))} :
    Triple (negChecked a)
      (fun s => ⟨(-a.toInt < -2147483648 ∨ 2147483647 < -a.toInt → (Q.2.1 .overflow s).down) ∧
        (¬(-a.toInt < -2147483648 ∨ 2147483647 < -a.toInt) → (Q.1 (-a) s).down)⟩) Q := by
  intro s h
  unfold negChecked
  split
  · exact h.1 ‹_›
  · exact h.2 ‹_›

/-- C#'s `a / b` on `int` (KTD6): `divideByZero` for a zero divisor, then `overflow` for
`MinValue / -1`, then Lean's truncating `/`. -/
def div {σ : Type} (a b : _root_.Int32) : ClrM σ _root_.Int32 :=
  if b = 0 then ClrM.throw .divideByZero
  else if a = _root_.Int32.minValue ∧ b = -1 then ClrM.throw .overflow
  else pure (a / b)

@[spec] theorem div_spec {σ : Type} (a b : _root_.Int32) {Q : PostCond _root_.Int32 (.except ClrExn (.arg σ .pure))} :
    Triple (div a b)
      (fun s => ⟨(b = 0 → (Q.2.1 .divideByZero s).down) ∧
        (¬b = 0 → a = _root_.Int32.minValue ∧ b = -1 → (Q.2.1 .overflow s).down) ∧
        (¬b = 0 → ¬(a = _root_.Int32.minValue ∧ b = -1) → (Q.1 (a / b) s).down)⟩) Q := by
  intro s h
  unfold div
  split
  · exact h.1 ‹_›
  · split
    · exact h.2.1 ‹_› ‹_›
    · exact h.2.2 ‹_› ‹_›

/-- C#'s `a % b` on `int` (KTD6): `divideByZero` for a zero divisor, then `overflow` for
`MinValue % -1`, then Lean's truncating `%`. -/
def rem {σ : Type} (a b : _root_.Int32) : ClrM σ _root_.Int32 :=
  if b = 0 then ClrM.throw .divideByZero
  else if a = _root_.Int32.minValue ∧ b = -1 then ClrM.throw .overflow
  else pure (a % b)

@[spec] theorem rem_spec {σ : Type} (a b : _root_.Int32) {Q : PostCond _root_.Int32 (.except ClrExn (.arg σ .pure))} :
    Triple (rem a b)
      (fun s => ⟨(b = 0 → (Q.2.1 .divideByZero s).down) ∧
        (¬b = 0 → a = _root_.Int32.minValue ∧ b = -1 → (Q.2.1 .overflow s).down) ∧
        (¬b = 0 → ¬(a = _root_.Int32.minValue ∧ b = -1) → (Q.1 (a % b) s).down)⟩) Q := by
  intro s h
  unfold rem
  split
  · exact h.1 ‹_›
  · split
    · exact h.2.1 ‹_› ‹_›
    · exact h.2.2 ‹_› ‹_›

/-! C#'s default-context `+`, `-`, `*` and unary `-` on `int` in a verified method that can raise (#244). The CLR
wraps on overflow; Warrant requires that a verified method's own arithmetic never does unless it is written `unchecked`.
So each model fails, as a `Spec.Assert` does (`assertFailed`, which no contract allows), where the exact result is out
of range, and otherwise is Lean's wrapping operation, which is then the exact result. Its `@[spec]` lemma says so, so
the goals after it read the value as a sum, difference or product rather than through `Int.bmod`, whose case split
`omega` cannot always close. The differential harness skips an input where the model fails a `Spec.Assert` (#186), so
it compares every input where no such operation overflows. -/

/-- `a + b` is exact where it does not overflow. -/
theorem toInt_add_of_range {a b : _root_.Int32} (h : ¬(a.toInt + b.toInt < -2147483648 ∨ 2147483647 < a.toInt + b.toInt)) : (a + b).toInt = a.toInt + b.toInt := by
  rw [_root_.Int32.toInt_add]
  exact Int.bmod_eq_of_le (by omega) (by omega)

/-- C#'s default-context `a + b` on `int` (#244): `assertFailed` when the exact result is out of range. -/
def addImplicit {σ : Type} (a b : _root_.Int32) : ClrM σ _root_.Int32 :=
  if a.toInt + b.toInt < -2147483648 ∨ 2147483647 < a.toInt + b.toInt then ClrM.throw .assertFailed else pure (a + b)

@[spec] theorem addImplicit_spec {σ : Type} (a b : _root_.Int32) {Q : PostCond _root_.Int32 (.except ClrExn (.arg σ .pure))} :
    Triple (addImplicit a b)
      (fun s => ⟨(a.toInt + b.toInt < -2147483648 ∨ 2147483647 < a.toInt + b.toInt → (Q.2.1 .assertFailed s).down) ∧
        (¬(a.toInt + b.toInt < -2147483648 ∨ 2147483647 < a.toInt + b.toInt) → (a + b).toInt = a.toInt + b.toInt → (Q.1 (a + b) s).down)⟩) Q := by
  intro s h
  unfold addImplicit
  split
  · exact h.1 ‹_›
  · exact h.2 ‹_› (toInt_add_of_range ‹_›)

/-- `a - b` is exact where it does not overflow. -/
theorem toInt_sub_of_range {a b : _root_.Int32} (h : ¬(a.toInt - b.toInt < -2147483648 ∨ 2147483647 < a.toInt - b.toInt)) : (a - b).toInt = a.toInt - b.toInt := by
  rw [_root_.Int32.toInt_sub]
  exact Int.bmod_eq_of_le (by omega) (by omega)

/-- C#'s default-context `a - b` on `int` (#244): `assertFailed` when the exact result is out of range. -/
def subImplicit {σ : Type} (a b : _root_.Int32) : ClrM σ _root_.Int32 :=
  if a.toInt - b.toInt < -2147483648 ∨ 2147483647 < a.toInt - b.toInt then ClrM.throw .assertFailed else pure (a - b)

@[spec] theorem subImplicit_spec {σ : Type} (a b : _root_.Int32) {Q : PostCond _root_.Int32 (.except ClrExn (.arg σ .pure))} :
    Triple (subImplicit a b)
      (fun s => ⟨(a.toInt - b.toInt < -2147483648 ∨ 2147483647 < a.toInt - b.toInt → (Q.2.1 .assertFailed s).down) ∧
        (¬(a.toInt - b.toInt < -2147483648 ∨ 2147483647 < a.toInt - b.toInt) → (a - b).toInt = a.toInt - b.toInt → (Q.1 (a - b) s).down)⟩) Q := by
  intro s h
  unfold subImplicit
  split
  · exact h.1 ‹_›
  · exact h.2 ‹_› (toInt_sub_of_range ‹_›)

/-- `a * b` is exact where it does not overflow. -/
theorem toInt_mul_of_range {a b : _root_.Int32} (h : ¬(a.toInt * b.toInt < -2147483648 ∨ 2147483647 < a.toInt * b.toInt)) : (a * b).toInt = a.toInt * b.toInt := by
  rw [_root_.Int32.toInt_mul]
  exact Int.bmod_eq_of_le (by omega) (by omega)

/-- C#'s default-context `a * b` on `int` (#244): `assertFailed` when the exact result is out of range. -/
def mulImplicit {σ : Type} (a b : _root_.Int32) : ClrM σ _root_.Int32 :=
  if a.toInt * b.toInt < -2147483648 ∨ 2147483647 < a.toInt * b.toInt then ClrM.throw .assertFailed else pure (a * b)

@[spec] theorem mulImplicit_spec {σ : Type} (a b : _root_.Int32) {Q : PostCond _root_.Int32 (.except ClrExn (.arg σ .pure))} :
    Triple (mulImplicit a b)
      (fun s => ⟨(a.toInt * b.toInt < -2147483648 ∨ 2147483647 < a.toInt * b.toInt → (Q.2.1 .assertFailed s).down) ∧
        (¬(a.toInt * b.toInt < -2147483648 ∨ 2147483647 < a.toInt * b.toInt) → (a * b).toInt = a.toInt * b.toInt → (Q.1 (a * b) s).down)⟩) Q := by
  intro s h
  unfold mulImplicit
  split
  · exact h.1 ‹_›
  · exact h.2 ‹_› (toInt_mul_of_range ‹_›)

/-- `-a` is exact where it does not overflow. -/
theorem toInt_neg_of_range {a : _root_.Int32} (h : ¬(-a.toInt < -2147483648 ∨ 2147483647 < -a.toInt)) : (-a).toInt = -a.toInt := by
  rw [_root_.Int32.toInt_neg]
  exact Int.bmod_eq_of_le (by omega) (by omega)

/-- C#'s default-context `-a` on `int` (#244): `assertFailed` when the exact result is out of range. -/
def negImplicit {σ : Type} (a : _root_.Int32) : ClrM σ _root_.Int32 :=
  if -a.toInt < -2147483648 ∨ 2147483647 < -a.toInt then ClrM.throw .assertFailed else pure (-a)

@[spec] theorem negImplicit_spec {σ : Type} (a : _root_.Int32) {Q : PostCond _root_.Int32 (.except ClrExn (.arg σ .pure))} :
    Triple (negImplicit a)
      (fun s => ⟨(-a.toInt < -2147483648 ∨ 2147483647 < -a.toInt → (Q.2.1 .assertFailed s).down) ∧
        (¬(-a.toInt < -2147483648 ∨ 2147483647 < -a.toInt) → (-a).toInt = -a.toInt → (Q.1 (-a) s).down)⟩) Q := by
  intro s h
  unfold negImplicit
  split
  · exact h.1 ‹_›
  · exact h.2 ‹_› (toInt_neg_of_range ‹_›)

end Int32

namespace Int64

/-- C#'s checked `a + b` on `long`: `overflow` when the exact result is out of range. -/
def addChecked {σ : Type} (a b : _root_.Int64) : ClrM σ _root_.Int64 :=
  if a.toInt + b.toInt < -9223372036854775808 ∨ 9223372036854775807 < a.toInt + b.toInt then ClrM.throw .overflow else pure (a + b)

@[spec] theorem addChecked_spec {σ : Type} (a b : _root_.Int64) {Q : PostCond _root_.Int64 (.except ClrExn (.arg σ .pure))} :
    Triple (addChecked a b)
      (fun s => ⟨(a.toInt + b.toInt < -9223372036854775808 ∨ 9223372036854775807 < a.toInt + b.toInt → (Q.2.1 .overflow s).down) ∧
        (¬(a.toInt + b.toInt < -9223372036854775808 ∨ 9223372036854775807 < a.toInt + b.toInt) → (Q.1 (a + b) s).down)⟩) Q := by
  intro s h
  unfold addChecked
  split
  · exact h.1 ‹_›
  · exact h.2 ‹_›

/-- C#'s checked `a - b` on `long`: `overflow` when the exact result is out of range. -/
def subChecked {σ : Type} (a b : _root_.Int64) : ClrM σ _root_.Int64 :=
  if a.toInt - b.toInt < -9223372036854775808 ∨ 9223372036854775807 < a.toInt - b.toInt then ClrM.throw .overflow else pure (a - b)

@[spec] theorem subChecked_spec {σ : Type} (a b : _root_.Int64) {Q : PostCond _root_.Int64 (.except ClrExn (.arg σ .pure))} :
    Triple (subChecked a b)
      (fun s => ⟨(a.toInt - b.toInt < -9223372036854775808 ∨ 9223372036854775807 < a.toInt - b.toInt → (Q.2.1 .overflow s).down) ∧
        (¬(a.toInt - b.toInt < -9223372036854775808 ∨ 9223372036854775807 < a.toInt - b.toInt) → (Q.1 (a - b) s).down)⟩) Q := by
  intro s h
  unfold subChecked
  split
  · exact h.1 ‹_›
  · exact h.2 ‹_›

/-- C#'s checked `a * b` on `long`: `overflow` when the exact result is out of range. -/
def mulChecked {σ : Type} (a b : _root_.Int64) : ClrM σ _root_.Int64 :=
  if a.toInt * b.toInt < -9223372036854775808 ∨ 9223372036854775807 < a.toInt * b.toInt then ClrM.throw .overflow else pure (a * b)

@[spec] theorem mulChecked_spec {σ : Type} (a b : _root_.Int64) {Q : PostCond _root_.Int64 (.except ClrExn (.arg σ .pure))} :
    Triple (mulChecked a b)
      (fun s => ⟨(a.toInt * b.toInt < -9223372036854775808 ∨ 9223372036854775807 < a.toInt * b.toInt → (Q.2.1 .overflow s).down) ∧
        (¬(a.toInt * b.toInt < -9223372036854775808 ∨ 9223372036854775807 < a.toInt * b.toInt) → (Q.1 (a * b) s).down)⟩) Q := by
  intro s h
  unfold mulChecked
  split
  · exact h.1 ‹_›
  · exact h.2 ‹_›

/-- C#'s checked `-a` on `long`: `overflow` when the exact result is out of range. -/
def negChecked {σ : Type} (a : _root_.Int64) : ClrM σ _root_.Int64 :=
  if -a.toInt < -9223372036854775808 ∨ 9223372036854775807 < -a.toInt then ClrM.throw .overflow else pure (-a)

@[spec] theorem negChecked_spec {σ : Type} (a : _root_.Int64) {Q : PostCond _root_.Int64 (.except ClrExn (.arg σ .pure))} :
    Triple (negChecked a)
      (fun s => ⟨(-a.toInt < -9223372036854775808 ∨ 9223372036854775807 < -a.toInt → (Q.2.1 .overflow s).down) ∧
        (¬(-a.toInt < -9223372036854775808 ∨ 9223372036854775807 < -a.toInt) → (Q.1 (-a) s).down)⟩) Q := by
  intro s h
  unfold negChecked
  split
  · exact h.1 ‹_›
  · exact h.2 ‹_›

/-- C#'s `a / b` on `long` (KTD6): `divideByZero` for a zero divisor, then `overflow` for
`MinValue / -1`, then Lean's truncating `/`. -/
def div {σ : Type} (a b : _root_.Int64) : ClrM σ _root_.Int64 :=
  if b = 0 then ClrM.throw .divideByZero
  else if a = _root_.Int64.minValue ∧ b = -1 then ClrM.throw .overflow
  else pure (a / b)

@[spec] theorem div_spec {σ : Type} (a b : _root_.Int64) {Q : PostCond _root_.Int64 (.except ClrExn (.arg σ .pure))} :
    Triple (div a b)
      (fun s => ⟨(b = 0 → (Q.2.1 .divideByZero s).down) ∧
        (¬b = 0 → a = _root_.Int64.minValue ∧ b = -1 → (Q.2.1 .overflow s).down) ∧
        (¬b = 0 → ¬(a = _root_.Int64.minValue ∧ b = -1) → (Q.1 (a / b) s).down)⟩) Q := by
  intro s h
  unfold div
  split
  · exact h.1 ‹_›
  · split
    · exact h.2.1 ‹_› ‹_›
    · exact h.2.2 ‹_› ‹_›

/-- C#'s `a % b` on `long` (KTD6): `divideByZero` for a zero divisor, then `overflow` for
`MinValue % -1`, then Lean's truncating `%`. -/
def rem {σ : Type} (a b : _root_.Int64) : ClrM σ _root_.Int64 :=
  if b = 0 then ClrM.throw .divideByZero
  else if a = _root_.Int64.minValue ∧ b = -1 then ClrM.throw .overflow
  else pure (a % b)

@[spec] theorem rem_spec {σ : Type} (a b : _root_.Int64) {Q : PostCond _root_.Int64 (.except ClrExn (.arg σ .pure))} :
    Triple (rem a b)
      (fun s => ⟨(b = 0 → (Q.2.1 .divideByZero s).down) ∧
        (¬b = 0 → a = _root_.Int64.minValue ∧ b = -1 → (Q.2.1 .overflow s).down) ∧
        (¬b = 0 → ¬(a = _root_.Int64.minValue ∧ b = -1) → (Q.1 (a % b) s).down)⟩) Q := by
  intro s h
  unfold rem
  split
  · exact h.1 ‹_›
  · split
    · exact h.2.1 ‹_› ‹_›
    · exact h.2.2 ‹_› ‹_›

/-- C#'s checked `(int)x` on `long`: `overflow` when `x` is outside `int`'s range. -/
def toInt32Checked {σ : Type} (x : _root_.Int64) : ClrM σ _root_.Int32 :=
  if x.toInt < -2147483648 ∨ 2147483647 < x.toInt then ClrM.throw .overflow else pure x.toInt32

@[spec] theorem toInt32Checked_spec {σ : Type} (x : _root_.Int64) {Q : PostCond _root_.Int32 (.except ClrExn (.arg σ .pure))} :
    Triple (toInt32Checked x)
      (fun s => ⟨(x.toInt < -2147483648 ∨ 2147483647 < x.toInt → (Q.2.1 .overflow s).down) ∧
        (¬(x.toInt < -2147483648 ∨ 2147483647 < x.toInt) → (Q.1 x.toInt32 s).down)⟩) Q := by
  intro s h
  unfold toInt32Checked
  split
  · exact h.1 ‹_›
  · exact h.2 ‹_›

/-! C#'s default-context `+`, `-`, `*` and unary `-` on `long` in a verified method that can raise (#244). The CLR
wraps on overflow; Warrant requires that a verified method's own arithmetic never does unless it is written `unchecked`.
So each model fails, as a `Spec.Assert` does (`assertFailed`, which no contract allows), where the exact result is out
of range, and otherwise is Lean's wrapping operation, which is then the exact result. Its `@[spec]` lemma says so, so
the goals after it read the value as a sum, difference or product rather than through `Int.bmod`, whose case split
`omega` cannot always close. The differential harness skips an input where the model fails a `Spec.Assert` (#186), so
it compares every input where no such operation overflows. -/

/-- `a + b` is exact where it does not overflow. -/
theorem toInt_add_of_range {a b : _root_.Int64} (h : ¬(a.toInt + b.toInt < -9223372036854775808 ∨ 9223372036854775807 < a.toInt + b.toInt)) : (a + b).toInt = a.toInt + b.toInt := by
  rw [_root_.Int64.toInt_add]
  exact Int.bmod_eq_of_le (by omega) (by omega)

/-- C#'s default-context `a + b` on `long` (#244): `assertFailed` when the exact result is out of range. -/
def addImplicit {σ : Type} (a b : _root_.Int64) : ClrM σ _root_.Int64 :=
  if a.toInt + b.toInt < -9223372036854775808 ∨ 9223372036854775807 < a.toInt + b.toInt then ClrM.throw .assertFailed else pure (a + b)

@[spec] theorem addImplicit_spec {σ : Type} (a b : _root_.Int64) {Q : PostCond _root_.Int64 (.except ClrExn (.arg σ .pure))} :
    Triple (addImplicit a b)
      (fun s => ⟨(a.toInt + b.toInt < -9223372036854775808 ∨ 9223372036854775807 < a.toInt + b.toInt → (Q.2.1 .assertFailed s).down) ∧
        (¬(a.toInt + b.toInt < -9223372036854775808 ∨ 9223372036854775807 < a.toInt + b.toInt) → (a + b).toInt = a.toInt + b.toInt → (Q.1 (a + b) s).down)⟩) Q := by
  intro s h
  unfold addImplicit
  split
  · exact h.1 ‹_›
  · exact h.2 ‹_› (toInt_add_of_range ‹_›)

/-- `a - b` is exact where it does not overflow. -/
theorem toInt_sub_of_range {a b : _root_.Int64} (h : ¬(a.toInt - b.toInt < -9223372036854775808 ∨ 9223372036854775807 < a.toInt - b.toInt)) : (a - b).toInt = a.toInt - b.toInt := by
  rw [_root_.Int64.toInt_sub]
  exact Int.bmod_eq_of_le (by omega) (by omega)

/-- C#'s default-context `a - b` on `long` (#244): `assertFailed` when the exact result is out of range. -/
def subImplicit {σ : Type} (a b : _root_.Int64) : ClrM σ _root_.Int64 :=
  if a.toInt - b.toInt < -9223372036854775808 ∨ 9223372036854775807 < a.toInt - b.toInt then ClrM.throw .assertFailed else pure (a - b)

@[spec] theorem subImplicit_spec {σ : Type} (a b : _root_.Int64) {Q : PostCond _root_.Int64 (.except ClrExn (.arg σ .pure))} :
    Triple (subImplicit a b)
      (fun s => ⟨(a.toInt - b.toInt < -9223372036854775808 ∨ 9223372036854775807 < a.toInt - b.toInt → (Q.2.1 .assertFailed s).down) ∧
        (¬(a.toInt - b.toInt < -9223372036854775808 ∨ 9223372036854775807 < a.toInt - b.toInt) → (a - b).toInt = a.toInt - b.toInt → (Q.1 (a - b) s).down)⟩) Q := by
  intro s h
  unfold subImplicit
  split
  · exact h.1 ‹_›
  · exact h.2 ‹_› (toInt_sub_of_range ‹_›)

/-- `a * b` is exact where it does not overflow. -/
theorem toInt_mul_of_range {a b : _root_.Int64} (h : ¬(a.toInt * b.toInt < -9223372036854775808 ∨ 9223372036854775807 < a.toInt * b.toInt)) : (a * b).toInt = a.toInt * b.toInt := by
  rw [_root_.Int64.toInt_mul]
  exact Int.bmod_eq_of_le (by omega) (by omega)

/-- C#'s default-context `a * b` on `long` (#244): `assertFailed` when the exact result is out of range. -/
def mulImplicit {σ : Type} (a b : _root_.Int64) : ClrM σ _root_.Int64 :=
  if a.toInt * b.toInt < -9223372036854775808 ∨ 9223372036854775807 < a.toInt * b.toInt then ClrM.throw .assertFailed else pure (a * b)

@[spec] theorem mulImplicit_spec {σ : Type} (a b : _root_.Int64) {Q : PostCond _root_.Int64 (.except ClrExn (.arg σ .pure))} :
    Triple (mulImplicit a b)
      (fun s => ⟨(a.toInt * b.toInt < -9223372036854775808 ∨ 9223372036854775807 < a.toInt * b.toInt → (Q.2.1 .assertFailed s).down) ∧
        (¬(a.toInt * b.toInt < -9223372036854775808 ∨ 9223372036854775807 < a.toInt * b.toInt) → (a * b).toInt = a.toInt * b.toInt → (Q.1 (a * b) s).down)⟩) Q := by
  intro s h
  unfold mulImplicit
  split
  · exact h.1 ‹_›
  · exact h.2 ‹_› (toInt_mul_of_range ‹_›)

/-- `-a` is exact where it does not overflow. -/
theorem toInt_neg_of_range {a : _root_.Int64} (h : ¬(-a.toInt < -9223372036854775808 ∨ 9223372036854775807 < -a.toInt)) : (-a).toInt = -a.toInt := by
  rw [_root_.Int64.toInt_neg]
  exact Int.bmod_eq_of_le (by omega) (by omega)

/-- C#'s default-context `-a` on `long` (#244): `assertFailed` when the exact result is out of range. -/
def negImplicit {σ : Type} (a : _root_.Int64) : ClrM σ _root_.Int64 :=
  if -a.toInt < -9223372036854775808 ∨ 9223372036854775807 < -a.toInt then ClrM.throw .assertFailed else pure (-a)

@[spec] theorem negImplicit_spec {σ : Type} (a : _root_.Int64) {Q : PostCond _root_.Int64 (.except ClrExn (.arg σ .pure))} :
    Triple (negImplicit a)
      (fun s => ⟨(-a.toInt < -9223372036854775808 ∨ 9223372036854775807 < -a.toInt → (Q.2.1 .assertFailed s).down) ∧
        (¬(-a.toInt < -9223372036854775808 ∨ 9223372036854775807 < -a.toInt) → (-a).toInt = -a.toInt → (Q.1 (-a) s).down)⟩) Q := by
  intro s h
  unfold negImplicit
  split
  · exact h.1 ‹_›
  · exact h.2 ‹_› (toInt_neg_of_range ‹_›)

end Int64

end Warrant
