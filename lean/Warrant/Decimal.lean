import Warrant.Effect

/-!
C#'s `decimal` (plan M6 U4, KTD7): the minimal model M6 needs. These definitions are TRUSTED (#117): nothing proves
them right. Each is kept small enough to read against the CLR, and `ClrAgreementTests` compares every one with the
CLR's own `decimal` arithmetic on the same inputs, by representation (sign, mantissa and scale), on boundary and random
operands (R5). The lemmas below are proved, and the kernel checks them with the bundle.

## The model

- A `decimal` is `(-1)^negative × mantissa × 10^-scale`, with a natural mantissa below 2^96 and a scale from 0 to 28,
  exactly as the CLR stores it. `1.0m` and `1.00m` are different values, and so are `0m` and negative zero `-0m`.
- `units d` is `d`'s value in units of 10^-28, the finest scale, so two values compare as integers. Equality (`eq`,
  C#'s `==`) and order (`<`, `<=`) compare values: `1.0m == 1.00m` and `-0m == 0m`.
- Unary `-` flips the sign, so `-0m` is negative zero. It never raises.
- `a + b` computes the exact sum at the larger operand scale. When its mantissa fits in 96 bits, that is the result.
  Otherwise the exact sum is rounded once, half to even, at the largest smaller scale whose rounded mantissa fits, and
  the sum raises `overflow` only when even its value rounded at scale 0 does not fit. A sum that is exactly zero is
  negative zero or zero as the CLR's `DecAddSub` makes it: the sign of the operand with the smaller scale (the first
  operand's at equal scales), unless that operand is itself zero and the scales differ, when the sum is the other
  operand. `a - b` is `a + (-b)`, as in the CLR. Both raise in any context (KTD11).
- `Math.Min`, `Math.Max` and `Math.Abs` on `decimal` are in `lean/Warrant/Math.lean`.

Multiplication, division and explicit rounding are not modelled (M7).
-/
namespace Warrant

/-- A C# `decimal`: `(-1)^negative × mantissa × 10^-scale`, with a 96-bit mantissa and a scale from 0 to 28 (KTD7). -/
structure Decimal where
  negative : Bool
  mantissa : Nat
  scale : Nat
  mantissa_lt : mantissa < 2 ^ 96
  scale_le : scale ≤ 28

namespace Decimal

open Std.Do

/-- A literal (a VIR `DecimalLitExpr`). The kernel checks both bounds by evaluating `Nat.ble`, so the translator states
a literal as `lit negative mantissa scale rfl rfl`. -/
def lit (negative : Bool) (mantissa scale : Nat) (hm : Nat.ble (mantissa + 1) (2 ^ 96) = true)
    (hs : Nat.ble scale 28 = true) : Decimal :=
  ⟨negative, mantissa, scale, Nat.le_of_ble_eq_true hm, Nat.le_of_ble_eq_true hs⟩

/-- The signed mantissa. -/
def num (d : Decimal) : Int := if d.negative then -(d.mantissa : Int) else d.mantissa

/-- The value in units of 10^-28: `num × 10^(28 - scale)`. -/
def units (d : Decimal) : Int := d.num * ((10 ^ (28 - d.scale) : Nat) : Int)

/-- C#'s `==` on `decimal`: equal values. -/
def eq (a b : Decimal) : Prop := a.units = b.units

instance decEq (a b : Decimal) : Decidable (eq a b) := Int.decEq a.units b.units

/-- C#'s `<` on `decimal`, by value. -/
instance instLT : LT Decimal := ⟨fun a b => a.units < b.units⟩

/-- C#'s `<=` on `decimal`, by value. -/
instance instLE : LE Decimal := ⟨fun a b => a.units ≤ b.units⟩

instance decLt (a b : Decimal) : Decidable (a < b) := Int.decLt a.units b.units

instance decLe (a b : Decimal) : Decidable (a ≤ b) := Int.decLe a.units b.units

/-- C#'s unary `-` on `decimal`: flips the sign, so `-0m` is negative zero. -/
def neg (a : Decimal) : Decimal := { a with negative := !a.negative }

/-- `n / p` rounded to the nearest natural number, ties to the even one (for `p > 0`). -/
def roundHalfEven (n p : Nat) : Nat :=
  if 2 * (n % p) < p ∨ (2 * (n % p) = p ∧ n / p % 2 = 0) then n / p else n / p + 1

/-- `(-1)^negative × n × 10^-e` rounded once, half to even, at the largest scale from `k` down to 0 whose rounded
mantissa is below 2^96 (for `k ≤ e`); `none` when even scale 0's is not. -/
def fit (negative : Bool) (n e : Nat) : (k : Nat) → k ≤ 28 → Option Decimal
  | 0, h =>
    if hm : roundHalfEven n (10 ^ (e - 0)) < 2 ^ 96 then some ⟨negative, _, 0, hm, h⟩ else none
  | k + 1, h =>
    if hm : roundHalfEven n (10 ^ (e - (k + 1))) < 2 ^ 96 then some ⟨negative, _, k + 1, hm, h⟩
    else fit negative n e k (Nat.le_of_succ_le h)

/-- The exact `a + b` as a signed mantissa at the larger operand scale, `max a.scale b.scale`. -/
def exact (a b : Decimal) : Int :=
  a.num * ((10 ^ (max a.scale b.scale - a.scale) : Nat) : Int) + b.num * ((10 ^ (max a.scale b.scale - b.scale) : Nat) : Int)

/-- The sign of an exactly zero sum (the CLR's `DecAddSub`): that of the operand with the smaller scale, the first one
at equal scales, unless the scales differ and that operand is zero, when the sum is the other operand. -/
def zeroSign (a b : Decimal) : Bool :=
  if b.scale < a.scale then (if b.mantissa = 0 then a.negative else b.negative)
  else if a.scale < b.scale then (if a.mantissa = 0 then b.negative else a.negative)
  else a.negative

/-- `a + b` on `decimal`: the exact sum at the larger scale, rounded by `fit` when it needs more than 96 bits; `none`
on overflow. -/
def sum (a b : Decimal) : Option Decimal :=
  fit (if exact a b < 0 then true else if 0 < exact a b then false else zeroSign a b) (exact a b).natAbs
    (max a.scale b.scale) (max a.scale b.scale) (Nat.max_le.mpr ⟨a.scale_le, b.scale_le⟩)

/-- C#'s `a + b` on `decimal`: `overflow` when the sum does not fit even at scale 0. -/
def add {σ : Type} (a b : Decimal) : ClrM σ Decimal :=
  match sum a b with
  | some r => pure r
  | none => ClrM.throw .overflow

/-- C#'s `a - b` on `decimal`: `a + (-b)`. -/
def sub {σ : Type} (a b : Decimal) : ClrM σ Decimal := add a (neg b)

/-! ## Spec lemmas (KTD15), in the shape of `lean/Warrant/Checked.lean`'s -/

@[spec] theorem add_spec {σ : Type} (a b : Decimal) {Q : PostCond Decimal (.except ClrExn (.arg σ .pure))} :
    Triple (add a b : ClrM σ Decimal)
      (fun s => ⟨(sum a b = none → (Q.2.1 .overflow s).down) ∧ (∀ r, sum a b = some r → (Q.1 r s).down)⟩) Q := by
  intro s h
  unfold add
  cases hs : sum a b with
  | none => exact h.1 hs
  | some r => exact h.2 r hs

@[spec] theorem sub_spec {σ : Type} (a b : Decimal) {Q : PostCond Decimal (.except ClrExn (.arg σ .pure))} :
    Triple (sub a b : ClrM σ Decimal)
      (fun s => ⟨(sum a (neg b) = none → (Q.2.1 .overflow s).down) ∧
        (∀ r, sum a (neg b) = some r → (Q.1 r s).down)⟩) Q :=
  add_spec a (neg b)

/-! ## Equality and order -/

theorem eq_iff (a b : Decimal) : eq a b ↔ a.units = b.units := Iff.rfl

theorem lt_iff (a b : Decimal) : a < b ↔ a.units < b.units := Iff.rfl

theorem le_iff (a b : Decimal) : a ≤ b ↔ a.units ≤ b.units := Iff.rfl

theorem eq_refl (a : Decimal) : eq a a := rfl

theorem eq_symm {a b : Decimal} (h : eq a b) : eq b a := h.symm

theorem eq_trans {a b c : Decimal} (h₁ : eq a b) (h₂ : eq b c) : eq a c := h₁.trans h₂

/-- Equality of `decimal` values is an equivalence. -/
theorem eq_equivalence : Equivalence eq := ⟨eq_refl, eq_symm, eq_trans⟩

theorem lt_irrefl (a : Decimal) : ¬a < a := by
  rw [lt_iff]; omega

theorem lt_trans {a b c : Decimal} (h₁ : a < b) (h₂ : b < c) : a < c := by
  rw [lt_iff] at *; omega

theorem le_refl (a : Decimal) : a ≤ a := by
  rw [le_iff]; omega

theorem le_trans {a b c : Decimal} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := by
  rw [le_iff] at *; omega

theorem le_antisymm {a b : Decimal} (h₁ : a ≤ b) (h₂ : b ≤ a) : eq a b := by
  rw [le_iff] at *; rw [eq_iff]; omega

/-- The order is total. -/
theorem le_total (a b : Decimal) : a ≤ b ∨ b ≤ a := by
  rw [le_iff, le_iff]; omega

theorem lt_trichotomy (a b : Decimal) : a < b ∨ eq a b ∨ b < a := by
  rw [lt_iff, lt_iff, eq_iff]; omega

theorem not_lt (a b : Decimal) : ¬a < b ↔ b ≤ a := by
  rw [lt_iff, le_iff]; omega

theorem not_le (a b : Decimal) : ¬a ≤ b ↔ b < a := by
  rw [lt_iff, le_iff]; omega

theorem lt_of_le_of_lt {a b c : Decimal} (h₁ : a ≤ b) (h₂ : b < c) : a < c := by
  rw [le_iff, lt_iff] at *; omega

theorem lt_of_lt_of_le {a b c : Decimal} (h₁ : a < b) (h₂ : b ≤ c) : a < c := by
  rw [le_iff, lt_iff] at *; omega

/-! ## Values of the operations -/

theorem num_neg (a : Decimal) : (neg a).num = -a.num := by
  cases a with
  | mk negative m s hm hs =>
    cases negative
    · rfl
    · exact (Int.neg_neg _).symm

theorem units_neg (a : Decimal) : (neg a).units = -a.units := by
  show (neg a).num * ((10 ^ (28 - a.scale) : Nat) : Int) = -(a.num * ((10 ^ (28 - a.scale) : Nat) : Int))
  rw [num_neg, Int.neg_mul]

/-- The exact sum's value: `exact a b` at the larger scale is `a + b`. -/
theorem exact_mul (a b : Decimal) :
    exact a b * ((10 ^ (28 - max a.scale b.scale) : Nat) : Int) = a.units + b.units := by
  have ha := a.scale_le
  have hb := b.scale_le
  have hpa : ((10 ^ (max a.scale b.scale - a.scale) : Nat) : Int) * ((10 ^ (28 - max a.scale b.scale) : Nat) : Int) =
      ((10 ^ (28 - a.scale) : Nat) : Int) := by
    rw [← Int.natCast_mul, ← Nat.pow_add]
    congr 2
    omega
  have hpb : ((10 ^ (max a.scale b.scale - b.scale) : Nat) : Int) * ((10 ^ (28 - max a.scale b.scale) : Nat) : Int) =
      ((10 ^ (28 - b.scale) : Nat) : Int) := by
    rw [← Int.natCast_mul, ← Nat.pow_add]
    congr 2
    omega
  unfold exact units
  rw [Int.add_mul, Int.mul_assoc, Int.mul_assoc, hpa, hpb]

/-- `fit` keeps a mantissa that already fits at the scale it starts from. -/
theorem fit_self {negative : Bool} {n : Nat} (h : n < 2 ^ 96) {e : Nat} (he : e ≤ 28) :
    fit negative n e e he = some ⟨negative, n, e, h, he⟩ := by
  have hr : roundHalfEven n (10 ^ (e - e)) = n := by
    simp only [roundHalfEven, Nat.sub_self, Nat.pow_zero, Nat.mod_one, Nat.div_one, Nat.mul_zero, Nat.zero_lt_one,
      true_or, ite_true]
  cases e with
  | zero => simp only [fit, hr, h, dite_eq_left]
  | succ e => simp only [fit, hr, h, dite_eq_left]

/-- The signed mantissa `sum` gives an exact sum: the sign is that of `exact a b` whenever it is not zero. -/
theorem num_of_sign (x : Int) (z : Bool) :
    (if (if x < 0 then true else if 0 < x then false else z) = true then -(x.natAbs : Int) else (x.natAbs : Int)) = x := by
  by_cases h1 : x < 0
  · rw [ite_eq_left h1, ite_eq_left rfl]; omega
  · rw [ite_eq_right h1]
    by_cases h2 : 0 < x
    · rw [ite_eq_left h2, ite_eq_right Bool.false_ne_true]; omega
    · rw [ite_eq_right h2]; split <;> omega

/-- When the exact sum's mantissa fits in 96 bits, `a + b` is exact: its value is the sum of the values, at the larger
scale. -/
theorem sum_of_fits (a b : Decimal) (h : (exact a b).natAbs < 2 ^ 96) :
    ∃ r, sum a b = some r ∧ r.units = a.units + b.units ∧ r.scale = max a.scale b.scale := by
  unfold sum
  rw [fit_self h]
  refine ⟨_, rfl, ?_, rfl⟩
  rw [← exact_mul]
  show num _ * _ = _
  congr 1
  exact num_of_sign (exact a b) (zeroSign a b)

/-- `a - b < a` when `b > 0` and the subtraction is exact. Without exactness it fails: the CLR rounds
`decimal.MaxValue - 0.4m` to `decimal.MaxValue`, and the model does too. -/
theorem sub_lt_of_fits {a b r : Decimal} (hb : 0 < b.units) (h : (exact a (neg b)).natAbs < 2 ^ 96)
    (hr : sum a (neg b) = some r) : r < a := by
  obtain ⟨r', hs, hu, -⟩ := sum_of_fits a (neg b) h
  rw [hs] at hr
  cases hr
  rw [lt_iff, hu, units_neg]
  omega

end Decimal

end Warrant
