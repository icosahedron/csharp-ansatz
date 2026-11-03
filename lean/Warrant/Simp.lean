/-!
Lemmas for Warrant's `simp` (plan KTD11, docs/m5a/05). Init has no lemma that splits an
equation whose left side is an `if`, and Warrant does not port Lean's ground arithmetic
simprocs, so `Int32`/`Int64` literals under `toInt` are rewritten by the literal lemmas here,
whose left side is marked `no_index`: a numeral in a goal keys as the number itself in a
discrimination tree, so a left side `OfNat.ofNat n` with a variable `n` would never be found.
Their side condition is discharged by `decide`.

None of these carries `@[simp]`: the C# default simp set (U17) and the omega-prep set (U18)
name them explicitly, and every name is a bundle root (`lean/bundle-roots.txt`).
-/
namespace Warrant

/-- An equation whose left side is an `if` holds in one of its branches. -/
theorem ite_eq_iff {p : Prop} [Decidable p] {α : Sort u} {a b c : α} :
    (if p then a else b) = c ↔ (p ∧ a = c) ∨ (¬p ∧ b = c) := by
  by_cases h : p <;> simp [h]

/-- An equation whose left side is a dependent `if` holds in one of its branches. -/
theorem dite_eq_iff {p : Prop} [Decidable p] {α : Sort u} {a : p → α} {b : ¬p → α} {c : α} :
    (if h : p then a h else b h) = c ↔ (∃ h : p, a h = c) ∨ (∃ h : ¬p, b h = c) := by
  by_cases h : p <;> simp [h]

namespace Int32

/-- A non-negative `int` literal's integer value is the literal. -/
theorem toInt_ofNat_lit (n : Nat) (h : n < 2 ^ 31) :
    (no_index (OfNat.ofNat n : _root_.Int32)).toInt = n :=
  _root_.Int32.toInt_ofNat_of_lt h

/-- A negative `int` literal's integer value is the literal, down to `int.MinValue`. -/
theorem toInt_neg_ofNat_lit (n : Nat) (h : n ≤ 2 ^ 31) :
    (-(no_index (OfNat.ofNat n : _root_.Int32))).toInt = -n := by
  rw [_root_.Int32.toInt_neg, _root_.Int32.toInt_ofNat]
  simp only [Int.bmod_def, _root_.Int32.size]
  split <;> split <;> omega

end Int32

namespace Int64

/-- A non-negative `long` literal's integer value is the literal. -/
theorem toInt_ofNat_lit (n : Nat) (h : n < 2 ^ 63) :
    (no_index (OfNat.ofNat n : _root_.Int64)).toInt = n :=
  _root_.Int64.toInt_ofNat_of_lt h

/-- A negative `long` literal's integer value is the literal, down to `long.MinValue`. -/
theorem toInt_neg_ofNat_lit (n : Nat) (h : n ≤ 2 ^ 63) :
    (-(no_index (OfNat.ofNat n : _root_.Int64))).toInt = -n := by
  rw [_root_.Int64.toInt_neg, _root_.Int64.toInt_ofNat]
  simp only [Int.bmod_def, _root_.Int64.size]
  split <;> split <;> omega

end Int64

end Warrant
