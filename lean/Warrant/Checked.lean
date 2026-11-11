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

None of these carries `@[simp]`; every name is a bundle root (`lean/bundle-roots.txt`). U3 adds the checked
models to this file.
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

end Warrant
