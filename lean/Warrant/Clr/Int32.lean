/-!
C# `int` is Lean's `Int32` (design D7, plan KTD1). These theorems record the CLR
behaviour, in unchecked code, that the translator relies on. Warrant's kernel
re-checks them every time it loads the bundle, so a Lean upgrade that changed
`Int32` would fail Warrant's own tests.
-/
namespace Warrant.Clr.Int32

/-- `int.MaxValue + 1 == int.MinValue`. -/
theorem maxValue_add_one : Int32.maxValue + 1 = Int32.minValue := by decide

/-- `int.MinValue - 1 == int.MaxValue`. -/
theorem minValue_sub_one : Int32.minValue - 1 = Int32.maxValue := by decide

/-- `-int.MinValue == int.MinValue`. -/
theorem neg_minValue : -Int32.minValue = Int32.minValue := by decide

/-- `int.MinValue * -1 == int.MinValue`. -/
theorem minValue_mul_neg_one : Int32.minValue * -1 = Int32.minValue := by decide

/-- Comparison is signed: `-1 < 1`. -/
theorem neg_one_lt_one : (-1 : Int32) < 1 := by decide

/-- `(int)(long)x == x`: widening then narrowing is the identity. -/
theorem toInt64_toInt32 (x : Int32) : x.toInt64.toInt32 = x := Int32.toInt32_toInt64 x

end Warrant.Clr.Int32
