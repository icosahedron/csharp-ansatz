/-!
C# `long` is Lean's `Int64` (design D7, plan KTD1): CLR facts in unchecked code.
-/
namespace Warrant.Clr.Int64

/-- `long.MaxValue + 1 == long.MinValue`. -/
theorem maxValue_add_one : Int64.maxValue + 1 = Int64.minValue := by decide

/-- `-long.MinValue == long.MinValue`. -/
theorem neg_minValue : -Int64.minValue = Int64.minValue := by decide

/-- `(int)3000000000L == -1294967296`: narrowing keeps the low 32 bits. -/
theorem toInt32_three_billion : (3000000000 : Int64).toInt32 = -1294967296 := by decide

end Warrant.Clr.Int64
