/-!
C# `bool` is Lean's `Bool` (plan KTD1). `&&`/`&` are `Bool.and`, `||`/`|` are
`Bool.or`, `^` is `Bool.xor` and `!` is `Bool.not` (docs/m4/05).
-/
namespace Warrant.Clr.Bool

/-- `true ^ true == false`. -/
theorem xor_true_true : Bool.xor true true = false := by decide

/-- `true ^ false == true`. -/
theorem xor_true_false : Bool.xor true false = true := by decide

end Warrant.Clr.Bool
