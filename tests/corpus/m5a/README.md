# M5a corpus

The M5a exit criterion as files (design §11, docs/m5a/01).
It follows the [M4 corpus](../m4/README.md)'s layout: the tests compile these files in memory with the `Warrant.Frontend` factory, and `expected.json` gives each compilation and the expected outcome of every member, keyed by documentation-comment ID.

## Outcomes

The outcomes are M4's, with these additions:

| Field | Meaning |
|---|---|
| `"by": "script"` | A theorem proved by its `.By(...)` script. |
| `"recursive": true` | A self-recursive method whose block body starts with `Spec.Decreases`. |
| `"goal"` | For a `false` theorem, the goal WRT0001 shows, in Lean's layout with C# names. |
| `"counterexample"` | For a `false` theorem, the parameter values the counterexample search reports. |
| `"obligation": "decreases"` | For a `false` recursive method, the decrease obligation is what fails. |

Each outcome is the one the finished milestone gives.
Extraction's tests check what extraction decides: which members become units and which are rejected with which diagnostics; that a theorem's parameters, script and statement are read; and that a recursive method's measure is.
The proofs, goals and counterexamples are checked by the units that build them.

## Files

| File | Members | Why it is here |
|---|---|---|
| `accepted/Payments.cs` | `Validate`, `ValidImpliesPositive` | Design §5.1's example, proved by `Unfold` and `Simp`. |
| `accepted/Increment.cs` | `Increment`, `LargerBelowMax` | The true variant of the false claim, proved by `Unfold`, `Simp` and `Omega`. |
| `accepted/Recursion.cs` | `Sum`, `Add`, `SumLong` | Well-founded recursion over `int`, with two parameters, and over `long`. |
| `accepted/Quantifiers.cs` | `ZeroIsNeutral`, `FlipTwice`, `RankIsSmall`, `AndTrueIsIdentity` | `Spec.ForAll` with `Intro`; `Cases` over `bool` and a `[Closed]` enum; `Induction`; `AllGoals`, `Try` and simp options. |
| `refuted/Increment.cs` | `AlwaysLarger` | The exit criterion's false claim, with its goal and counterexample. |
| `refuted/Recursion.cs` | `Bad` | A recursion whose decrease obligation fails. |
| `rejected/Recursion.cs` | `IsEven`, `IsOdd`, `Factorial`, `Countdown`, `Nested` | Mutual recursion, recursion without `Spec.Decreases`, `Spec.Decreases` not first, nested recursion (WRT0002). |
| `rejected/Scripts.cs` | `UnfoldsAnOverload`, `SimpWithAString`, `ForAllInCode` | A `nameof` of an overloaded method, a string literal where a lemma is expected, and `Spec.ForAll` outside a theorem (WRT0004). |
