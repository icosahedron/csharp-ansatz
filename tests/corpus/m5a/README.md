# M5a corpus

The M5a exit criterion as files (design §11, docs/m5a/01).
It follows the [M4 corpus](../m4/README.md)'s layout: the tests compile these files in memory with the `Warrant.Frontend` factory, and `expected.json` gives each compilation and the expected outcome of every member, keyed by documentation-comment ID.

## Outcomes

The outcomes are M4's, with these additions:

| Field | Meaning |
|---|---|
| `"by": "script"` | A theorem proved by its `.By(...)` script. |
| `"recursive": true` | A self-recursive method whose block body starts with `Spec.Decreases`. |
| `"outcome": "unproved"` | A theorem or recursive method that was not proved, under the name the reports and `warrant verify` use. An unproved claim is never reported false; the counterexample is what shows it is. |
| `"code"` | For an `unproved` member, its diagnostic code (WRT0001). |
| `"goal"` | For an `unproved` member, the goal WRT0001 shows, in Lean's layout with C# names: for a theorem, the goal of the tactic that failed. |
| `"counterexample"` | For an `unproved` member, the parameter values the counterexample search reports; absent when it finds none. |
| `"obligation": "decreases"` | For an `unproved` recursive method, the decrease obligation is what fails. |

Each outcome is the one the finished milestone gives.
Extraction's tests check what extraction decides: which members become units and which are rejected with which diagnostics; that a theorem's parameters, script and statement are read; and that a recursive method's measure is.
`tests/Warrant.Engine.Tests/CorpusTests.cs` checks the rest in one test, the exit criterion (plan U19): every member's outcome, proof kind, code, goal, counterexample and diagnostics.

## Files

| File | Members | Why it is here |
|---|---|---|
| `accepted/Payments.cs` | `Validate`, `ValidImpliesPositive` | Design §5.1's example, proved by `Unfold` and `Simp`. |
| `accepted/Increment.cs` | `Increment`, `LargerBelowMax` | The true variant of the false claim, proved by `Unfold`, `Simp` and `Omega`. |
| `accepted/Clamp.cs` | `Clamp`, `AtMostOneHundred` | A bound through `int` literals, proved by `Unfold` and `Omega`. |
| `accepted/Recursion.cs` | `Sum`, `Add`, `SumLong` | Well-founded recursion over `int`, with two parameters, and over `long`. |
| `accepted/Quantifiers.cs` | `ZeroIsNeutral`, `FlipTwice`, `RankIsSmall`, `AndTrueIsIdentity` | `Spec.ForAll` with `Intro`; `Cases` over `bool` and a `[Closed]` enum; `Induction`; `AllGoals`, `Try` and simp options. |
| `refuted/Increment.cs` | `AlwaysLarger` | The exit criterion's false claim, with its goal and counterexample. |
| `refuted/Recursion.cs` | `Bad` | A recursion whose decrease obligation fails. |
| `rejected/Recursion.cs` | `IsEven`, `IsOdd`, `Factorial`, `Countdown`, `Nested` | Mutual recursion, recursion without `Spec.Decreases`, `Spec.Decreases` not first, nested recursion (WRT0002). |
| `rejected/Scripts.cs` | `UnfoldsAnOverload`, `SimpWithAString`, `ForAllInCode` | A `nameof` of an overloaded method, a string literal where a lemma is expected, and `Spec.ForAll` outside a theorem (WRT0004). |

## Arithmetic that must not overflow (#244)

Since the M6 follow-ups a verified method's own `int` and `long` arithmetic in C#'s default context must not overflow
(docs/m6/06). No outcome changed:

| Member | Change | Why |
|---|---|---|
| `accepted` `Increment` | `Spec.Requires(x < int.MaxValue)` | `x + 1`; `LargerBelowMax`'s premise is the precondition, which the theorem's well-definedness obligation checks. |
| `refuted` `Increment` | `unchecked(x + 1)` | `AlwaysLarger` is about the wrap: still false, with the counterexample `x = 2147483647`. |
| `Sum`, `SumLong` | `unchecked(n + Sum(n - 1))` | Nothing is known of a recursive call's result where the obligation is stated (a recursive method has no `Spec.Ensures` yet), and the sums do overflow for large `n`. |
| `Add` | `Spec.Requires(b >= 0 && a <= int.MaxValue - b)` (#256; it was `unchecked(a + 1)` before a recursive method could state one) | The body assumes it, so `a + 1` and `b - 1` are proved, and the recursive call `Add(a + 1, b - 1)` is checked against it; `Add` admits its `$wd` obligations and `$contract` after its equation lemma. |
| `rejected` `Scale` (both) | `unchecked(x + x)` | Helpers of the rejected scripts. |

`Bad`'s `n - 1` has an obligation too, but its decrease obligation fails first, so it is refuted for the same reason.
