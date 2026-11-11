# M6 corpus

The M6 exit criterion as files (plan M6 KTD24), started by plan unit U7.
It follows the [M4 corpus](../m4/README.md)'s layout: the tests compile these files in memory with the `Warrant.Frontend` factory, and `expected.json` gives each compilation and the expected outcome of every member, keyed by documentation-comment ID.

## Who reads it

Extraction reads this corpus, and so does translation: `MonadicTranslationTests` in `Warrant.Semantics.Tests` (U9) translates the members with no `decimal`, contract or dependency and admits them, and `DependencyObligationTests` (U19) translates every compilation in full and admits it.
`Warrant.Extraction.Tests` (`CorpusTests`, `DiagnoseTests`), `Warrant.Analyzers.Tests` (`CorpusParityTests`) and `Warrant.Semantics.Tests` copy it and check it.
`Warrant.Engine.Tests` runs every member through the default procedure (U11, U19, `CorpusTests.EveryM6MemberGetsItsExpectedOutcome`), and copies the corpus for the differential tests (U13, `Differential/EffectDifferentialTests`).
`Warrant.Cli.Tests` (`M6CorpusTests`) runs `warrant verify` on its files without dependencies (U20 adds the others).
The methods that call a dependency (`ProcessPayment`, `QuantityOf`, `Counted`, `Reserved`) are marked `"awaits": "U20"`: they translate (U19) and their dependencies' contract members pass their KTD25 and KTD26 checks, but the walker has no rule for an external call until U20, so each is `unproved` with one `Unsupported` VC, the first call's triple (`"at": "no line"`: the walker's leftover for the call carries no VIR node yet), for now. U20 is to prove them; the cross-check row comes with U14.

## Outcomes

Each outcome is the member's proof outcome under the default procedure (U11): `translated` means the member's definition and, when it has one, its contract obligation are admitted; `unproved` means WRT0001, with `vc` giving the first failing VC's kind and line and the number of failing VCs, and `goal` that VC's goal after the VC simp set; `rejected` lists exactly the diagnostics a member gets, as in the M4 corpus.
`accepted/` proves, except the four methods awaiting U20, and `refuted/` fails with WRT0001 because an implicit exception (overflow, a zero divisor, a null read) is possible and nothing rules it out (KTD12).
In `rejected/`, the methods the rejected members name or call have proof outcomes too: `Scale`'s unguarded division is not proved, and `Kept`'s script (`Tactic.Omega()` on the triple) does not close it.

## Compilations

| Name | Files | Notes |
|---|---|---|
| `accepted` | `accepted/*.cs` | |
| `refuted` | `refuted/*.cs` except `CheckedProject.cs` | |
| `rejected` | `rejected/*.cs` | One member per construct M6 still rejects. |
| `checked-project` | `refuted/CheckedProject.cs` | Compiled with overflow checking on. |

## Members moved from the M4 corpus

These members were rejected in the M4 corpus for a construct M6 supports. U7, U17 and U18 moved them here unchanged, keys included, so the M4 corpus keeps its meaning (R14); the M4 README's flip list records each move.

| Member | M4 outcome | M6 outcome now |
|---|---|---|
| `Corpus.Rejected.Arithmetic.Halve` | WRT0002 `division` | proved (accepted) |
| `Corpus.Rejected.Arithmetic.Remainder` | WRT0002 `remainder` | proved (accepted) |
| `Corpus.Rejected.Statements.Throws` | WRT0002 `throw` | proved (accepted) |
| `Corpus.Rejected.Arithmetic.CheckedAdd` | WRT0002 `checked arithmetic` | `unproved` (refuted) |
| `Corpus.Rejected.Statements.CallsUnverified` | WRT0005 `M:System.Math.Abs(System.Int32)` | `unproved` (refuted) |
| `Corpus.Rejected.CheckedProject.Checked.Add` | WRT0002 `checked arithmetic` | `unproved` (checked-project) |
| `Corpus.Rejected.CheckedProject.Checked.Negate` | WRT0002 `checked arithmetic` | `unproved` (checked-project) |
| `Corpus.Rejected.CheckedProject.Checked.Narrow` | WRT0002 `checked arithmetic` | `unproved` (checked-project) |
| `Corpus.Rejected.Types.NullableParameter` | WRT0002 `nullable type` | proved (accepted) |
| `Corpus.Rejected.Types.ReturnsNull` | WRT0002 `nullable type` | proved (accepted) |
| `Corpus.Rejected.Statements.Decimals` | WRT0002 `decimal` | proved (accepted) |
| `Corpus.Rejected.Counter.Next` | WRT0002 `instance member of a class` | WRT0002 `member access on this` (rejected): U18 accepts a class's instance methods, and this one reads a field that is not a dependency |

## Files

| File | Members | Why it is here |
|---|---|---|
| `accepted/Arithmetic.cs` | `Halve`, `Remainder` | Moved from M4. `/` and `%` by a constant other than 0 and -1 cannot throw, so they stay pure (KTD11). |
| `accepted/Statements.cs` | `Throws`, `Decimals` | Moved from M4. A throw expression of a `System` exception, and a `decimal` passed through. |
| `accepted/Types.cs` | `NullableParameter`, `ReturnsNull` | Moved from M4. A parameter and a return value declared nullable (`Point?`), with the record they use. |
| `accepted/Effects.cs` | `Biggest`, `Smallest`, `Guard` | `Math.Max` and `Math.Min` (KTD23), and a throw statement of a user exception that only chains to a `System` one. |
| `accepted/Nullables.cs` | `Nullables.*`, `Decimals.*` | `is null`, `!= null`, `??`, `GetValueOrDefault()`, `HasValue` guarding `Value`, a value wrapped as `int?`, a `Payment?` used only after it is tested (#163, the unwrap the path proves), and `decimal` comparisons, record equality with a `decimal` field, unary `-` and `Math.Max`/`Min`/`Abs`. |
| `refuted/Arithmetic.cs` | `CheckedAdd` | Moved from M4. `checked(a + b)` can overflow. |
| `refuted/Statements.cs` | `CallsUnverified` | Moved from M4. `Math.Abs(int.MinValue)` throws (R4). |
| `refuted/CheckedProject.cs` | `Add`, `Negate`, `Narrow` | Moved from M4. A `CheckForOverflowUnderflow` project's `+`, unary `-` and narrowing cast are checked. Its widening cast stays in the M4 corpus. |
| `refuted/Effects.cs` | `Ratio`, `Magnitude` | `a / b` and `Math.Abs` on `long` with nothing ruling out the exception. |
| `refuted/Nullables.cs` | `Read`, `Cast`, `IdOf`, `Unchecked`, `AddFee`, `Difference` | `x.Value`, `(long)x`, a member access and an argument of a `Payment?` that nothing tests (the compiler's warnings are silenced; the model checks anyway), and `decimal` `+` and `-`, which can overflow. |
| `rejected/Nullables.cs` | `Forgiven`, `LiftedLess`, `LiftedEquals`, `LiftedAdd`, `ReadIsPositive`, `Product`, `AddingOneIsLarger` | `!` (`null-forgiving operator`), `lifted comparison` and `lifted arithmetic` on `int?` (#76), `decimal operator other than + and -`, and a theorem statement with `nullable read` or `decimal arithmetic` (KTD11). |
| `rejected/Effects.cs` | `ThrowsOdd`, `TryFinally`, `Sign`, `RatioAtMost`, `AbsoluteIsNonNegative` | An exception whose constructor divides, `try`/`finally`, a `Math` member that is not modelled (WRT0005), and a theorem statement that divides or calls a throwing modelled member (KTD11). |
| `accepted/Contracts.cs` | `NonNegative`, `AtMost`, `Capped`, `Average`, `Same` | Contracts without dependencies (U8): leading `Spec.Requires` and `Spec.Ensures`, a call to a method with `Spec.Requires` (which makes the caller raising, KTD11), `Spec.Assert` with a script, and a `[ProofFor]` method whose script starts with `Tactic.VcGen()`. |
| `accepted/Payments.cs` | `PaymentService.ProcessPayment`, `Validate`, the contract units of `IPaymentStore.GetPayment` and `SavePayment` | Design §5.2's payment example (U18): `store` is a never-assigned primary-constructor parameter of an interface whose `file` contract class states `GetPayment`'s `Ensures` and assumes nothing of `SavePayment` (`=> default!`). `ProcessPayment` has `store` as its one dependency with both members, the contract units as dependencies, and assumes `store` and both returned tasks are not null. |
| `accepted/Dependencies.cs` | `OrderService.QuantityOf`, `Counted`, `Reserved`, `Steps.Next`, `Run`, the contract units of `IOrders`' members and `IDisposable.Dispose` | U18: a readonly-field dependency whose interface inherits `IDisposable`, a `Task<Order?>` result that is nullable once awaited (#171), a `void` and a synchronous member, an `abstract` contract member, a `ValueTask`, a member with an unmodelled type (`Describe`, `string`) that nothing calls, and a verified async method awaiting another. |
| `rejected/Dependencies.cs` | `Counter.Next`, the `Store` and `Assigned` members, and the contract classes `StockAgain`, `ShakyContract`, `TwiceContract`, `PublicContract`, `WideContract`, `ExtraContract`, `ItemContract`, `LaxContract` | One U18 rejection each: dependencies that break KTD9's rules, other uses of the class's state, tasks that are not the direct operand of `await` (KTD22), and each step of the contract shape (KTD10). `Store.Sum` translates. |
| `rejected/Contracts.cs` | `EnsuresLate`, `RequiresAfterEnsures`, `DecreasesAfterRequires`, `Countdown`, `Descend`, `Widened`, `NoResult`, `NotALambda`, `Scaled`, `NextIsPositive`, the `[ProofFor]` methods `MissingProof`, `KeptAgain`, `BareProof`, `GivenProof`, `TwinProof`, `PlainProof` | One U8 rejection each: the order and place of the leading `Spec` statements, the type `Spec.Ensures` binds (KTD8), a contract on a recursive method, recursion with effects, a `Spec` expression and a theorem that call a raising method (KTD11, #164, #165), and each way a `[ProofFor]` method supplies no script (KTD16). The methods they name or call (`Scale`, `Checked`, `Next`, `Kept`, `Bare`, `Given`, `Twin`) translate. |
