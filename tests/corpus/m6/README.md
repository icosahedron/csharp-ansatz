# M6 corpus

The M6 exit criterion as files (plan M6 KTD24), started by plan unit U7.
It follows the [M4 corpus](../m4/README.md)'s layout: the tests compile these files in memory with the `Warrant.Frontend` factory, and `expected.json` gives each compilation and the expected outcome of every member, keyed by documentation-comment ID.

## Who reads it

Extraction reads this corpus, and so does translation: `MonadicTranslationTests` in `Warrant.Semantics.Tests` (U9) translates the members with no `decimal`, contract or dependency and admits them, and `DependencyObligationTests` (U19) translates every compilation in full and admits it.
`Warrant.Extraction.Tests` (`CorpusTests`, `DiagnoseTests`), `Warrant.Analyzers.Tests` (`CorpusParityTests`) and `Warrant.Semantics.Tests` copy it and check it.
`Warrant.Engine.Tests` runs every member through the default procedure (U11, U19, U20, `CorpusTests.EveryM6MemberGetsItsExpectedOutcome`), and copies the corpus for the differential tests (U13, `Differential/EffectDifferentialTests`; U22, `Differential/DependencyDifferentialTests` for the dependency files under mocked dependencies, and `Differential/ContractStatementTests` for every proved contract on the CLR).
`Warrant.Cli.Tests` (`M6CorpusTests`) runs `warrant verify` on `accepted/` and `refuted/`, the files with dependencies included, and checks each refuted member's line and kind.
The methods that call a dependency (`ProcessPayment`, `Found`, `IdIfPending`, `QuantityOf`, `Counted`, `Reserved`, `IdOf`, `ShipIfFound`) are proved from U20 on: at each call the walker uses the member's contract hypothesis (design D9), so `ProcessPayment` is proved with its store as a hypothesis. Its block of the assumption report is `ProcessPayment.report.txt`, and that of `Closed`, which throws on every path, is `Closed.report.txt`; `ReportTests` (engine) and `M6CorpusTests` (CLI) compare both with the report they build.
`scripts/cross-check.sh`'s M6 rows (U14, R13) verify `accepted/` with `--out` and have Lean's kernel replay the certificate, `ProcessPayment`'s contract theorem included; do the same for what Warrant admits from `refuted/` and `rejected/`, translating the `checked-project` file with overflow checking on (#111); and check that a copy of the certificate with `ProcessPayment`'s proof replaced is rejected by both kernels.
The M6 exit tests (`dotnet test --filter M6Exit`: `M6ExitTests` in `Warrant.Cli.Tests`, `Warrant.Engine.Tests` and `Warrant.Semantics.Tests`) read it too.

## Outcomes

Each outcome is the member's proof outcome under the default procedure (U11): `translated` means the member's definition and, when it has one, its contract obligation are admitted; `unproved` means WRT0001, with `vc` giving the first failing VC's kind and line and the number of failing VCs (`none` and 0 when no VC failed: an unsatisfiable contract, KTD25, or a `[ProofFor]` script, which is reported where its script fails, or at `no line` when it ends with goals left), and `goal` that VC's goal after the VC simp set; `skipped` means the engine did not run a method because something it calls was not admitted; `rejected` lists exactly the diagnostics a member gets, as in the M4 corpus.
`accepted/` proves, and `refuted/` fails with WRT0001: an implicit exception (overflow, a zero divisor, a null read) is possible and nothing rules it out (KTD12), or a `Spec.Ensures`, `Spec.Assert` or callee's `Spec.Requires` does not hold, or a contract is unsatisfiable (KTD25).
In `rejected/`, the methods the rejected members name or call have proof outcomes too: `Scale`'s unguarded division is not proved, and `Kept`'s script (`Tactic.Omega()` on the triple) does not close it.

## Compilations

| Name | Files | Notes |
|---|---|---|
| `accepted` | `accepted/*.cs` | |
| `refuted` | `refuted/*.cs` except `CheckedProject.cs` and `Dependencies.cs` | |
| `refuted-dependencies` | `refuted/Dependencies.cs` | Refuted methods that call dependencies (U14), in a compilation of their own so the differential harness for dependencies (`DependencyDifferentialTests`) compiles them apart from the rest. |
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

## Arithmetic that must not overflow (#244)

Since #244 a verified method's own `int` and `long` arithmetic in C#'s default context must not overflow (docs/m6/06).
Three members changed, keeping their outcomes: `Lookups.Neighbour` in `refuted/Dependencies.cs` gained
`Spec.Requires(id < int.MaxValue)` for its `id + 1` (it still fails at its postcondition, its goal now listing the bound
and the exact value of `id + 1`, and the members below it moved down a line); `Contracts.Next` and
`Dependencies.Store.Sum` in `rejected/`, helpers of rejected members, write their arithmetic `unchecked`. The accepted
members' arithmetic was already bounded (`Sum`, `Average`, `Steps.Next`).

## Files

| File | Members | Why it is here |
|---|---|---|
| `accepted/Arithmetic.cs` | `Halve`, `Remainder` | Moved from M4. `/` and `%` by a constant other than 0 and -1 cannot throw, so they stay pure (KTD11). |
| `accepted/Statements.cs` | `Throws`, `Decimals` | Moved from M4. A throw expression of a `System` exception, and a `decimal` passed through. |
| `accepted/Types.cs` | `NullableParameter`, `ReturnsNull` | Moved from M4. A parameter and a return value declared nullable (`Point?`), with the record they use. |
| `accepted/Effects.cs` | `Biggest`, `Smallest`, `Guard`, `DivisibleByFour`, `Closed` | `Math.Max` and `Math.Min` (KTD23), a throw statement of a user exception that only chains to a `System` one, `year % 4` in a pure method (KTD11), and a method that throws on every path, whose `Spec.Ensures` holds vacuously and whose report lists the throw (`Closed.report.txt`, KTD12, KTD20). |
| `accepted/Nullables.cs` | `Nullables.*`, `Decimals.*`, `Refunds.*` and the records `Fee` and `Refund` | `is null`, `!= null`, `??`, `GetValueOrDefault()`, `HasValue` guarding `Value`, a value wrapped as `int?`, a `Payment?` used only after it is tested (#163, the unwrap the path proves), and `decimal` comparisons, record equality with a `decimal` field, unary `-` and `Math.Max`/`Min`/`Abs`; and (#218) records with `int?`, `decimal?` and `Payment?` fields, compared with `==` (`SameFee`, `SameRefund`), read after a null test in a body and in a `Spec.Requires` (`OriginalIdOrZero`), and updated with `with` (`Waived`). |
| `refuted/Arithmetic.cs` | `CheckedAdd` | Moved from M4. `checked(a + b)` can overflow. |
| `refuted/Statements.cs` | `CallsUnverified` | Moved from M4. `Math.Abs(int.MinValue)` throws (R4). |
| `refuted/CheckedProject.cs` | `Add`, `Negate`, `Narrow` | Moved from M4. A `CheckForOverflowUnderflow` project's `+`, unary `-` and narrowing cast are checked. Its widening cast stays in the M4 corpus. |
| `refuted/Effects.cs` | `Ratio`, `Magnitude` | `a / b` and `Math.Abs` on `long` with nothing ruling out the exception. |
| `refuted/Nullables.cs` | `Read`, `Cast`, `IdOf`, `Unchecked`, `AddFee`, `Difference`, `Refunds.OriginalId` | `x.Value`, `(long)x`, a member access and an argument of a `Payment?` that nothing tests (the compiler's warnings are silenced; the model checks anyway), and `decimal` `+` and `-`, which can overflow; and a record's nullable field read that nothing tests (#218). |
| `refuted/Contracts.cs` | `Ratio`, `Neg`, `Share`, `ShareOfNothing`, `Twice`, `Kept`, `Asserted`, `Impossible`, `QuotientOfAny`, `SumUnbounded`, `Grown` | U14 (#98): `Ratio` with only `Spec.Requires(b != 0)`, which leaves `int.MinValue / -1`; `x / -1`; a caller that passes 0 to `Share`, which requires a non-zero argument (`Share` itself proves); a plainly false `Spec.Ensures`, and one aimed at by a `[ProofFor]` script (`Kept`, reported at the script's failing `Tactic.Omega()`), each with a `Spec.Requires` that keeps its `Spec.Ensures` arithmetic from overflowing (#183), so they still fail for being false; `Spec.Assert(b != 0); return a / b;` with no `Spec.Requires`, which fails at the `Spec.Assert` (and at the division, which can still overflow); and a contradictory pair of `Spec.Requires` (KTD25, at the second); `QuotientOfAny`, whose `Spec.NoThrow` fails at its `throw` because its `Spec.Requires` does not rule out `b == 0` (#182, `ReachableThrow`); and `SumUnbounded`, whose `Spec.Ensures<int>(r => r == a + b)` fails at its `a + b`, which nothing keeps from overflowing (#183: arithmetic in a `Spec` expression must not overflow); and `Grown`, whose `Spec.Ensures` written with `Spec.Implies` is false and fails at its line (#213). |
| `refuted/Dependencies.cs` | `Lookups.Neighbour`, `Saved`, `Twice`, `TwiceScripted`, the contract units of `IPaymentStore` and `ICounter.Count`, `Tally.Size`, `Steps.Next`, `Run` | U14 (#96, #97): an `Ensures` that holds only through `GetPayment`'s contract fails when the call asks for `id + 1`, or relies on `SavePayment`'s empty contract, or on two calls to `GetPayment(id)` agreeing, which the world threaded between them (KTD4) does not give, under the default procedure and with a `[ProofFor]` script that cases on the call's result and then runs simp; and a contract-class member whose `Spec.Ensures` admits no result (KTD25), so `Size`, which calls it, is skipped; and `Steps.Run`, whose `Requires(x < 200)` does not give the `x < 100` that `Next`, which it awaits, requires (#228: an awaited call is a call site like any other). Its own compilation, `refuted-dependencies`. |
| `rejected/Nullables.cs` | `Forgiven`, `LiftedLess`, `LiftedEquals`, `LiftedAdd`, `ReadIsPositive`, `Product`, `AddingOneIsLarger` | `!` (`null-forgiving operator`), `lifted comparison` and `lifted arithmetic` on `int?` (#76), `decimal operator other than + and -`, and a theorem statement with `nullable read` or `decimal arithmetic` (KTD11). |
| `rejected/Effects.cs` | `ThrowsOdd`, `TryFinally`, `Sign`, `RatioAtMost`, `AbsoluteIsNonNegative`, `TryCatch`, `Gcd` | An exception whose constructor divides, `try`/`finally` and `try`/`catch` (`try`), a `Math` member that is not modelled (WRT0005), a theorem statement that divides by a variable (#164) or calls a throwing modelled member (KTD11), and a `%`-based recursive `Gcd` (`recursion with effects`). |
| `accepted/Contracts.cs` | `NonNegative`, `AtMost`, `Capped`, `Average`, `Same`, `Quotient`, `Half`, `Sum`, `Successor` | Contracts without dependencies (U8): leading `Spec.Requires` and `Spec.Ensures`, a call to a method with `Spec.Requires` (which makes the caller raising, KTD11), `Spec.Assert` with a script, a `[ProofFor]` method whose script starts with `Tactic.VcGen()`; `Quotient`, whose `Spec.NoThrow` is proved because its `Spec.Requires` rules out its guard's `throw` (#182), and `Half`, a caller without `Spec.NoThrow` that uses its contract; and `Sum`, with `a + b` in a `Spec.Ensures` that bounds in `Spec.Requires` keep from overflowing (#183); and `Successor`, a `Spec.Ensures` with `Spec.Implies` whose premise keeps the `x + 1` in its conclusion from overflowing (#213). |
| `accepted/Payments.cs` | `PaymentService.ProcessPayment`, `Validate`, `PaymentLookup.Found`, `IdIfPending`, the contract units of `IPaymentStore.GetPayment` and `SavePayment` | Design §5.2's payment example (U18): `store` is a never-assigned primary-constructor parameter of an interface whose `file` contract class states `GetPayment`'s `Ensures` and assumes nothing of `SavePayment` (`=> default!`). `ProcessPayment` has `store` as its one dependency with both members, the contract units as dependencies, and assumes `store` and both returned tasks are not null. Its `Spec.Ensures` is proved by the default procedure with both members' contracts as hypotheses (U20). `Found`'s `Spec.Ensures` holds only through `GetPayment`'s contract (U20's external-contract member, #97; its refuted twins are in `refuted/Dependencies.cs`). `IdIfPending` reads two fields of `GetPayment`'s result after its null test, and its `Spec.Ensures` needs the contract's fact about the first read for the second (#226). |
| `accepted/Dependencies.cs` | `OrderService.QuantityOf`, `Counted`, `Reserved`, `Steps.Next`, `Run`, `ShipmentService.IdOf`, `ShipIfFound`, the contract units of `IOrders`' and `IShipments`' members and `IDisposable.Dispose` | U18: a readonly-field dependency whose interface inherits `IDisposable`, a `Task<Order?>` result that is nullable once awaited (#171), a `void` and a synchronous member, an `abstract` contract member, a `ValueTask`, a member with an unmodelled type (`Describe`, `string`) that nothing calls, and a verified async method awaiting another; and (#215) a `CancellationToken` parameter passed through to both of `IShipments`' members, and a bare `return;` in a `Task` method (`ShipIfFound`, which proves `Ship`'s `Spec.Requires` from `Find`'s contract). |
| `rejected/Dependencies.cs` | `Counter.Next`, the `Store` (`Dropped` and `Stored` among them: `_ = M();` and `var t = M(); await t;` on a Task-returning `M`, U14; `Uncancelled`, which passes `default` for a `CancellationToken`, #215, in place of `Early`, whose bare `return;` is accepted now) and `Assigned` members, and the contract classes `StockAgain`, `ShakyContract`, `TwiceContract`, `PublicContract`, `WideContract`, `ExtraContract`, `ItemContract`, `LaxContract` | One U18 rejection each: dependencies that break KTD9's rules, other uses of the class's state, tasks that are not the direct operand of `await` (KTD22), and each step of the contract shape (KTD10). `Store.Sum` translates. |
| `rejected/Contracts.cs` | `EnsuresLate`, `RequiresAfterEnsures`, `DecreasesAfterRequires`, `NoThrowAfterEnsures`, `Countdown`, `Descend`, `Widened`, `NoResult`, `NotALambda`, `Scaled`, `NextIsPositive`, the `[ProofFor]` methods `MissingProof`, `KeptAgain`, `BareProof`, `GivenProof`, `TwinProof`, `PlainProof` | One U8 rejection each: the order and place of the leading `Spec` statements, the type `Spec.Ensures` binds (KTD8), a `Spec.Ensures` on a recursive method (`Countdown`; a `Spec.Requires` is allowed since #256), recursion with effects, a `Spec` expression and a theorem that call a raising method (KTD11, #164, #165), and each way a `[ProofFor]` method supplies no script (KTD16). The methods they name or call (`Scale`, `Checked`, `Next`, `Kept`, `Bare`, `Given`, `Twin`) translate. |
