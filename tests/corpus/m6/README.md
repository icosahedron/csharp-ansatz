# M6 corpus

The M6 exit criterion as files (plan M6 KTD24), started by plan unit U7.
It follows the [M4 corpus](../m4/README.md)'s layout: the tests compile these files in memory with the `Warrant.Frontend` factory, and `expected.json` gives each compilation and the expected outcome of every member, keyed by documentation-comment ID.

## Who reads it

Until translation of the effect monad lands (plan U9) and the default procedure proves contract obligations (U11), only extraction reads this corpus.
`Warrant.Extraction.Tests` (`CorpusTests`, `DiagnoseTests`) and `Warrant.Analyzers.Tests` (`CorpusParityTests`) copy it and check it; the engine, CLI, cross-check and differential tests do not copy it, and `Warrant.Engine.Tests` and `Warrant.Cli.Tests` each pin that it is absent from their output.
U11 and U13 add those consumers.

## Outcomes

Each outcome is, for now, the one extraction decides: `translated` means the member becomes a VIR unit with no diagnostics, and `rejected` lists exactly the diagnostics it gets, as in the M4 corpus.
U11 replaces each `translated` with the member's proof outcome.
The directory a member sits in is the outcome it is expected to have then: `accepted/` proves, `refuted/` fails with WRT0001 because an implicit exception (overflow, a zero divisor, a null read) is possible and nothing rules it out (KTD12).

## Compilations

| Name | Files | Notes |
|---|---|---|
| `accepted` | `accepted/*.cs` | |
| `refuted` | `refuted/*.cs` except `CheckedProject.cs` | |
| `rejected` | `rejected/*.cs` | One member per construct M6 still rejects. |
| `checked-project` | `refuted/CheckedProject.cs` | Compiled with overflow checking on. |

## Members moved from the M4 corpus

These members were rejected in the M4 corpus for a construct M6 supports. U7 and U17 moved them here unchanged, keys included, so the M4 corpus keeps its meaning (R14); the M4 README's flip list records each move.

| Member | M4 outcome | M6 outcome now |
|---|---|---|
| `Corpus.Rejected.Arithmetic.Halve` | WRT0002 `division` | `translated` (accepted) |
| `Corpus.Rejected.Arithmetic.Remainder` | WRT0002 `remainder` | `translated` (accepted) |
| `Corpus.Rejected.Statements.Throws` | WRT0002 `throw` | `translated` (accepted) |
| `Corpus.Rejected.Arithmetic.CheckedAdd` | WRT0002 `checked arithmetic` | `translated` (refuted) |
| `Corpus.Rejected.Statements.CallsUnverified` | WRT0005 `M:System.Math.Abs(System.Int32)` | `translated` (refuted) |
| `Corpus.Rejected.CheckedProject.Checked.Add` | WRT0002 `checked arithmetic` | `translated` (checked-project) |
| `Corpus.Rejected.CheckedProject.Checked.Negate` | WRT0002 `checked arithmetic` | `translated` (checked-project) |
| `Corpus.Rejected.CheckedProject.Checked.Narrow` | WRT0002 `checked arithmetic` | `translated` (checked-project) |
| `Corpus.Rejected.Types.NullableParameter` | WRT0002 `nullable type` | `translated` (accepted) |
| `Corpus.Rejected.Types.ReturnsNull` | WRT0002 `nullable type` | `translated` (accepted) |
| `Corpus.Rejected.Statements.Decimals` | WRT0002 `decimal` | `translated` (accepted) |

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
