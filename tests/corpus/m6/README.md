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
The directory a member sits in is the outcome it is expected to have then: `accepted/` proves, `refuted/` fails with WRT0001 because an implicit exception (overflow, a zero divisor) is possible and nothing rules it out (KTD12).

## Compilations

| Name | Files | Notes |
|---|---|---|
| `accepted` | `accepted/*.cs` | |
| `refuted` | `refuted/*.cs` except `CheckedProject.cs` | |
| `rejected` | `rejected/*.cs` | One member per construct M6 still rejects. |
| `checked-project` | `refuted/CheckedProject.cs` | Compiled with overflow checking on. |

## Members moved from the M4 corpus

These members were rejected in the M4 corpus for a construct M6 supports. U7 moved them here unchanged, keys included, so the M4 corpus keeps its meaning (R14); the M4 README's flip list records each move.

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

## Files

| File | Members | Why it is here |
|---|---|---|
| `accepted/Arithmetic.cs` | `Halve`, `Remainder` | Moved from M4. `/` and `%` by a constant other than 0 and -1 cannot throw, so they stay pure (KTD11). |
| `accepted/Statements.cs` | `Throws` | Moved from M4. A throw expression of a `System` exception. |
| `accepted/Effects.cs` | `Biggest`, `Smallest`, `Guard` | `Math.Max` and `Math.Min` (KTD23), and a throw statement of a user exception that only chains to a `System` one. |
| `refuted/Arithmetic.cs` | `CheckedAdd` | Moved from M4. `checked(a + b)` can overflow. |
| `refuted/Statements.cs` | `CallsUnverified` | Moved from M4. `Math.Abs(int.MinValue)` throws (R4). |
| `refuted/CheckedProject.cs` | `Add`, `Negate`, `Narrow` | Moved from M4. A `CheckForOverflowUnderflow` project's `+`, unary `-` and narrowing cast are checked. Its widening cast stays in the M4 corpus. |
| `refuted/Effects.cs` | `Ratio`, `Magnitude` | `a / b` and `Math.Abs` on `long` with nothing ruling out the exception. |
| `rejected/Effects.cs` | `ThrowsOdd`, `TryFinally`, `Sign`, `RatioAtMost`, `AbsoluteIsNonNegative` | An exception whose constructor divides, `try`/`finally`, a `Math` member that is not modelled (WRT0005), and a theorem statement that divides or calls a throwing modelled member (KTD11). |
