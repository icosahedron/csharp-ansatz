# M4 corpus

The M4 exit criterion as files (design §11, docs/m4/02).
None of these files belongs to a project: the tests compile them in memory with the `Warrant.Frontend` factory, so the repository's build settings never apply to them.
`.gitattributes` keeps them LF on every machine, so spans and hashes do not change between checkouts.

`expected.json` gives each compilation and the expected outcome of every member, keyed by documentation-comment ID.

## Compilations

| Name | Files | Notes |
|---|---|---|
| `accepted` | `accepted/*.cs` | Every member translates and every theorem is proved. `warrant translate` exits 0 here, and `scripts/cross-check.sh` has Lean's kernel re-check the result. |
| `refuted` | `refuted/*.cs` | Theorems that translate but are false (WRT0001). |
| `rejected` | `rejected/*.cs` except `CheckedProject.cs` | One member per rejected construct, using nothing else unsupported. |
| `checked-project` | `rejected/CheckedProject.cs` | Compiled with overflow checking on. Only its widening cast is left (see the flip list). |

## Outcomes

| Outcome | Meaning |
|---|---|
| `translated` | The unit translates and the kernel admits it. `assumeNonNull` lists the values the unit's assumptions must cover; `assumeIdentityEquality` marks a closed class with its own equality. |
| `proved` | A theorem proved by the proof named in `by` (`rfl` or `decide`). |
| `false` | A theorem reported false (WRT0001). |
| `rejected` | The unit is not translated; `diagnostics` lists exactly the diagnostics it gets, each with its code and construct name. |
| `warning` | A member or type that gets only the warnings listed. |

The construct names in `expected.json` are the ones extraction reports.
A unit that depends on a rejected unit is rejected with the construct `depends on a rejected unit`.

## Accepted files

| File | Why it is here |
|---|---|
| `PayoutRules.cs` | The tutorial's running example, followed through every chapter of docs/m4. |
| `Discounts.cs` | The how-to guide's example. |
| `Payments.cs` | The `Validate`-shaped method the exit criterion asks for, over a record and open enums, with `int` in place of `decimal`. |
| `Increment.cs` | Wrap-around at `int.MaxValue` and `long.MaxValue`. |
| `ClaimStatus.cs` | A `[Closed]` enum, with a switch expression using `or` and `_`. |
| `Outcome.cs` | A `[Closed]` closed-set class with a `string` field, compared with `==`. `Code` returns `3` on the CLR for `null`, the value the non-null assumption excludes. |
| `Records.cs` | Construction, property reads, `with`, equality, a verified instance property, and record fields of record and closed-class type. |
| `Locals.cs` | Reassignment, a `let` of an `ite`, a join point, the nested-`return` shape that the shortcut rules must not touch, compound assignment, `++`, and a switch statement that falls through. |
| `Conversions.cs` | `int` to `long` and back, and casts between open enums and integers, including an unnamed value. |

## Flip list

A member whose construct a later milestone supports leaves this corpus, so every member here keeps its M4 outcome (M6 R14).
Each move, with the milestone unit that made it and where the member went:

| Member | M4 outcome | Moved by | Now |
|---|---|---|---|
| `M:Corpus.Rejected.Arithmetic.Halve(System.Int32)` | WRT0002 `division` | M6 U7 | `tests/corpus/m6/accepted/Arithmetic.cs` |
| `M:Corpus.Rejected.Arithmetic.Remainder(System.Int32)` | WRT0002 `remainder` | M6 U7 | `tests/corpus/m6/accepted/Arithmetic.cs` |
| `M:Corpus.Rejected.Arithmetic.CheckedAdd(System.Int32,System.Int32)` | WRT0002 `checked arithmetic` | M6 U7 | `tests/corpus/m6/refuted/Arithmetic.cs` |
| `M:Corpus.Rejected.Statements.Throws(System.Int32)` | WRT0002 `throw` | M6 U7 | `tests/corpus/m6/accepted/Statements.cs` |
| `M:Corpus.Rejected.Statements.CallsUnverified(System.Int32)` | WRT0005 `M:System.Math.Abs(System.Int32)` | M6 U7 | `tests/corpus/m6/refuted/Statements.cs` |
| `M:Corpus.Rejected.CheckedProject.Checked.Add(System.Int32,System.Int32)` | WRT0002 `checked arithmetic` | M6 U7 | `tests/corpus/m6/refuted/CheckedProject.cs` |
| `M:Corpus.Rejected.CheckedProject.Checked.Negate(System.Int32)` | WRT0002 `checked arithmetic` | M6 U7 | `tests/corpus/m6/refuted/CheckedProject.cs` |
| `M:Corpus.Rejected.CheckedProject.Checked.Narrow(System.Int64)` | WRT0002 `checked arithmetic` | M6 U7 | `tests/corpus/m6/refuted/CheckedProject.cs` |
| `M:Corpus.Rejected.Types.NullableParameter(Corpus.Rejected.Point)` | WRT0002 `nullable type` | M6 U17 | `tests/corpus/m6/accepted/Types.cs` |
| `M:Corpus.Rejected.Types.ReturnsNull` | WRT0002 `nullable type` | M6 U17 | `tests/corpus/m6/accepted/Types.cs` |
| `M:Corpus.Rejected.Statements.Decimals(System.Decimal)` | WRT0002 `decimal` | M6 U17 | `tests/corpus/m6/accepted/Statements.cs` |

Their keys are unchanged, and the M6 corpus README gives each one's M6 outcome.
`CallsUnmodelled` (`Math.Sign`) replaces `CallsUnverified`, so the corpus still has a WRT0005 member.
`ComparesWithNull` stays: its parameter is not declared nullable, so it is assumed non-null and comparing it with `null` is still rejected as `null`.