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
| `checked-project` | `rejected/CheckedProject.cs` | Compiled with overflow checking on. |

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
