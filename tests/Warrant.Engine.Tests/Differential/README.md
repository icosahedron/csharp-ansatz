# Differential tests

Every accepted corpus function is run on the CLR and in the model on the same inputs, and the two must agree (docs/m4/07, "Differential tests"; plan U10, KTD14).

- **The CLR side.** `CorpusAssembly` emits the same `CSharpCompilation` that extraction read and loads it into a collectible `AssemblyLoadContext`. That context resolves `Warrant` to the package image embedded in `Warrant.Frontend`, which is the image the compilation referenced.
- **The model side.** For each input, `ModelCheck` builds `f a₁ … aₙ`, with the receiver first for an instance member. It turns the .NET result `r` into a term (`Values`) and admits `@Eq.{1} T (f a₁ … aₙ) r`, proved by `@Eq.refl.{1} T (f a₁ … aₙ)`, into a scratch fork of the engine run's frozen environment. Read-back is used only to put the model's value in failure messages.
- **Inputs** (`Inputs`).
  - `int` and `long`: the seven boundary values of `Generators`, then its boundary-biased random values.
  - `bool`: both values.
  - Open enums: every named value plus unnamed values (`MinValue`, `MaxValue`, -1 and one past the largest named value).
  - Closed enums and classes: every member.
  - Records: every combination of their fields' values.

  Every combination of boundary values is tried, because no corpus function has more than three parameters (`AgreesOnEveryBoundaryCombination`, deterministic). Separately, each function's agreement is an FsCheck property over random inputs (`AgreesOnRandomInputs`; see "Properties" below).
- **Properties** (M5a KTD26, `Warrant.TestSupport/Pbt.cs`). `AgreesOnRandomInputs` checks `Prop.ForAll(inputs, args => model(args) = clr(args))` with `RandomInputsPerFunction` (1,000) cases per function. A failing input is shrunk: `int` and `long` toward 0 and the boundary values, `bool` to `false`, enums and closed values toward their first member, records field by field, and a function's arguments one at a time. The failure message shows the original and shrunk input, the disagreement, and a line `Replay with WARRANT_PBT_SEED=seed,gamma`. The same helper runs the CLR-agreement properties in `Warrant.Semantics.Tests`.

  | Variable | Effect |
  |---|---|
  | `WARRANT_PBT_SEED` | Unset: the pinned seed `20261103,1`, so every run tests the same inputs. `seed,gamma` (as a failure prints it): replay that run. `random`: a seed from the clock, which a failure prints. `gamma` must be odd. |
  | `WARRANT_PBT_COUNT` | Cases per property, for every property. |
  | `WARRANT_PBT_LONG=1` | 10,000 cases per property, unless `WARRANT_PBT_COUNT` is set. For a nightly or pre-release run: `WARRANT_PBT_LONG=1 dotnet test --filter Differential`. |

- **Other tests.**
  - `NullTests`: null arguments and null record fields on the CLR, and the non-null assumptions that exclude them.
  - `ClosedEqualityTests`: identity equality of closed-class instances (KTD11).
  - `TheoremStatementTests`: every theorem's claim computed on the CLR from a rewritten copy of the compilation, against the engine's outcome, including every combination of premise and conclusion for `Spec.Implies`.

## Measured cost

These measurements set the random-input count. They were taken on 2026-11-02 on the development machine (Windows 11, .NET 10.0.14, Debug build). Set `WARRANT_DIFFERENTIAL_COST=1` and run `DifferentialTests.MeasureTheCostOfAChecks` to measure again.

The fuel column is the fuel a fresh `TypeChecker` uses for the checks `Kernel.Add` makes on the theorem: its type, its proof and the definitional-equality check. The time column is the wall clock of the real check, which forks the environment and admits the theorem, averaged over the boundary inputs.

| Function | Boundary inputs | Fuel per check (mean / max) | ms per check (mean) |
|---|---|---|---|
| `Claims.Conversions.Narrow(long)` | 7 | 824 / 1096 | 0.51 |
| `Claims.Conversions.Widen(int)` | 7 | 821 / 1096 | 0.71 |
| `Corpus.Increments.Increment(int)` | 7 | 567 / 703 | 0.35 |
| `Corpus.Increments.IncrementLong(long)` | 7 | 567 / 703 | 0.32 |
| `Corpus.Locals.Bucket(int)` | 7 | 1383 / 1692 | 0.84 |
| `Corpus.Locals.Fee(int, bool)` | 14 | 773 / 1001 | 0.48 |
| `Corpus.Locals.NestedReturn(bool, bool)` | 4 | 158 / 190 | 0.20 |
| `Corpus.Locals.Shipping(int, bool, bool)` | 28 | 1031 / 1263 | 0.54 |
| `Corpus.Locals.Steps(int)` | 7 | 1049 / 1195 | 0.53 |
| `Payouts.PayoutRules.Payout(int, int, int)` | 343 | 1260 / 2176 | 0.70 |
| `Pricing.Discounts.Discounted(int, int)` | 49 | 1035 / 1556 | 0.63 |
| `Claims.ClaimStatuses.IsFinal(Claims.ClaimStatus)` | 4 | 115 / 119 | 0.16 |
| `Claims.ClaimStatuses.Priority(Claims.ClaimStatus)` | 4 | 81 / 81 | 0.11 |
| `Claims.Assignment.NeedsAlert` | 56 | 270 / 520 | 0.15 |
| `Claims.Outcomes.Code(Claims.Outcome)` | 2 | 176 / 207 | 0.30 |
| `Claims.Outcomes.Same(Claims.Outcome, Claims.Outcome)` | 4 | 100 / 113 | 0.13 |
| `Claims.Conversions.FromCode(int)` | 7 | 92 / 97 | 0.09 |
| `Claims.Conversions.IsUnnamed(Claims.PaymentStatus)` | 7 | 721 / 917 | 0.58 |
| `Claims.Conversions.StatusCode(Claims.PaymentStatus)` | 7 | 91 / 97 | 0.09 |
| `Claims.Payments.Validate(Claims.Payment)` | 343 | 984 / 1151 | 0.49 |
| `Claims.Records.Amount(Claims.Claim)` | 4802 | 213 / 233 | 0.09 |
| `Claims.Records.Distance(Claims.Point)` | 49 | 1814 / 2203 | 0.80 |
| `Claims.Records.Move(Claims.Point, int)` | 343 | 708 / 1030 | 0.26 |
| `Claims.Records.SamePlace(Claims.Point, Claims.Point)` | 2401 | 586 / 957 | 0.29 |

In all, 8,509 boundary checks used 432 fuel each on average and at most 2,203. The limit, `KernelLimits.Corpus`, is 100,000,000. A check takes between 0.1 and 0.9 ms.

**Random-input count.** With `RandomInputsPerFunction = 1000`, the M4 suite of 24 functions ran 8,509 boundary checks and 24,000 random ones, and every differential test together took about 15 seconds. Each function's checks take from 0.03 s (`StatusCode`) to 1.1 s (`SamePlace`), and loading the bundle and running the engine once take most of the rest. That is well within the budget of a few minutes. The count can grow about tenfold before the suite reaches two minutes. The boundary combinations are never reduced.

Measured again on 2026-11-03, with the random inputs as properties and 37 functions: the default run of every differential test takes about 20 seconds (each property from 0.02 s to 1.2 s), and the long run (`WARRANT_PBT_LONG=1`, 370,000 random checks) about 2.2 minutes.

## Recursive units

The M5a corpus's recursive functions (`Sum`, `Add`, `SumLong` in `tests/corpus/m5a/accepted/Recursion.cs`) are tested in `RecursiveDifferentialTests`, over the M5a accepted compilation (docs/m5a/08, "Recursive methods"; plan M5a U15).

- **Bounded inputs.** M4's boundary values would recurse 2³¹ times: the CLR would die of an uncatchable `StackOverflowException` and the kernel would run out of fuel. The parameter `Spec.Decreases` names is drawn from -1,000 to 1,000 (`MeasureBound`; a negative measure clamps to 0 and returns at once), and shrinks only within that range; the other parameters come from the M4 generators. `AgreesOnBoundedRandomInputs` checks 100 inputs per function (`RandomInputsPerFunction`) by kernel `Eq.refl`, as for M4 units: `Nat.fix` computes in the kernel.
- **Skipped inputs.** An input whose check runs out of kernel fuel is counted as skipped, not as a disagreement, and a test whose inputs were all skipped fails, so it cannot pass by testing nothing (`AnInputOverTheFuelBudgetIsSkipped`, `ATestWhoseInputsAreAllSkippedFails`). At the bound no corpus input is skipped.
- **A second evaluation.** `AgreesByRewritingWithTheEquationLemma` evaluates five inputs per function (measures -3, 0, 1, 5 and 12) by rewriting with `f.$eq_def` instead (`EquationEvaluator`): each call is rewritten with an instance of the equation lemma at its arguments' values, each `if` is decided and each argument evaluated by the kernel, and congruence (`congrArg`) carries the results out, all as one `Eq.trans` chain that the kernel checks as the proof of `f a = r`. It rewrites once per level of recursion and once where the guard stops it. `RewritingCatchesAWrongResult` checks that the chain for a wrong result is rejected.

### Measured fuel per level of recursion

Measured on 2026-11-04 on the development machine (Windows 11, .NET 10.0, Debug build), with `WARRANT_DIFFERENTIAL_COST=1` and `RecursiveDifferentialTests.MeasureTheFuelPerLevelOfRecursion`. The fuel is that of a fresh `TypeChecker` for the checks `Kernel.Add` makes on `f a = r` by `Eq.refl`; the measure parameter is the depth and the others are 1.

| Function | Levels | Fuel | Fuel per level | ms |
|---|---|---|---|---|
| `Corpus.Recursion.Add(int, int)` | 10 | 6,406 | 640 | 25 |
| `Corpus.Recursion.Add(int, int)` | 100 | 54,376 | 543 | 50 |
| `Corpus.Recursion.Add(int, int)` | 1,000 | 534,076 | 534 | 563 |
| `Corpus.Recursion.Sum(int)` | 10 | 6,348 | 634 | 5 |
| `Corpus.Recursion.Sum(int)` | 100 | 53,958 | 539 | 63 |
| `Corpus.Recursion.Sum(int)` | 1,000 | 530,058 | 530 | 612 |
| `Corpus.Recursion.SumLong(long)` | 10 | 6,348 | 634 | 3 |
| `Corpus.Recursion.SumLong(long)` | 100 | 53,958 | 539 | 38 |
| `Corpus.Recursion.SumLong(long)` | 1,000 | 530,058 | 530 | 569 |

The cost is linear, about 540 fuel per level after a fixed cost of about 1,000. At `KernelLimits.Corpus` (100,000,000) that allows about 185,000 levels, and at the build limit (20,000,000) about 37,000, so fuel does not lower the starting bound of 1,000: 1,000 levels use about 0.5% of the corpus fuel. Time does bind: about 0.6 s per check at full depth, so the default run of the three properties takes about 35 s, and the bound stays at 1,000 rather than rising. A long run (`WARRANT_PBT_LONG=1`) checks 10,000 inputs per function, about an hour for the three.
