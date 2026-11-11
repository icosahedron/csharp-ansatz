# Differential tests

Every accepted corpus function is run on the CLR and in the model on the same inputs, and the two must agree (docs/m4/07, "Differential tests"; plan U10, KTD14).

- **The CLR side.** `CorpusAssembly` emits the same `CSharpCompilation` that extraction read and loads it into a collectible `AssemblyLoadContext`. That context resolves `Warrant` to the package image embedded in `Warrant.Frontend`, which is the image the compilation referenced.
- **The model side.** For each input, `ModelCheck` builds `f a₁ … aₙ`, with the receiver first for an instance member. It turns the .NET result `r` into a term (`Values`) and admits `@Eq.{1} T (f a₁ … aₙ) r`, proved by `@Eq.refl.{1} T (f a₁ … aₙ)`, into a scratch fork of the engine run's frozen environment. Read-back is used only to put the model's value in failure messages.
- **Inputs** (`Inputs`).
  - `int` and `long`: the seven boundary values of `Generators`, then its boundary-biased random values.
  - `bool`: both values.
  - `decimal` (M6): the 24 `Generators.DecimalBoundaries` (`MinValue`, `MaxValue` and their neighbours, zero and negative zero at several scales, one at scales 0 to 2, the smallest positive value, the largest mantissa at scale 28, and values around the rounding boundary), then `Generators.DecimalValues`, which spreads sign, scale and mantissa width. A `decimal` is the term `Warrant.Decimal.lit negative mantissa scale (Eq.refl true) (Eq.refl true)`, as Semantics writes a literal, so the kernel's check compares representations: a result equal in value at another scale (`-1.0m` against `-1.00m`), or zero of the other sign, is a disagreement, though C#'s `==` would call them equal (`ADecimalResultIsComparedByRepresentation`).
  - Open enums: every named value plus unnamed values (`MinValue`, `MaxValue`, -1 and one past the largest named value).
  - Closed enums and classes: every member.
  - Records: every combination of their fields' values.
  - Nullable types (M6): `null` and the value type's values. One random value in four is `null`, and a failing value shrinks to `null` first.

  Every combination of boundary values is tried, because no corpus function has more than three parameters (`AgreesOnEveryBoundaryCombination`, deterministic). Separately, each function's agreement is an FsCheck property over random inputs (`AgreesOnRandomInputs`; see "Properties" below).
- **Properties** (M5a KTD26, `Warrant.TestSupport/Pbt.cs`). `AgreesOnRandomInputs` checks `Prop.ForAll(inputs, args => model(args) = clr(args))` with `RandomInputsPerFunction` (1,000) cases per function. A failing input is shrunk: `int` and `long` toward 0 and the boundary values, `bool` to `false`, `decimal` toward 0, 1 and -1 and to smaller mantissas (`Generators.ShrinkDecimal`), enums and closed values toward their first member, records field by field, and a function's arguments one at a time. The failure message shows the original and shrunk input, the disagreement, and a line `Replay with WARRANT_PBT_SEED=seed,gamma`. The same helper runs the CLR-agreement properties in `Warrant.Semantics.Tests`.

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

## M6 functions that can raise

`EffectDifferentialTests` compares the M6 corpus's functions without dependencies (`tests/corpus/m6`, compilations `accepted`, `refuted` and `checked-project`) with the CLR, on every boundary combination and on 1,000 random inputs each with the pinned seed (plan M6 U13, KTD21). Refuted members are compared too: agreement is about the model, not about whether a contract holds.

- **Pure functions** are checked as M4 functions are, and the CLR must not throw.
- **Raising functions** (`∀ {σ : Type} params, ClrM σ R`, plan U9) are run from an arbitrary world, and only the `Except` part is compared (#110): the kernel admits `@Eq.{2} (∀ σ : Type, σ → Except ClrExn R) (fun σ s => (StateT.run (ExceptT.run (f σ args)) s).1) (fun σ s => outcome)` by `Eq.refl`, where `outcome` is `Except.ok r` for the CLR's result `r`, or `Except.error e` for an `e` that stands for the CLR's exception.
- **Exceptions** (`ClrExceptions`, #78). Each `ClrExn` constructor maps to the CLR type it must match exactly: `overflow` to `OverflowException`, `divideByZero` to `DivideByZeroException`, `invalidOperation` to `InvalidOperationException`, `nullReference` to `NullReferenceException`, and `thrown k` to the type whose documentation-comment ID is `k`. A CLR exception therefore matches its implicit constructor, if it has one, or `thrown` of its own key: the CLR cannot tell `x.Value` on `null` from `throw new InvalidOperationException()`. `external` is plan U22's mock sentinel. `EveryClrExnConstructorIsMapped` fails if the bundle's `ClrExn` gains a constructor.
- **`Spec.Assert`** (#186). `assertFailed` has no CLR counterpart: `Spec.Assert` is `[Conditional]` and does nothing at run time. An input on which the model fails an assertion is skipped and counted, and a function fails unless at least a quarter of its inputs, and at least one, were evaluated (`EffectRun.MinimumEvaluatedShare`, #144). No corpus function compared today has a `Spec.Assert`, so none is skipped; `AnInputThatFailsASpecAssertIsSkippedAndCounted` and `AFunctionWithTooFewEvaluatedInputsFails` check the rule on inline functions.
- **`decimal`** (U21). The `decimal` functions, and those taking `Corpus.M6.Payment`, which has a `decimal` field, are compared like the others, with results compared by representation (see "Inputs" above). A `Payment`'s boundary values are every combination of its `int` and `decimal` fields' (7 × 24 = 168), so `SameAmount` and `SamePayment`, with two, check 28,224 boundary inputs each.
- **Skipped functions.** Functions whose translation is not on the branch yet are listed with the unit that brings them: the five members of `Contracts` (U10). `EveryM6FunctionWithoutDependenciesIsComparedOrSkippedForAReason` pins the two lists against `expected.json` and fails as soon as a skipped function translates. The functions in `Payments.cs` and `Dependencies.cs` are plan U22's.

### Measured cost

Measured on 2026-11-11 on the development machine (Windows 11, .NET 10.0.14, Debug build), with `WARRANT_DIFFERENTIAL_COST=1` and `EffectDifferentialTests.MeasureTheCostOfAnM6Check`. Fuel and time are as in the M4 table; for a raising function the theorem is the `Eq.{2}` one above.

| Function | Raising | Boundary inputs | Fuel per check (mean / max) | ms per check (mean) |
|---|---|---|---|---|
| `Corpus.Rejected.Arithmetic.Halve(int)` | no | 7 | 930 / 1080 | 1.83 |
| `Corpus.Rejected.Arithmetic.Remainder(int)` | no | 7 | 880 / 1035 | 0.60 |
| `Corpus.Rejected.Statements.Throws(int)` | yes | 7 | 1002 / 1200 | 0.96 |
| `Corpus.M6.Effects.Biggest(int, int)` | no | 49 | 904 / 1210 | 0.58 |
| `Corpus.M6.Effects.Smallest(long, long)` | no | 49 | 904 / 1210 | 0.51 |
| `Corpus.M6.Effects.Guard(int)` | yes | 7 | 1096 / 1276 | 0.91 |
| `Corpus.Rejected.Types.NullableParameter(Corpus.Rejected.Point?)` | no | 50 | 188 / 201 | 0.13 |
| `Corpus.Rejected.Types.ReturnsNull()` | no | 1 | 47 / 47 | 0.77 |
| `Corpus.M6.Nullables.OrZero(int?)` | no | 8 | 116 / 122 | 0.14 |
| `Corpus.M6.Nullables.OrDefault(long?)` | no | 8 | 116 / 122 | 0.17 |
| `Corpus.M6.Nullables.Wrap(int)` | no | 7 | 73 / 78 | 0.14 |
| `Corpus.M6.Nullables.ValueWhenKnown(int?)` | yes | 8 | 394 / 403 | 0.53 |
| `Corpus.Rejected.Statements.Decimals(decimal)` | no | 24 | 228 / 228 | 0.13 |
| `Corpus.M6.Decimals.AtLeastOne(decimal)` | no | 24 | 904 / 952 | 0.51 |
| `Corpus.M6.Decimals.SameAmount(Corpus.M6.Payment, Corpus.M6.Payment)` | no | 28224 | 888 / 1044 | 0.46 |
| `Corpus.M6.Decimals.SamePayment(Corpus.M6.Payment, Corpus.M6.Payment)` | no | 28224 | 808 / 1412 | 0.37 |
| `Corpus.M6.Decimals.Negate(decimal)` | no | 24 | 412 / 414 | 0.28 |
| `Corpus.M6.Decimals.Largest(decimal, decimal)` | no | 576 | 981 / 1137 | 0.52 |
| `Corpus.M6.Decimals.Smallest(decimal, decimal)` | no | 576 | 1082 / 1236 | 0.55 |
| `Corpus.M6.Decimals.Size(decimal)` | no | 24 | 386 / 395 | 0.18 |
| `Corpus.M6.Nullables.IsMissing(Corpus.M6.Payment?)` | no | 169 | 266 / 272 | 0.14 |
| `Corpus.M6.Nullables.Use(Corpus.M6.Payment)` | no | 168 | 269 / 274 | 0.11 |
| `Corpus.M6.Nullables.Guarded(Corpus.M6.Payment?)` | yes | 169 | 740 / 747 | 0.71 |
| `Corpus.M6.Nullables.IdOrZero(Corpus.M6.Payment?)` | yes | 169 | 729 / 736 | 0.71 |
| `Corpus.M6.Refuted.Decimals.AddFee(decimal)` | yes | 24 | 2221 / 2615 | 1.45 |
| `Corpus.M6.Refuted.Decimals.Difference(decimal, decimal)` | yes | 576 | 2541 / 9742 | 1.72 |
| `Corpus.Rejected.Arithmetic.CheckedAdd(int, int)` | yes | 49 | 1719 / 2300 | 1.15 |
| `Corpus.Rejected.Statements.CallsUnverified(int)` | yes | 7 | 1336 / 1699 | 0.89 |
| `Corpus.M6.Refuted.Effects.Ratio(int, int)` | yes | 49 | 1544 / 2052 | 0.98 |
| `Corpus.M6.Refuted.Effects.Magnitude(long)` | yes | 7 | 1336 / 1699 | 1.09 |
| `Corpus.M6.Refuted.Nullables.Read(int?)` | yes | 8 | 300 / 310 | 0.41 |
| `Corpus.M6.Refuted.Nullables.Cast(long?)` | yes | 8 | 300 / 310 | 0.42 |
| `Corpus.M6.Refuted.Nullables.Use(Corpus.M6.Refuted.Payment)` | no | 7 | 93 / 98 | 0.20 |
| `Corpus.M6.Refuted.Nullables.IdOf(Corpus.M6.Refuted.Payment?)` | yes | 8 | 453 / 467 | 0.88 |
| `Corpus.M6.Refuted.Nullables.Unchecked(Corpus.M6.Refuted.Payment?)` | yes | 8 | 480 / 498 | 0.69 |
| `Corpus.Rejected.CheckedProject.Checked.Add(int, int)` | yes | 49 | 1719 / 2300 | 1.57 |
| `Corpus.Rejected.CheckedProject.Checked.Negate(int)` | yes | 7 | 1382 / 1557 | 1.48 |
| `Corpus.Rejected.CheckedProject.Checked.Narrow(long)` | yes | 7 | 1371 / 1985 | 1.38 |

In all, 59,393 boundary checks used 865 fuel each on average and at most 9,742 (on `Difference`), well under `KernelLimits.Corpus`. A raising check costs about twice an M4 one, because the run unfolds the monad's `bind` and `StateT.run`; a raising `decimal` sum or difference about twice that again. With 38 functions the M6 tests check 59,393 boundary inputs and 38,000 random ones, every one evaluated (none skipped). The boundary inputs are dominated by `SameAmount` and `SamePayment` (28,224 each, about 11 to 14 s each alone); each random-input property takes 0.03 to 3.5 s, about 36 s together. The default run of every differential test, M4, M5a and M6, took 1.7 minutes on the same machine, the recursive tests included, so the count of 1,000 stays.

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
