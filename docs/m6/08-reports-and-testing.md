# 8. Reports and testing

> Part of the [M6 design](README.md). Decisions: KTD3, KTD20, KTD21 and KTD24. Units: U12, U20 (report), U13, U22
> (differential tests), U14 (corpus, cross-check, exit tests).

## What the report says a proof rests on

A proof under contracts is only as good as the contracts, and some of what it assumes is not checked anywhere.
The assumption report (design §8.4; `warrant verify --report <dir>` writes `report.md` and `report.json`) lists it,
unit by unit.
M6 adds four kinds (KTD20), rendered by `src/Warrant.Engine/Reports/` under two new headings:

| Kind | Heading | Text, from the corpus |
|---|---|---|
| `CallerPrecondition` | Assumed (contracts) | `S.Ratio(int, int)'s Spec.Requires is assumed on entry: verified callers prove it at each call, but it is not checked at run time or at call sites Warrant does not verify` |
| `CalleeContract` | Assumed (contracts) | `S.G(int) returns only values its Spec.Ensures allows, as Warrant proved under its own assumptions; this method proves its Spec.Requires at each call` |
| `ExternalContract` | Assumed (contracts) | `Every implementation of …IPaymentStore.GetPayment(int) keeps its contract: Spec.Ensures<Payment?>(r => r is null \|\| r.Id == id)`; for a `=> default!` member, `… keeps its contract, which states nothing: a call may return any value or throw` |
| `MayThrow` | Assumed (exceptions) | `…Closed(int) may throw System.InvalidOperationException (the throw at accepted/Effects.cs:40); its proof says nothing about a call that ends in it` |

- `CallerPrecondition` is a method's own `Spec.Requires`. `Spec` calls are compiled out (chapter 4), so nothing checks
  it at run time, and a caller Warrant does not verify can pass anything. A method that unverified code calls and that
  must not misbehave on bad input should check it with a guard that throws, which the proof covers, rather than rely on
  `Spec.Requires`.
- `ExternalContract` quotes the contract class's `Spec` calls (design §8.4) and adds "this method proves its
  Spec.Requires at each call" when the member has one.
- `MayThrow` is each explicit `throw` the walker could not show unreachable, each call to a dependency (whose exception
  the contract allows), and each call to a verified callee that may throw, naming the call and the callee's throw site
  (#70). A throw proved unreachable is not listed (#92). Its subject carries VIR node IDs, not lines
  (`MayThrowSubject`), so a cached outcome renders at the current lines.
  The list does not depend on how the contract was proved (#229): for a `[ProofFor]` script it comes from every walk the
  script's `Tactic.VcGen()` steps ran, and for a script that ran none from the walk the default procedure would make,
  its proof discarded; if that walk cannot finish, every explicit `throw`, dependency call and verified callee with a
  contract in the method is listed instead. A unit whose `$contract` is admitted from its cached certificate keeps the
  cached list, even when another of its proofs is built again (#231).
- The existing `NonNull` kind covers each dependency a method calls through, each non-nullable reference a dependency
  returns, the `Task` included, under "Assumed (parameters)": `store is not null`, `store.GetPayment() is not null`.
  Nullable-reference annotations remain assumptions (design §12 Q11, decided by KTD20); a value declared `T?` is
  checked instead (chapter 2).

In `report.json` the kinds are `caller-precondition`, `callee-contract`, `external-contract` and `may-throw`, and a
contract unit is `contract`.
The global line about overflow now names both regions ("Arithmetic wraps on overflow, except in a checked region, where
it throws (overflow checking is off)", #147), and the bundle line names the M6 models.
`ProcessPayment`'s and `Closed`'s blocks are checked in as `tests/corpus/m6/ProcessPayment.report.txt` and
`Closed.report.txt`, and the engine's `ReportTests` and the CLI's `M6CorpusTests` compare them with the report they
build.

A unit's status word is still M5a's: a function whose definition and contract obligation are admitted is `TRANSLATED`,
and `VERIFIED` is for theorems.
The CLI's per-unit lines say `translated` for it, and the summary line counts theorems only, so a run whose contracts
fail ends with "0 not proved" and exit code 1 (#225); the diagnostics and the exit code are right.

## Differential tests

The models are trusted, so they are tested against the CLR in three layers.

**CLR agreement** compares each model operation with the CLR on boundary and random operands (chapters 2 and 3).

**Effects** (U13, `Differential/EffectDifferentialTests`).
Every M6 corpus function without dependencies, accepted and refuted alike, runs on the CLR and in the kernel on every
boundary combination and on 1,000 random inputs with the pinned seed.
A raising function runs from an arbitrary world, and the kernel admits, by `Eq.refl`, that its `Except` part equals the
CLR's outcome (#110).
Each `ClrExn` constructor maps to the CLR exception type it must match exactly: `overflow` to `OverflowException`,
`divideByZero` to `DivideByZeroException`, `invalidOperation` to `InvalidOperationException`, `nullReference` to
`NullReferenceException`, and `thrown k` to the type whose key is `k`, not a base type (#78).
The mapping runs from the model to the CLR because the CLR cannot tell `x.Value` on null from
`throw new InvalidOperationException()`.
`assertFailed` has no CLR counterpart, since `Spec.Assert` does nothing at run time: an input on which the model fails an
assertion is skipped and counted, and a function fails unless at least a quarter of its inputs were evaluated (#186,
#144).
`decimal` results are compared by representation (chapter 3).
`EveryM6FunctionWithoutDependenciesIsComparedOrSkippedForAReason` pins the compared list; nothing is skipped.

**Dependencies** (U22, `Differential/DependencyDifferentialTests`).
A method with dependencies runs against contract-satisfying mocks on both sides, as reply tapes (KTD21).
The model runs in the world `Nat`, the call index, with one operation per member that returns the tape's reply for call
`i` when call `i` went to that member of that dependency with exactly the CLR's arguments (decided by the kernel), and
otherwise throws a marked error; the final world must equal the CLR's number of calls.
So a model that calls the wrong member, with other arguments, in another order, or a different number of times fails
(`ACallWithOtherArgumentsOrInAnotherOrderIsCaught`). Arguments of nullable or closed types are not compared yet; no
corpus member passes one.
On the CLR side, a mock class per contracted interface replays the same tape in a rewritten copy of the compilation
(`ContractCompilation`), which only adds members: `DispatchProxy` cannot proxy interfaces from the collectible load
context the tests use, which the plan did not foresee.
A reply is the first candidate whose member `Ensures`, run on the CLR, holds: half drawn from the return type's
generator, half built from the call's arguments; a call with no such reply within 64 candidates fails the test.
A mock that throws throws `MockException`, which `ClrExn.external` must match and nothing else.
`ProcessPayment`, `QuantityOf`, `Counted` and `Reserved` agree with the CLR on 112 boundary runs (7 inputs × 16 tapes)
and 1,000 random runs each, including scripted tapes for `ProcessPayment`: an invalid id, `GetPayment` returning null, a
pending payment that is saved as processed, a payment that is not pending, a zero amount, `GetPayment` throwing,
`SavePayment` throwing, and two calls that see different payments.

**Contracts on the CLR** (U22, `Differential/ContractStatementTests`, #94).
Every accepted method whose obligation is proved runs on the CLR alone on 1,000 inputs that satisfy its `Requires`:
every normal return must keep its `Ensures`, every exception must be an explicit throw or the mock sentinel, and every
dependency call must keep the member's `Requires`.
Fewer than 100 satisfying inputs fails the test (#185).
This checks the statement against the CLR, independently of the proof: a translation that made a contract easier to prove
than the C# deserves would show up here.
One weak spot: an exception counts as explicit when its type matches a `throw` in the source, so an implicit exception of
the same type in the same method would be missed; no corpus method has one.

## The corpus

`tests/corpus/m6/` is the exit criterion as files (KTD24), in the M4 corpus's layout: `accepted/`, `refuted/` and
`rejected/`, and `expected.json` with each member's outcome and each compilation, five of them (`accepted`, `refuted`,
`refuted-dependencies`, `rejected`, `checked-project`).
It holds 147 members.
`tests/corpus/m6/README.md` lists every file, what each member is for, and the members that moved from the M4 corpus
(chapter 4).

- `accepted/` proves under the default procedure: the payment example and its pure parts, contracts without
  dependencies, `Spec.Assert` with a script, a `[ProofFor]` script that starts with `Tactic.VcGen()`, nullable and
  `decimal` members, `year % 4` in a pure method, a method that throws on every path (`Closed`), and `Found`, whose
  `Ensures` holds only through `GetPayment`'s contract.
- `refuted/` fails with WRT0001, and `expected.json` gives the failing VC's kind and line, the number of failing VCs and
  the goal: implicit exceptions nothing rules out, `Ratio` with only `Requires(b != 0)`, `x / -1`, a caller that passes 0
  to a method that requires a non-zero argument, false `Ensures` with and without a `[ProofFor]` script, a failing
  `Spec.Assert`, a contradictory `Requires`; and in `refuted-dependencies`, `GetPayment(id + 1)`, reliance on
  `SavePayment`'s empty contract, two calls to `GetPayment(id)` expected to agree (with and without a script), an
  unsatisfiable contract member, and an awaited call that breaks its callee's `Requires` (`Steps.Run`, #228).
- `rejected/` has one member per construct M6 still rejects, among them `try`/`catch`, a `%`-based recursive `Gcd`, a
  theorem that calls a raising method or divides by a variable, `_ = M();` and `var t = M(); await t;`, and each step of
  the contract-class shape.

The engine (`CorpusTests.EveryM6MemberGetsItsExpectedOutcome`), extraction, the analyzer parity tests, translation
(`MonadicTranslationTests`, `DependencyObligationTests`), the differential tests and the CLI (`M6CorpusTests`, which runs
`warrant verify` on `accepted/` and `refuted/` and checks each refuted member's line and kind) all read it.

## Lean's kernel agrees

`scripts/cross-check.sh` has M6 rows (R13):

```text
M6 corpus                    -         accept    accept         ok
M6 refuted                   -         reject    accept         ok
M6 rejected                  -         reject    accept         ok
M6 checked-project           -         reject    accept         ok
M6 tampered                  -         reject    reject         ok

all verdicts agree
```

`warrant verify tests/corpus/m6/accepted --out` must exit 0, its certificate must hold `ProcessPayment`'s
`$contract` theorem, and Lean's kernel (`tools/lean-replay`) must accept the certificate, the bundle with its `Std.Do`
closure included.
The refuted and rejected compilations must fail to verify, and Lean must accept what Warrant admitted from them; the
overflow-checking file is translated with `--check-overflow` (#111).
A copy of the accepted certificate with `ProcessPayment`'s proof replaced by another theorem's must be rejected by both
kernels.
On Windows (Git Bash, 2026-11-11) every row agrees.

## The build

`tests/Warrant.Build.Tests` adds a contract-bearing sample: a division under its precondition, and design §5.2's payment
flow through a dependency whose contract class is in the project, with `async`.
It verifies, and its refuted twin fails at the division, under `dotnet build`, Visual Studio 2026's MSBuild and Visual
Studio 2022's MSBuild (`AContractBearingProject…VerifiesWith…AndItsRefutedTwinFailsAtTheDivision`, #106).
With `WARRANT_BUILD_INTEGRATION=1` the whole build matrix passes, 65 of 65.

## The exit criterion as tests

`dotnet test --filter M6Exit` runs four facts, one per Success Criterion except the private-codebase one (KTD24):

| Fact | Project | Criterion |
|---|---|---|
| `ThePurePartsOfThePaymentExampleVerify` | `Warrant.Cli.Tests` | the records and enums, `Validate` and the contract class's members verify with no diagnostic |
| `ProcessPaymentVerifiesWithItsStoreAsAHypothesisAndItsCertificateChecks` | `Warrant.Cli.Tests` | `ProcessPayment` verifies, and Warrant's kernel re-checks its certificate (Lean's half is the cross-check row above) |
| `DifferentialTestsWithContractSatisfyingMockedExternalsPass` | `Warrant.Engine.Tests` | the dependency differential tests |
| `EveryNewModelOperationAgreesWithTheClrOnGeneratorsWithZeroDivisorsMinValueByMinusOneAndRescaledDecimals` | `Warrant.Semantics.Tests` | CLR agreement of every new model |

The private-codebase criterion (its blocked candidates that need only R1 to R4 translate, and one verifies with a stated
`Spec.Ensures`) is checked by hand in that codebase and reported without naming its code, so it is not a test here.

## Start time

U14 measured server start with the complete M6 bundle against M5b's in one session, as KTD3 requires: 4,053 ms against
2,807 ms on the reference workstation, under the 5 s threshold (chapter 1, `tests/data/README.md`).
Warm, cached and rechecked requests are measured by `scripts/measure-m5b.sh` as in M5b; M6 did not set new baselines
for them.
