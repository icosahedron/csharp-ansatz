# 8. Testing and cross-checks

> Part of the [M5a design](README.md). Decisions: KTD26 to KTD29, Key Decisions in the [plan](../plans/2026-11-03-0838-feat-m5a-meta-tactics-plan.md).

Tactics are untrusted: a bug in one makes a true theorem fail, never a false one pass.
The assurance work in M5a is therefore about the trusted parts it touches: the translator, which gains quantified statements and recursion, and the kernel, whose verdicts the design asks to be compared with other kernels before M5a closes.
This chapter covers the property-based differential tests, the tests for recursive methods, the kernel property tests, and the cross-checks.

## Differential tests become properties

M4's differential tests check each translated method against the compiled .NET method: every combination of boundary values, then 1,000 random inputs drawn with FsCheck's `Gen.Sample` (M4 docs/m4/07).
That is random testing.
A failure reports whatever input happened to fail, a fresh seed is drawn on every run, so a failure may not reproduce, and the count cannot be raised for a longer search.

M5a rewrites them as FsCheck properties (KTD26):

```csharp
[Fact]
public void TranslationAgreesWithTheClr() =>
    Prop.ForAll(Arbitraries.For(unit),                          // generators with shrinkers
                args => Model(unit, args) == Clr(unit, args))   // kernel: f args = r by Eq.refl
        .Check(Pbt.Config());
```

- **Shrinking.** `int` and `long` shrink toward 0 and the boundary values, records field by field, enums toward their first member, so a failure reports `MinValue` or `0`, not `-1216`.
- **Seeds.** `Pbt.Config()` pins a default seed, so every run tests the same inputs. `WARRANT_PBT_SEED=seed,gamma` replays a failure, and `WARRANT_PBT_SEED=random` draws a new one; the failure message prints the seed in that form. FsCheck 3.6.0 requires `gamma` to be odd.
- **Length.** `WARRANT_PBT_COUNT` sets the count, and `WARRANT_PBT_LONG=1` runs 10,000 cases per method for a nightly or pre-release run.
- **Boundaries.** The exhaustive boundary combinations stay a separate, deterministic test.

The CLR-agreement tests for the operator table get the same treatment.
The harness is proved by breaking the translator on purpose: swapping `Le` and `Lt` in `Switches.Matches` must fail with a shrunk input and a seed that replays.

## Recursive methods

A recursive unit is tested the same way, because `Nat.fix` computes in the kernel (chapter 3): `Sum 5 = 15` is admitted by `Eq.refl`, the method M4 uses for every unit.
Two things change for recursive units.

**Bounded inputs.** M4's generators always include `int.MinValue` and `int.MaxValue`.
For `Sum(int.MaxValue)` that is 2³¹ levels of recursion: the .NET side throws `StackOverflowException`, which cannot be caught and kills the test host, and the kernel side runs out of fuel.
Recursive units draw inputs whose measure is at most 1,000 to start, lowered by U15 to what its measurement of the kernel fuel per level of recursion allows.
An input over the fuel budget is reported as skipped, and a test whose inputs were all skipped fails, so the test cannot pass by testing nothing.

**A second evaluation.** On five inputs per recursive unit, the test also evaluates by rewriting (Key Decisions).
It rewrites `Sum 5` with `Sum.$eq_def`, reduces what does not mention `Sum` by `whnf`, finds the next call, and repeats, building

```lean
Sum 5 = (if 5 ≤ 0 then 0 else 5 + Sum 4)     -- Sum.$eq_def 5
      = 5 + Sum 4                              -- by reduction
      = …
      = 15
```

as one `Eq.trans` chain that the kernel checks.
It agrees with the `Eq.refl` result, and it exercises the equation lemma itself, which kernel evaluation never touches.

## Tactic-level properties

Three properties guard the parts of the tactics that must match Lean exactly:

- **Discrimination-tree keys.** For every simp entry in the sidecar, the keys Warrant computes equal the keys Lean exported (chapter 5).
- **omega's arithmetic.** C#'s constraint normalisation and combination agree with kernel evaluation of Init's `Lean.Omega` definitions on random inputs (chapter 6).
- **Emitted constants.** Every constant a tactic can emit is a bundle root (KTD29).

A debug flag in Meta kernel-checks every ground term it assigns, which catches an ill-typed assignment where it happens instead of at the final admission.

## Kernel property tests

Design §10.3 lists properties of the kernel that `tests/Warrant.Kernel.Tests/PropertyTests.cs` does not yet test (ticket `338bdc9`).
M5a adds them, reusing the existing generators of well-typed terms (KTD28):

- definitional equality is reflexive, symmetric and transitive on generated terms, including chains built from beta, delta and Nat-literal reductions;
- substituting a well-typed argument into a well-typed body gives a term of the instantiated type;
- instantiating universe parameters with well-formed levels keeps a declaration well-typed.

`docs/kernel.md` lists them with the existing ones.

## The certificate cross-check

`scripts/cross-check.sh` gains an M5a step, after M4's: `warrant verify tests/corpus/m5a/accepted --out m5a.ndjson`, then Lean's `lean-replay` re-checks every declaration.
That covers the quantified theorems, their simp and omega proofs, the recursive definitions with their decrease theorems and equation lemmas, and the generated `casesOn` and `ctorIdx`.
A tampered certificate, with one proof replaced, must be rejected by both kernels.

The script also stops downloading the Linux Lean build when an elan toolchain is installed, which fixes the second-run failure on Windows that M4 worked around with `LEAN_TOOLCHAIN_BIN`.

## Other kernels

Design §9 counts agreement between independent kernels as evidence for trusting Warrant's (ticket `d953584`).
So far only Lean's kernel has been compared.
`scripts/cross-kernel.sh` adds two more sources (KTD27):

- **The lean-kernel-arena.** It runs 33 independent kernels on 247 tests and publishes every verdict in `results.json`, with the tests in `lean-arena-tests.tar.gz`. The script downloads both at a recorded commit, runs `warrant check` on each test, and compares Warrant's verdict with the expected outcome and with the official (Lean's C++), nanoda and lean4lean verdicts. A test whose SHA-256 differs from the published one is skipped. No other kernel has to be built.
- **Ansatz.** Its `arena-check` tool reads lean4export files directly. The script runs it, with fuel raised to Warrant's 100M, on init-medium, the arena fixtures in `tests/data/arena/`, Warrant's own exports of them, the C#-built fixtures and the M5a certificates. Ansatz needs the Clojure CLI, which this machine does not have; without it, the Ansatz column says SKIPPED.

A decline or timeout is no verdict.
Every disagreement between verdicts gets an entry in `docs/kernel.md` explaining it, and a regression fixture.
Some are expected: Ansatz was built for Lean 4.33.1 and has not run full Init at 4.35.0; it admits mutual unsafe blocks one declaration at a time; and 30 arena tests are marked "either", where kernels may legitimately differ.
