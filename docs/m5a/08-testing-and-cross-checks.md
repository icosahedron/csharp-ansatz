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
    Pbt.Check(Prop.ForAll(Inputs.Arbitrary(unit.Parameters),     // generators with shrinkers
                          args => Model(unit, args) == Clr(unit, args)),  // kernel: f args = r by Eq.refl
              RandomInputsPerFunction);                          // appends the replay seed on failure
```

- **Shrinking.** `int` and `long` shrink toward 0 and the boundary values, records field by field, enums toward their first member, so a failure reports `MinValue` or `0`, not `-1216`.
- **Seeds.** `Pbt.Config` pins a default seed, `20261103,1`, so every run tests the same inputs. `WARRANT_PBT_SEED=seed,gamma` replays a failure, and `WARRANT_PBT_SEED=random` draws a new one; the failure message ends with `Replay with WARRANT_PBT_SEED=seed,gamma`. FsCheck 3.6.0 requires `gamma` to be odd.
- **Length.** `WARRANT_PBT_COUNT` sets the count, and `WARRANT_PBT_LONG=1` runs 10,000 cases per method for a nightly or pre-release run.
- **Boundaries.** The exhaustive boundary combinations stay a separate, deterministic test.

The CLR-agreement tests for the operator table get the same treatment.
The harness was proved by breaking the translator on purpose and reverting the change: with `Le` and `Lt` swapped in `Switches.Matches`, the properties failed with a shrunk input and a seed that replayed.
Only the M4 corpus's `Band` caught that mutation; `Bucket`'s relational patterns test at 5 and 9, which the boundary values do not hit. That is a known gap in the generators.

The default run of every differential test, 37 functions, takes about 20 seconds; the long run takes about 2.2 minutes (`tests/Warrant.Engine.Tests/Differential/README.md`).

## Recursive methods

A recursive unit is tested the same way, because `Nat.fix` computes in the kernel (chapter 3): `Sum 5 = 15` is admitted by `Eq.refl`, the method M4 uses for every unit.
Two things change for recursive units.

**Bounded inputs.** M4's generators always include `int.MinValue` and `int.MaxValue`.
For `Sum(int.MaxValue)` that is 2³¹ levels of recursion: the .NET side throws `StackOverflowException`, which cannot be caught and kills the test host, and the kernel side runs out of fuel.
Recursive units draw the parameter that `Spec.Decreases` names from -1,000 to 1,000 (a negative measure clamps to 0 and returns at once), 100 inputs per function, and the other parameters from M4's generators.
U15 measured the kernel fuel per level of recursion: about 540, linearly, so 1,000 levels use about 0.5% of the corpus fuel. Time binds instead (about 0.6 s per check at full depth in a Debug build), so the bound stays at 1,000.
An input over the fuel budget is reported as skipped, and a test whose inputs were all skipped fails, so the test cannot pass by testing nothing; at the bound, no corpus input is skipped.

**A second evaluation.** On five inputs per recursive unit (measures -3, 0, 1, 5 and 12), the test also evaluates by rewriting (Key Decisions).
It rewrites `Sum 5` with an instance of `Sum.$eq_def`, decides the `if` and evaluates the arguments in the kernel, carries the results out with `congrArg`, finds the next call, and repeats, building

```lean
Sum 5 = (if 5 ≤ 0 then 0 else 5 + Sum 4)     -- Sum.$eq_def 5
      = 5 + Sum 4                              -- by reduction
      = …
      = 15
```

as one `Eq.trans` chain that the kernel checks.
It agrees with the `Eq.refl` result, and it exercises the equation lemma itself, which kernel evaluation never touches; a test checks that the chain for a wrong result is rejected.

## Tactic-level properties

Three properties guard the parts of the tactics that must match Lean exactly:

- **Discrimination-tree keys.** For every simp entry in the sidecar, all 346, the keys Warrant computes equal the keys Lean exported (chapter 5).
- **omega's arithmetic.** C#'s constraint normalisation and combination agree with kernel evaluation of Init's `Lean.Omega` definitions on random inputs (chapter 6).
- **Emitted constants.** Every constant a tactic can emit is a bundle root (KTD29).

A debug flag in Meta (`MetaM.DebugCheckAssignments`) kernel-checks every ground term it assigns, which catches an ill-typed assignment where it happens instead of at the final admission.

## Kernel property tests

Design §10.3 lists properties of the kernel that `tests/Warrant.Kernel.Tests/PropertyTests.cs` does not yet test (ticket `338bdc9`).
M5a adds six, reusing the existing generators of well-typed terms (KTD28):

- definitional equality is reflexive, symmetric and transitive on generated terms, including chains built from beta, delta and Nat-literal reductions (`DefinitionalEqualityIsReflexive`, `…IsSymmetric`, `…IsTransitive`);
- instantiating a well-typed body with well-typed arguments, as de Bruijn indices or as free variables, gives a term of the instantiated type (`InstantiationPreservesTyping`, `SubstitutionPreservesTyping`);
- instantiating universe parameters with well-formed levels keeps a declaration well-typed (`UniverseInstantiationPreservesWellTypedness`).

They found no kernel bug. `docs/kernel.md` lists them with the existing ones.

## The certificate cross-check

`scripts/cross-check.sh` gains an M5a step, after M4's: `warrant verify tests/corpus/m5a/accepted --out m5a.ndjson`, then Lean's `lean-replay` re-checks every declaration.
That covers the quantified theorems, their simp and omega proofs, the recursive definitions with their decrease theorems and equation lemmas, and the generated `casesOn` and `ctorIdx`.
A tampered certificate, with one proof replaced, must be rejected by both kernels.

The scripts find the Lean toolchain through `scripts/lib/lean-toolchain.sh`, which U19 changes so that the cross-check runs on Windows without setting `LEAN_TOOLCHAIN_BIN`, the workaround M4 needed.

## Other kernels

Design §9 counts agreement between independent kernels as evidence for trusting Warrant's (ticket `d953584`).
So far only Lean's kernel has been compared.
`scripts/cross-kernel.sh` adds two more sources (KTD27):

- **The lean-kernel-arena.** It publishes every kernel's verdict in `results.json`, with the tests in `lean-arena-tests.tar.gz`. The script downloads both at a recorded commit, runs Warrant and Lean's kernel on each test, and compares Warrant's verdict with the expected outcome and with the official (Lean's C++), nanoda and lean4lean verdicts. A test whose SHA-256 differs from the published one is skipped. No other kernel has to be built. The 30 tests marked "either", where kernels may legitimately differ, are not in the tarball.
- **Ansatz.** Its `arena-check` tool reads lean4export files directly. The script runs it, with fuel raised to Warrant's 100M, on the arena tests, init-medium, the arena fixtures in `tests/data/arena/`, Warrant's own exports of them, the C#-built fixtures and the translated corpus. Ansatz needs the Clojure CLI and a built Ansatz checkout; without them, the Ansatz column says SKIPPED. The recorded run used the Clojure CLI (deps.clj 1.12.6.1673) and Ansatz `4ff56b8`.

A decline or timeout is no verdict.
Every disagreement between verdicts has an entry in `docs/kernel.md` explaining it, with a regression fixture where Warrant's behaviour needs one.
Warrant's verdict matched the expected outcome on every row. The run found two bugs in other kernels: Ansatz accepts a proof of `False` built on forged quotient declarations, and nanoda's published verdict accepts an inductive type that uses an undeclared universe. Both files are now fixtures in `tests/data/arena/`.
Other disagreements are expected: Ansatz targets Lean 4.33.1, and it admits recursive unsafe definitions one declaration at a time.
