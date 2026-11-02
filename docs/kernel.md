# The Warrant kernel

`src/Warrant.Kernel` is a port of the Lean 4 kernel (`src/kernel/` in
[leanprover/lean4](https://github.com/leanprover/lean4)), made against tag
**v4.33.1** (commit `819816b`), the toolchain that produced the init-medium test
export, and re-diffed against **v4.35.0**, the current pin. The only kernel
change between the two removes native reduction (`Lean.reduceBool` and
`Lean.reduceNat`), which Warrant never supported, so the port is unchanged. Ansatz's Java kernel was a second reference. The port follows the C++
closely, function by function, so that each part can be compared directly with
the original.

## File map

| Lean 4 (C++) | Warrant (C#) | Contents |
|---|---|---|
| `level.cpp` | `LevelOps.cs` | `mk_max`/`mk_imax`, `normalize`, `is_equivalent`, `is_geq`, instantiate |
| `instantiate.cpp`, `abstract.cpp`, `replace_fn.cpp`, `expr.cpp` (part) | `ExprOps.cs` | bound-variable substitution, abstraction, lift/lower, level-parameter instantiation, beta, `infer_implicit` |
| `local_ctx.cpp` | `LocalContext.cs` | free-variable declarations, `mk_pi`/`mk_lambda` |
| `type_checker.cpp` | `TypeChecker.cs` (inference), `TypeChecker.Whnf.cs` (reduction, Nat extensions), `TypeChecker.DefEq.cs` (definitional equality) | the type checker |
| `inductive.h` | `TypeChecker.Whnf.cs` | iota reduction, K-like reduction, structure eta for recursor majors |
| `quot.h`, `quot.cpp` | `TypeChecker.Whnf.cs`, `Kernel.cs` (`Quotient`) | quotient reduction and the quotient package |
| `environment.cpp` | `Kernel.cs` | admission of axioms, definitions, theorems, opaques, mutual definitions |
| `inductive.cpp` | `Inductive.cs` | inductive admission, recursor generation, nested-inductive elimination and restoration |
| (Lean's `Replay`) | `ExportChecker.cs` | re-checking lean4export data: rebuilds kernel declarations and compares generated constants with exported ones |

## Expression equality

The C++ kernel's `==` on expressions (`is_equal`) ignores binder names and binder
info. Its caches and quick checks are keyed on that equality, and so are
Warrant's (`Expr.AlphaEquals`, `Expr.AlphaComparer`). `Expr.Equals` is exact
equality, which the export round-trip tests need.

## Deliberate differences from Lean

| Lean 4 | Warrant | Why |
|---|---|---|
| No step limit (only heartbeats/recursion depth from the caller) | **Fuel**: each call of the core procedures costs a step; 20M interactive, 100M for corpora. Running out rejects as a *resource limit*, never as a type error | Checking must terminate inside a build server. |
| `Lean.reduceBool`/`Lean.reduceNat` run compiled code | **Not supported**: they never reduce, so declarations relying on them (`native_decide`) are rejected | Warrant has no compiler, and trusting one would enlarge the trusted base. |
| Recursion on large native stacks | Recursion on a 512 MB-stack thread (`KernelThread`); stack exhaustion becomes a resource limit | Same algorithm, no stack-overflow crash. |
| The local context is restored after leaving a binder | Free-variable declarations accumulate for the life of a type checker | Names are globally unique, so this is unobservable; it avoids copying. |
| `Name.appendAfter` strips macro scopes first | Not modelled | Only affects generated binder names, which are compared up to alpha-equivalence. |

## How exported data is checked

lean4export lists *constants*, while the kernel admits *declarations*.
`ExportChecker` rebuilds the declarations the way Lean's own replay does:

- **Inductive blocks** are admitted from their types and constructors only. The
  kernel derives constructors, recursors (including the `I.rec_n` auxiliaries of
  nested types) and their computation rules. Each exported constant must equal the
  generated one up to binder names, and every generated constant must appear in
  the export.
- **Quotients**: the first exported quotient constant triggers the kernel's
  quotient package (which checks `Eq`). All four exported constants must match
  the generated ones.
- **Mutual unsafe/partial definitions** are buffered until the whole block has
  arrived, then admitted together.

## Results (milestone 2)

| Corpus | Result | Time |
|---|---|---|
| **full Init** (Lean 4.33.1): 57,977 declarations, 59,433 constants (348 MB export) | **all accepted** | ≈73 s |
| **full Init** (Lean 4.35.0): 57,919 declarations, 59,349 constants (346 MB export) | **all accepted** | ≈41 s |
| init-medium (Lean 4.33.1 Init subset): 4,631 declarations, 5,118 constants | all accepted | ≈3 s |
| lean4export `Nat.add_succ` example (format 3.0.0) | all accepted | <0.1 s |
| arena `001_basicDef`, `sparse-name-index` | accepted | |
| arena `002_badDef` | `badDef` rejected (type mismatch) | |
| arena `141_falseFromUnsafe` | `unsafeLoop` accepted, `falseFromUnsafe` rejected, as in Lean | |
| arena `proj-of-subst-prop` (lean4#14807) | `PR14806Subst.observe` rejected; Init closure accepted | |
| arena `rec-of-subst-prop` (lean4#14847) | `Issue.forallFalse` rejected; Init closure accepted | |

The kernel tests also tamper with real declarations: wrong proofs, a theorem that
is not a proposition, undefined or duplicate universe parameters, non-positive
and universe-too-big inductives, a flipped K flag, swapped computation rules, a
missing recursor, wrong field counts and a forged quotient constant. Each must be
rejected for the expected reason, and each has a positive control that must be
accepted.

The full Init export is too large to commit. `scripts/export-lean-library.sh`
reproduces it (Lean 4.35.0, lean4export `5a9a355`), and the opt-in test
`AcceptsFullInit` checks it when `WARRANT_INIT_EXPORT` points to the file.
(Ansatz's documentation quotes 54,335 declarations for an earlier Init export.)

**Not yet run:** Mathlib (Ansatz reports 707,508 declarations at v4.33.1). The same script can
export it from a Mathlib checkout.

## Cross-kernel checks (milestone 3)

Warrant's verdicts are compared with **Lean's own kernel**, using
[`tools/lean-replay`](../tools/lean-replay/README.md): lean4export's parser plus
`Lean.Environment.replay`. Run everything with `scripts/cross-check.sh`.

| Check | Result |
|---|---|
| Lean's verdict on each corpus file vs Warrant's | identical on every file: both accept init-medium, `001_basicDef` and `sparse-name-index`, and both reject `badDef`, `falseFromUnsafe`, `PR14806Subst.observe` and `Issue.forallFalse` with the same reasons |
| Lean re-checks what Warrant admitted (`warrant export`), corpus | accepted for every file, including our 3.0.0 → 3.1.0 conversion of `Nat.add_succ` |
| Lean re-checks what Warrant admitted, full Init | all 59,433 constants accepted at Lean 4.33.1 (≈71 s in Lean; ≈88 s for Warrant to check and export); all 59,349 accepted at Lean 4.35.0 |
| Lean re-checks declarations built from scratch in C# (`CrossCheckFixtures.cs`) | all accepted: recursive, mutual (`Even`/`Odd`), nested through `List` (`Rose`, with `Rose.rec_1`), structure with eta, universe-polymorphic (`Box`, motive universe `u_1`), K-like (`IsZero`), a definition by recursion and theorems needing iota and struct eta |
| The harness detects divergence | flipping the K flag of one Warrant-generated recursor makes Lean reject the file ("Invalid recursor test.IsZero.rec") |

Replay requires every recursor in the file to be `==` to the one Lean generates,
so these runs check Warrant's recursor generation against Lean's, not just
type correctness.

## Property-based tests (milestone 3)

`tests/Warrant.Kernel.Tests/PropertyTests.cs` uses FsCheck to compare the kernel
with an independent meaning on random inputs:

- **Universe levels vs. evaluation** (all assignments of 0–3 to `u`, `v`, `w`):
  normalization preserves value; `IsEquivalent` and `IsGeq` are sound;
  `mk_max`/`mk_imax` and instantiation match their meaning; equivalence is
  reflexive and symmetric.
- **Expression operations**: abstraction/instantiation and lift/lower are inverse;
  instantiating removes the variable; alpha-equality, equality and hashing agree;
  random terms survive the export round trip.
- **Nat arithmetic vs. BigInteger**: random closed expressions over `Nat.succ`,
  `add`, `mul`, `sub`, `div`, `mod`, `max`, `min` reduce to their value, and
  definitional equality between them is symmetric and matches value equality.
- **A small typed language** (`Nat`, `Bool`, `List Nat`, `Nat × Bool`, with
  `cond`, list functions, pairs and beta-redexes) generated from its typing rules:
  every generated term is accepted with its type, reduction preserves types, and
  applying `Nat.succ` to a non-`Nat` term is rejected.

**Finding:** Lean's level normalization is not idempotent. Its `imax` case
rebuilds an unsorted `max`, so `IsEquivalent(l, Normalize(l))` can be false even
though both sides always evaluate equal. This is incompleteness, not unsoundness.
Warrant matches the C++ exactly, and
`NormalizationIsNotIdempotentExactlyAsInLean` pins the behaviour.
