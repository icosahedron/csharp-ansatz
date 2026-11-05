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
| No wall-clock limit | **Deadline** (M5a): an optional `KernelLimits.Deadline`, read on the first step and then every 1,024 steps against a monotonic clock. Passing it rejects as a resource limit, like fuel | A theorem's 30-second limit must stop the kernel too ([docs/m5a/02](m5a/02-metavariables-and-meta.md)). |
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

## Metavariables (milestone 5a)

`Warrant.Cic.Expr` has a metavariable kind and `Level` a metavariable level
since M5a, for `Warrant.Meta`'s tactics ([docs/m5a/02](m5a/02-metavariables-and-meta.md)).
The kernel never accepts either. `Kernel.Add` rejects a declaration whose type
or value has an expression or universe metavariable before it type-checks
anything, with Lean's message `declaration has metavariables 'name'` (Lean adds
a `(kernel) ` prefix), using flags cached on every term. The type checker also
throws "kernel type checker does not support meta variables" on one, and the
NDJSON writer refuses them. `MVarRejectionTests` puts a universe metavariable
only in a binder's domain (`Sort ?u`) and only in a constant's universe
argument (`PUnit.{?u}`): without the up-front check, the kernel accepted both,
and Ansatz's kernel misses universe metavariables the same way.

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

### Mathlib

[Checking Mathlib](mathlib.md) describes the run in full.

Mathlib v4.35.0 (commit `56a0058`), exported with the same lean4export, is a 6.3 GB
file: 712,205 declaration records making 729,263 constants (517,916 theorems,
184,355 definitions, 7,046 inductives, 2,913 opaques). Measured on one machine
(32 cores, 64 GB), with the Release build:

| Check | Result | Time | Peak memory |
|---|---|---|---|
| `warrant check mathlib.ndjson` | accepted 712,205, rejected 0, declined 0 | 1,580 s | 12.6 GB working set, 12.7 GB private |
| Lean's kernel (`lean-replay`) on the export | accepted 729,263 constants | 1,801 s | |
| `warrant export` (check, then write what was admitted) | 712,205 declarations written | 2,269 s | |
| Lean's kernel on Warrant's export | accepted 729,263 constants | 1,725 s | |

For comparison, full Init peaks at 0.73 GB. The 12.6 GB is almost all the
environment: every constant stays in memory, as the checker needs. Ansatz checks
its v4.33.1 export (707,508 declarations) in about 80 minutes on 4 workers;
Warrant checks one declaration at a time.

`warrant check --slowest N` lists the declarations that took longest. On
Mathlib the slowest twenty take 3.5 to 20.5 s each; the slowest is
`CategoryTheory.instIsIsoIndCoimageImageComparison` (20.5 s), then
`AlgebraicGeometry.Proj.awayι_comp_map` (15.6 s),
`Polynomial.iterate_derivative_derivative_mul_X` (13.3 s) and
`PresheafOfModules.freeObj._proof_2` (12.4 s). The memory column is what the
thread allocated while checking (up to 17 GB for one declaration), most of it
short-lived garbage, so it is not a heap size and is not comparable with Ansatz's
5–6 GB heap figure for its hardest declarations.

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

## Cross-kernel checks: Ansatz and the arena (milestone 5a)

`scripts/cross-kernel.sh` compares Warrant's verdicts with several kernels at once
(ticket `d953584`, plan KTD27). Each row is one file, with one verdict column per kernel:

- **LEAN**: Lean's kernel, through `tools/lean-replay` (Lean 4.35.0).
- **WARRANT**: `warrant export` on an original file, which checks it as `warrant check` does;
  `warrant check` on a file Warrant wrote.
- **ANSATZ**: Ansatz's `arena-check --fuel 100000000`, with fuel equal to Warrant's corpus fuel.
  It needs `clojure` on `PATH` and a built Ansatz checkout in `ANSATZ_DIR` (default `../ansatz`;
  build it once with `clojure -T:build javac`). Without either, the column says SKIPPED.
  The script passes `-J-Dansatz.kernel.natDecEqShortcut=false` (override with `ANSATZ_JVM_OPTS`). The property is
  read only by a local patch to Ansatz, described under "Ansatz on Lean 4.35 certificates" below;
  an unpatched Ansatz ignores it.
- **ARENA-OFFICIAL, NANODA, LEAN4LEAN**: the verdicts
  [lean-kernel-arena](https://arena.lean-lang.org/) publishes in `results.json` for Lean's C++ kernel,
  nanoda and lean4lean. They exist for arena tests only.

A decline, a timeout (`KERNEL_TIMEOUT`, 900 s by default) or a checker error is no verdict.
`scripts/lib/arena.sh` downloads `lean-arena-tests.tar.gz` and `results.json` and records the
arena commit from `results.json`. It also checks each test's SHA-256 against `results.json`
and skips any test that does not match, with a message. The rows are:

- every test in the arena tarball, judged against the arena's expected outcome;
- init-medium, `Nat.add_succ` and `tests/data/arena/*`, judged against their known outcome;
- Warrant's export of each of those files, which every kernel must accept;
- the declarations built in C# (`CrossCheckFixtures.cs`, on top of init-medium), the translated M4 corpus
  (the semantics bundle plus the translated definitions and theorems) and the M5a certificate
  (`warrant verify tests/corpus/m5a/accepted --out …`: the bundle plus the theorems proved by their scripts,
  the recursive definitions with their decrease theorems and equation lemmas), which must be accepted;
- the M5a certificate with its last theorem's proof replaced by the proof of the theorem before it, which
  must be rejected.

`CORPUS_ONLY=1` skips the arena tests and their download, for a run over the committed files only.

The script exits 1 only when Warrant contradicts an expected outcome, or when Lean rejects
something Warrant admitted. It lists every other disagreement, and each one is explained below.
Arena tests marked `either` would be recorded without a judgement, but the tarball contains none:
the 30 `either` tests are not in it.

### Results

The run used arena commit `236ab46` (results published 2026-11-02 18:44 UTC) and Ansatz `4ff56b8`.
All 207 tarball tests matched their published SHA-256. Ansatz ran under the Clojure CLI
(deps.clj 1.12.6.1673) on Java 26. The run produced 432 rows in about 60 minutes.
Ansatz took 45 of those minutes, two of them 900-second timeouts, Warrant 7 and Lean 4.
The two fixtures added afterwards (below) raise the count to 436 rows. A second run over the
committed corpus alone took 113 s and gave the same verdicts on the new fixtures as on their arena originals.

| Rows | Lean | Warrant | Ansatz | official / nanoda / lean4lean |
|---|---|---|---|---|
| 127 arena tests expected to accept | 127 accept | 127 accept | 125 accept, 1 timeout, 1 decline | 127 accept / 125 accept and 2 declines / 127 accept |
| 80 arena tests expected to reject | 74 reject, 6 decline | 80 reject | 79 reject, **1 accept** | 80 reject / 79 reject and **1 accept** / 80 reject |
| 207 Warrant exports of the arena tests | 207 accept | 207 accept | 204 accept, 1 reject, 1 timeout, 1 decline | – |
| init-medium, `Nat.add_succ`, the 6 committed arena files, and the exports of all 8 | 15 agree, 1 decline | 16 agree | 13 agree, 3 reject | – |
| C# fixtures; translated M4 corpus | accept; accept | accept; accept | reject; reject | – |

**Warrant's verdict matched the expected outcome on every row, and Lean accepted everything
Warrant wrote.** No verdict from another kernel showed a fault in Warrant.

The M5a certificate rows were added later and run with `CORPUS_ONLY=1` (Lean 4.35.0 from elan, 26 rows; the
rows the earlier run also had gave the same verdicts). With unpatched Ansatz `4ff56b8`, Ansatz rejected the M4
corpus and both M5a certificates at `Nat.zero_sub`, inside the bundle (see "Ansatz on Lean 4.35 certificates").
The table is the rerun of 2026-11-04 with the patched Ansatz:

| Row | Lean | Warrant | Ansatz (patched) |
|---|---|---|---|
| translated M4 corpus (2,956 declarations) | accept | accept | accept, all 2,956 |
| M5a certificate (2,879 constants: the bundle and 38 admitted declarations) | accept | accept | accept, all 2,879 |
| M5a certificate, one proof replaced (`RankIsSmall` given `ValidImpliesPositive`'s proof) | reject: "declaration type mismatch" at `RankIsSmall` | reject: the same, at `RankIsSmall` | reject at `RankIsSmall`, after admitting the other 2,878 |

All three kernels reject the tampered certificate at the theorem whose proof was replaced, and nowhere else.
So the translated definitions, the proofs found by tactics, the decrease theorems and the equation lemmas are
checked by three independent kernels. The other rows gave the same verdicts as the unpatched run.

### Ansatz on Lean 4.35 certificates

Ansatz targets Lean 4.33.1. Its reducer has a native short-cut for `Nat.decEq` on two equal literals, which builds
`Decidable.isTrue (Eq.refl n)` (`src-java/ansatz/kernel/Reducer.java`, `mkNatDecEqTrue`). In Lean 4.35.0,
`Decidable` is a structure built with `Decidable.intro` and a `Bool` field. That term no longer reduces, so
`decide (Nat.pred 0 = 0)` does not reach `true`, and unpatched Ansatz rejects the 4.35 bundle at `Nat.zero_sub`.

The local patch adds the JVM property `ansatz.kernel.natDecEqShortcut`. When the property is `false`, both
short-cut call sites return no result, and `Nat.decEq` reduces by its definition, as it does in Lean's kernel.
The default is unchanged. The patch removes an optimisation and adds no reduction rule. With the short-cut off,
Ansatz reduces `Nat.decEq` only by the unfolding that Lean's kernel also uses. The patch is 7 lines, is not upstream, and is kept in
`tools/ansatz/nat-deceq-shortcut.patch` against Ansatz `4ff56b8`. Apply it with
`git -C "$ANSATZ_DIR" apply <path>/tools/ansatz/nat-deceq-shortcut.patch`, then rebuild with `clojure -T:build javac`.
Reporting it upstream, with `forged-quot-ind`, is still to do.

### Disagreements

| Row(s) | Kernel | Cause | Regression |
|---|---|---|---|
| `bugs/forged-quot-ind` | Ansatz **accepts** a proof of `False` | **Ansatz is unsound here.** The file declares `Quot.ind` before `Quot` and `Quot.mk`, and then defines `Quot` and `Quot.mk` as ordinary definitions. Ansatz checks the quotient declaration by comparing its type with one built from the names `Quot` and `Quot.mk`. It does not require them to be the primitives already in the environment. Warrant, like Lean, installs the whole quotient package when the first quotient constant arrives. The later `def Quot` therefore fails with "'Quot' has already been declared", and `fakeQuotFalse` does not type-check. The arena reports that nanoda once had the same bug; its published verdict is now reject. | `tests/data/arena/forged-quot-ind.ndjson`, `CorpusTests.ArenaVerdicts` and `QuotientPrimitivesCannotBeForged` |
| `other/inductive-undeclared-universe` | nanoda (published) accepts | **nanoda's bug.** An inductive type uses the universe parameter `u` without declaring it. Warrant rejects it with "invalid reference to undefined universe level parameter 'u'", as do Lean, official, lean4lean and Ansatz. | `tests/data/arena/inductive-undeclared-universe.ndjson`, `CorpusTests.ArenaVerdicts` |
| init-medium and its export; the C# fixtures, which include init-medium; Warrant's exports of `tutorial/140_falseFromUnsafe` and of `141_falseFromUnsafe` | Ansatz rejects with "Unknown constant" at a recursive unsafe definition (`_private…Array.foldlMUnsafe.fold`, `unsafeLoop`) | **An Ansatz limitation.** `arena-check` admits definitions one at a time and does not put a recursive `unsafe` (or `partial` implementation) definition in the environment before checking its body. Lean and Warrant admit such definitions; Warrant buffers each mutual unsafe block (see "How exported data is checked"). On the original `falseFromUnsafe` files Ansatz rejects too, with the expected verdict, but at `unsafeLoop` rather than at `falseFromUnsafe`. | None: Warrant's behaviour is covered by `UnsafeDefinitionIsAcceptedButSafeUseIsNot` and by Lean's verdict on the same files |
| translated M4 corpus; the M5a certificate and its tampered copy (unpatched Ansatz only) | Ansatz rejects `Nat.zero_sub` (declaration 583 in M4 and in M5a) | **A version difference**, explained under "Ansatz on Lean 4.35 certificates". Unpatched Ansatz accepts the Lean 4.33.1 `Nat.zero_sub` in init-medium, and rejects `tests/data/warrant-semantics.ndjson.gz` the same way, with or without its `mdata` nodes. With the patch, Ansatz accepts the M4 corpus and the M5a certificate and rejects the tampered copy at the replaced proof. | None: with the patch, Ansatz agrees with Lean and Warrant on all three rows |

### Rows without a verdict

| Row(s) | Kernel | Why |
|---|---|---|
| `tutorial/132_dup_defs`, `133_dup_ind_def`, `134_dup_ctor_def`, `135_dup_rec_def`, `138_dup_ctor_rec`, `139_DupConCon` | Lean declines | lean-replay's parser stops at a duplicate declaration ("Duplicate declaration: …") before the kernel runs. Every other kernel rejects these files, as expected. |
| `Nat.add_succ` | Lean declines | The file is format 3.0.0, which Lean's parser does not read. Lean accepts Warrant's 3.1.0 export of it. |
| `perf/app-lam` and its export | Ansatz times out (900 s) | Ansatz's own proposed arena entry declines this test because it exhausts the heap. Warrant takes 4 s. |
| `perf/magma-list-deep-n36` and its export | Ansatz declines | "Java heap space" with `-Xmx8g`, after admitting 622 of 623 declarations. |
| `other/level-index-out-of-order`, `other/sparse-name-index` | nanoda declines (published) | nanoda's parser rejects non-contiguous table indices. |

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

The design's §10.3 properties (M5a, KTD28) build on the same generators:

- **Definitional equality is an equivalence** on the typed language.
  `DefinitionalEqualityIsReflexive`, `DefinitionalEqualityIsSymmetric` and
  `DefinitionalEqualityIsTransitive` pair each generated term with terms one to
  three known reductions away. A reduction is applied at a random subterm, in
  either direction: beta (contract a redex, or wrap a subterm in one), delta
  (unfold a definition at its levels) and Nat literals (`n` to `succ (n-1)` or
  `k + (n-k)`, and back). Symmetry and transitivity also use independent terms of
  the same type, so both verdicts occur. Transitivity requires every reduction
  chain `a → b → c` to be accepted, and given `a ≡ b`, it requires `b ≡ c`
  exactly when `a ≡ c`.
- **Substitution and instantiation preserve typing.** A body is generated in a
  context of one or two variables, with closed arguments of the variables' types.
  `InstantiationPreservesTyping` binds the variables as de Bruijn indices: the
  instantiated body checks, and its type is the body type from the kernel's Pi
  type, instantiated. `SubstitutionPreservesTyping` binds them as free variables
  of a local context, and the substituted term has the substituted type.
- **Universe instantiation preserves well-typedness.**
  `UniverseInstantiationPreservesWellTypedness` generates definitions
  `fun (α : Sort U) (β : Type V) (a : α) (b : β) => t` over parameters `u`, `v`
  and `w`. Here `t` is built by the typing rules of a small polymorphic language
  with `id`, `cond`, `List`, `PProd` (whose projections are `Proj` terms) and
  beta-redexes. The kernel admits each definition, and it also admits the
  definition with its parameters instantiated at random levels, including
  `imax` and `0`.

**Finding:** Lean's level normalization is not idempotent. Its `imax` case
rebuilds an unsorted `max`, so `IsEquivalent(l, Normalize(l))` can be false even
though both sides always evaluate equal. This is incompleteness, not unsoundness.
Warrant matches the C++ exactly, and
`NormalizationIsNotIdempotentExactlyAsInLean` pins the behaviour.
