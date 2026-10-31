# The LeanSharp kernel

`src/LeanSharp.Kernel` is a port of the Lean 4 kernel (`src/kernel/` in
[leanprover/lean4](https://github.com/leanprover/lean4)), made against tag
**v4.33.1** (commit `819816b`), the toolchain that produced the init-medium test
export. Ansatz's Java kernel was a second reference. The port follows the C++
closely, function by function, so that each part can be compared directly with
the original.

## File map

| Lean 4 (C++) | LeanSharp (C#) | Contents |
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
LeanSharp's (`Expr.AlphaEquals`, `Expr.AlphaComparer`). `Expr.Equals` is exact
equality, which the export round-trip tests need.

## Deliberate differences from Lean

| Lean 4 | LeanSharp | Why |
|---|---|---|
| No step limit (only heartbeats/recursion depth from the caller) | **Fuel**: each call of the core procedures costs a step; 20M interactive, 100M for corpora. Running out rejects as a *resource limit*, never as a type error | Checking must terminate inside a build server. |
| `Lean.reduceBool`/`Lean.reduceNat` run compiled code | **Not supported**: they never reduce, so declarations relying on them (`native_decide`) are rejected | LeanSharp has no compiler, and trusting one would enlarge the trusted base. |
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

**Not yet run:** the full Init export (54,335 declarations) and Mathlib
(707,508). Neither ships with Ansatz as NDJSON, and producing them needs the Lean
toolchain and lean4export to run.
