# Checking Mathlib

Warrant's kernel accepts all of Mathlib v4.35.0: 712,205 declarations, making
729,263 constants, with none rejected. Lean's own kernel accepts the same export,
and it also accepts the file Warrant writes back out. The check takes 26 minutes
and peaks at 12.6 GB of memory. This page records how the run was done, what it
measured, and what the numbers mean for the store in milestone M5b.

## Why it was run

The design ([§1](design.md#1-goals-and-non-goals), [§7.2](design.md#72-import-lean4export-ndjson))
says that Lean's libraries, Mathlib included, are available to a proof as imported
declarations. That claim needs two things to hold. The kernel must accept
Mathlib, since a proof that cites a lemma relies on the kernel having checked it.
And the cost of holding Mathlib must be known before the store's layout is
decided. The run was planned for M2 and M3, was deferred, and became the first
step of M5b because store v1 waited on its memory figure (ticket `7afb02b`).

Before this run, the largest library Warrant had checked was Lean's full `Init`
(57,919 declarations, 0.73 GB peak). Ansatz, the Java port Warrant learned from,
reports checking 707,508 Mathlib declarations at v4.33.1.

## What was done

1. **Export.** Mathlib was cloned at tag `v4.35.0` (commit `56a0058`), the
   release for the Lean version Warrant is pinned to. `lake exe cache get`
   fetched the prebuilt `.olean` files, and lean4export (commit `5a9a355`, the
   same build used for `Init`) wrote Mathlib as NDJSON. The export took 312 s
   and produced 6.3 GB: 4,241,558 names, 47,805 universe levels and
   105,894,257 expressions.
2. **Count.** `scripts/count-export.py`, which does not use Warrant, counted the
   constants by kind:

   | Kind | Count |
   |---|---|
   | Theorems | 517,916 |
   | Definitions | 184,355 |
   | Constructors | 9,863 |
   | Recursors | 7,162 |
   | Inductive types | 7,046 |
   | Opaque constants | 2,913 |
   | Axioms | 4 |
   | Quotient constants | 4 |
   | **Total** | **729,263** |

3. **Check with Warrant.** `warrant check mathlib.ndjson --quiet --slowest 20`
   ran on the Release build. A script sampled the process every 500 ms for its
   peak working set and private bytes, because Windows no longer reports them
   once the process exits.
4. **Check with Lean.** `tools/lean-replay`, which runs Lean's kernel through
   `Lean.Environment.replay`, checked the same export.
5. **Round trip.** `warrant export` checked the export again and wrote out
   what its kernel admitted, including the constructors and recursors it
   generates itself. Lean's kernel then checked that file. Replay requires the
   generated recursors to equal Lean's own, so this step also tests Warrant's
   recursor generation on every inductive type in Mathlib.

The machine was a Windows 11 workstation with 32 cores and 64 GB of memory.
Warrant checks one declaration at a time, so the core count does not affect
its time.

## Results

| Check | Result | Time | Peak memory |
|---|---|---|---|
| `warrant check` | 712,205 accepted, 0 rejected, 0 declined | 1,580 s | 12.60 GB working set, 12.67 GB private |
| Lean's kernel on the export | 729,263 constants accepted | 1,801 s | not measured |
| `warrant export` | 712,205 declarations written | 2,269 s | not measured |
| Lean's kernel on Warrant's export | 729,263 constants accepted | 1,725 s | not measured |

For comparison:

| Library | Declarations | Warrant check time | Peak working set |
|---|---|---|---|
| `Init` (Lean 4.35.0) | 57,919 | 46.6 s | 0.73 GB |
| Mathlib v4.35.0 | 712,205 | 1,580 s | 12.60 GB |

Memory grows roughly in line with the number of constants: about 12 KB per
constant for `Init` and about 17 KB for Mathlib. Almost all of it is the
environment, which keeps every checked constant, with its type and value, in
memory, because a later declaration may refer to any of them.

### The slowest declarations

`--slowest N`, added to `warrant check` for this run, prints the N declarations
that took longest. The twenty slowest in Mathlib:

| Seconds | MB allocated | Declaration |
|---|---|---|
| 20.521 | 16,815.7 | `CategoryTheory.instIsIsoIndCoimageImageComparison` |
| 15.638 | 13,018.1 | `AlgebraicGeometry.Proj.awayι_comp_map` |
| 13.337 | 12,723.5 | `Polynomial.iterate_derivative_derivative_mul_X` |
| 12.413 | 17,335.8 | `PresheafOfModules.freeObj._proof_2` |
| 7.479 | 6,726.2 | `CategoryTheory.Sheaf.H.longSequence_exact` |
| 6.887 | 6,235.3 | `CategoryTheory.GrothendieckTopology.MayerVietorisSquare.biprodAddEquiv_symm_biprodIsoProd_hom_toBiprod_apply` |
| 6.741 | 11,428.5 | `PadicInt.coe_adicCompletionIntegersEquiv_apply` |
| 6.172 | 3,841.6 | `CategoryTheory.GrothendieckTopology.MayerVietorisSquare.sequenceIso._proof_1` |
| 5.955 | 3,942.8 | `CategoryTheory.GrothendieckTopology.MayerVietorisSquare.sequenceIso` |
| 5.866 | 5,945.6 | `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq_aux₂` |
| 5.355 | 4,935.6 | `CategoryTheory.GrothendieckTopology.MayerVietorisSquare.sequenceIso._proof_2` |
| 5.322 | 4,938.1 | `CategoryTheory.GrothendieckTopology.MayerVietorisSquare.sequenceIso._proof_5` |
| 5.152 | 1,629.9 | `AlgebraicGeometry.Scheme.instSubsingletonEllAdicCohomologyOfIsEmptyCarrierCarrierCommRingCat` |
| 4.729 | 4,025.9 | `AlgebraicGeometry.Proj.sheafedSpaceMap._proof_1` |
| 4.319 | 3,848.7 | `CategoryTheory.GrothendieckTopology.MayerVietorisSquare.sequenceIso._proof_4` |
| 4.018 | 3,943.7 | `CategoryTheory.GrothendieckTopology.MayerVietorisSquare.mk₀_f_comp_biprodAddEquiv_symm_biprodIsoProd_hom` |
| 3.980 | 1,402.5 | `Unitary.conjStarAlgAut_symm_unitaryLinearIsometryEquiv` |
| 3.585 | 1,636.6 | `CategoryTheory.Sheaf.H.addEquiv₀_map` |
| 3.538 | 3,122.8 | `_private.Mathlib.AlgebraicGeometry.EllipticCurve.Affine.AddSubMap.0.WeierstrassCurve.Affine.Point.sym2x_add_sub_eq_addSubMap_sym2x._proof_1_8` |
| 3.508 | 820.7 | `AlgebraicGeometry.Scheme.instAddCommGroupEllAdicCohomology._proof_5` |

The slowest `Init` declaration takes 0.433 s. Most of the slow Mathlib
declarations come from category theory and algebraic geometry.

"MB allocated" is everything the checking thread allocated between one result
and the next, reading the declaration included. Most of it is short-lived and
collected straight away, so it measures work, not the memory a declaration
holds. It cannot be compared with Ansatz's figure of a 5–6 GB heap for its
hardest declarations, which is a heap limit.

## What it shows

- **The kernel handles all of Mathlib.** No declaration was rejected, and none
  was declined as needing something the kernel does not model. Lean's kernel
  gives the same verdict on every constant. Accepting a correct library does not
  test soundness; the rejection tests in [kernel.md](kernel.md) do that.
- **Warrant writes back what it admits faithfully at scale.** Lean accepted
  Warrant's re-export, so the kernel's own constructors and recursors match
  Lean's for all 7,046 inductive types.
- **Lemma imports from Mathlib are feasible,** but holding all of Mathlib costs
  about 13 GB.

## What it means for M5b

The verification server in M5b keeps an environment in memory between builds.
At 12.6 GB for all of Mathlib, eagerly loading every library into the server is
not reasonable on a developer machine. Store v1 should therefore load only the
constants a project needs, or keep the full Mathlib store opt-in. `Init` and the
semantics library together are small enough (under 1 GB) to load whole. The M5b
plan makes the decision. This run supplies the figure the design said store v1
was waiting for ([§11, M5b](design.md#11-milestones)).

The check time also matters for verified import mode, in which `check-store`
re-checks a library before trusting it. Re-checking Mathlib takes about 26
minutes on one thread, so it is a one-off or CI job, not something to run on
every build. Trusted mode, which reads the store without re-checking it, is the
everyday path.

## What it does not show

- **Peak memory for Lean's kernel and for `warrant export`** was not measured.
- **One run on one machine.** The times are not averages and will vary.
- **Live heap per declaration** was not measured; only total allocation was.
- **Ansatz** was not run on this export, so there is no like-for-like time
  comparison. Its 80-minute figure is for v4.33.1 on 4 workers, from its own
  documentation.

## Reproducing it

[REPRODUCING.md, step 10](../REPRODUCING.md#10-mathlib) gives the commands. The
summary in [kernel.md](kernel.md#mathlib) carries the same numbers.
