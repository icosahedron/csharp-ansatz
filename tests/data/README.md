# Test corpus

lean4export NDJSON files used by the reader, writer and (later) kernel tests.

| File | Format | Source | License |
|---|---|---|---|
| `Nat.add_succ.ndjson` | 3.0.0 | [leanprover/lean4export](https://github.com/leanprover/lean4export) `examples/`, commit `df81913` | Apache-2.0 |
| `init-medium.ndjson.gz` | 3.1.0 | [replikativ/ansatz](https://github.com/replikativ/ansatz) `resources/ansatz/`, commit `662ac21`; an export of part of Lean 4.33.1's `Init` | Apache-2.0 (Ansatz, Lean 4) |
| `arena/001_basicDef`, `002_badDef`, `141_falseFromUnsafe`, `proj-of-subst-prop`, `rec-of-subst-prop` | 3.1.0 | [leanprover/lean-kernel-arena](https://github.com/leanprover/lean-kernel-arena), via Ansatz `test-data/arena/` | Apache-2.0 |
| `arena/forged-quot-ind.ndjson`, `arena/inductive-undeclared-universe.ndjson` | 3.1.0 | [leanprover/lean-kernel-arena](https://github.com/leanprover/lean-kernel-arena) tests `bugs/forged-quot-ind` and `other/inductive-undeclared-universe` at commit `236ab46` (SHA-256 as in its `results.json`): regression fixtures for the cross-kernel disagreements in `docs/kernel.md` (Ansatz and nanoda accept them; Warrant must reject) | Apache-2.0 |
| `arena/sparse-name-index.ndjson` | 3.1.0 | Hand-written by Ansatz (`test-data/arena/`): non-contiguous table indices | Apache-2.0 |
| `warrant-semantics.ndjson.gz` | 3.1.0 | Exported from this repository's `lean/` by `scripts/export-semantics.sh` with Lean 4.35.0 and lean4export `5a9a355`: the semantics library and its 605 roots (`lean/bundle-roots.txt`) with their dependency closure, including the `Std.Do` triples, weakest preconditions and `@[spec]` lemmas M6's contracts use (M6 U1), the effect monad `ClrM` with its raising integer models (M6 U3), the nullable and `Math` models (M6 U16), the `decimal` model (M6 U4) and the constants the monadic translation emits (M6 U9), exported with `--export-mdata` so `no_index` annotations survive. The M4 tests load it instead of init-medium, which is a Lean 4.33.1 subset without `Int32` or `Int64`. | Apache-2.0 (Lean 4, Warrant) |
| `warrant-attributes.ndjson.gz` | sidecar 2 | Exported by `scripts/export-attributes.sh` (`tools/warrant-attrs/Main.lean`) with Lean 4.35.0 from `Init` and `lean/`: the simp, congr, instance, reducibility, defeq, matcher, class and `@[spec]` entries of the bundle's constants (plan KTD9, docs/m5a/05; `spec`, M6 KTD15). Not a lean4export file. | Apache-2.0 (Lean 4, Warrant) |

Several arena files contain declarations a kernel **must reject** (for example
`002_badDef`, whose value does not have its declared type). The reader accepts
them, because they are well-formed; rejecting them is the kernel's job (milestone 2).

The full Init export (348 MB) is not committed. Reproduce it with
`scripts/export-lean-library.sh` and run the opt-in kernel test with
`WARRANT_INIT_EXPORT=<path> dotnet test --filter AcceptsFullInit`.

## Expected counts

Computed independently of Warrant by `scripts/count-export.py`, which reads
the raw JSON. These are the values asserted in `ReaderCorpusTests`.

| File | Names | Levels | Exprs | Decl. lines | Constants (axiom/def/thm/opaque/quot/induct/ctor/rec) |
|---|---|---|---|---|---|
| `Nat.add_succ` | 103 | 15 | 434 | 19 | 0/12/1/0/0/6/7/6 = 32 |
| `init-medium` | 31,267 | 122 | 343,950 | 4,631 | 4/1791/2615/11/4/206/279/208 = 5,118 |
| `001_basicDef` | 1 | 1 | 2 | 1 | 0/1/0/0/0/0/0/0 = 1 |
| `002_badDef` | 1 | 1 | 2 | 1 | 0/1/0/0/0/0/0/0 = 1 |
| `141_falseFromUnsafe` | 7 | 1 | 10 | 3 | 0/1/1/0/0/1/0/1 = 4 |
| `proj-of-subst-prop` | 708 | 18 | 4,030 | 110 | 0/63/26/2/0/19/23/19 = 152 |
| `rec-of-subst-prop` | 776 | 18 | 4,203 | 127 | 1/76/25/3/0/22/25/22 = 174 |
| `sparse-name-index` | 1 | 0 | 1 | 1 | 1/0/0/0/0/0/0/0 = 1 |
| `warrant-semantics` | 21,161 | 83 | 306,639 | 3,800 | 3/1316/2343/1/4/133/164/135 = 4,099 |

### The `Std.Do` roots (M6 U1)

M6's `Std.Do` section of `lean/bundle-roots.txt` grew the bundle from 2,835 to 3,210 constants (2,599 to 2,927
declaration records), with no new axiom. M6 KTD3 keeps the bundle a verified load while server start stays under 5 s.
Measured on 2026-11-09 with `scripts/measure-m5b.sh` and seven alternating cold starts of each bundle
(`warrant verify tests/corpus/m5a/rejected --server auto --timings`, "started the server and connected in"), on Linux
with 4 logical cores and the .NET 10.0.403 SDK:

| Bundle | Server start, median (range) | GC heap after start |
|---|---|---|
| M5b, 2,835 constants | 4,318 ms (4,231–4,538) | 41 MB |
| M6 U1, 3,210 constants | 4,775 ms (4,710–4,896) | 62 MB |

The new roots cost about 460 ms (11%) of start time here. The M5b baseline on the 32-core Windows machine of
docs/m5b/08 was 2.9 s, so the same share puts it near 3.2 s. Warm, cached and rechecked requests did not change.

### The division roots (M6 U2)

M6 U2's division and remainder roots (`lean/Warrant/Checked.lean`'s bridges and the Init `Int32`/`Int64` lemmas they
are proved from) grew the bundle from 3,210 to 3,920 constants (2,927 to 3,633 declaration records), with no new
axiom. Most of the new constants are the `BitVec`, `Nat` and `Int` lemmas (about 410 of them private to Init's
`Data` modules or in `BitVec`) that the proofs of Init's `toInt_div_of_ne_left`, `toInt_div_of_ne_right` and
`toInt_mod` use for `BitVec.sdiv` and `BitVec.srem`. Measured on 2026-11-10 on the reference workstation of docs/m5b/08 (Windows 11, 32
logical cores), seven alternating cold starts of the U1 and U2 CLIs built in Release, as above:

| Bundle | Server start, median (range) | GC heap after start |
|---|---|---|
| M6 U1, 3,210 constants | 3,147 ms (2,979–3,259) | 34–35 MB |
| M6 U2, 3,920 constants | 4,152 ms (3,881–4,686) | 41–48 MB |

The new roots cost about 1.0 s (32%) of start time. That is under M6 KTD3's 5 s threshold, with 0.85 s left for U3,
U16 and U4.

### The effect core (M6 U3)

M6 U3's roots (`lean/Warrant/Effect.lean`'s `ClrExn`, `ClrM`, throw, `ClrExn.Allowed` and the `ite`/`dite` triple
rules, `Std.Do.PostCond.entails.mk`, and `lean/Warrant/Checked.lean`'s raising integer models with their `@[spec]`
lemmas) grew the bundle from 3,920 to 3,973 constants (3,633 to 3,678 declaration records), with no new axiom and no
new pinned declaration: the proofs reuse what U1 and U2 already brought in. Measured on 2026-11-10 on the reference
workstation, seven alternating cold starts of the U2 and U3 CLIs built in Release, as above:

| Bundle | Server start, median (range) | GC heap after the request |
|---|---|---|
| M6 U2, 3,920 constants | 4,303 ms (3,793–4,415) | 41–48 MB |
| M6 U3, 3,973 constants | 4,217 ms (3,943–4,591) | 44–50 MB |

The difference is within the run-to-run noise (an earlier pair of runs in the same session gave 4,461 and 4,289 ms).
U3 stays under M6 KTD3's 5 s threshold; U2's bundle measured 0.15 s slower here than on 2026-11-10, so the headroom
for U16 and U4 is about 0.7 s against this session's figures.

### Nullable values and `Math` (M6 U16)

M6 U16's roots (`lean/Warrant/Nullable.lean`'s `value`, `nonNull` and `coalesce`, `lean/Warrant/Math.lean`'s `min`,
`max` and `abs` on `Int32` and `Int64`, with their `@[spec]` lemmas and equations, and `Option` with its constructors)
grew the bundle from 3,973 to 3,993 constants (3,678 to 3,698 declaration records), with no new axiom and no new pinned
declaration. Measured on 2026-11-11 on the reference workstation, seven alternating cold starts of Release CLIs carrying
the U3 and U16 bundles and sidecars, as above:

| Bundle | Server start, median (range) | GC heap after the request |
|---|---|---|
| M6 U3, 3,973 constants | 4,095 ms (3,891–5,946) | 44–49 MB |
| M6 U16, 3,993 constants | 3,936 ms (3,821–4,684) | 42–46 MB |

The difference is within the run-to-run noise; U16 stays under M6 KTD3's 5 s threshold.

### The `decimal` model (M6 U4)

M6 U4's roots (`lean/Warrant/Decimal.lean`'s `Decimal` with its literal constructor, value order and equality, unary
minus, `+` and `-` with their `@[spec]` lemmas and the lemmas about them, and `lean/Warrant/Math.lean`'s `min`, `max`
and `abs` on `Decimal`) grew the bundle from 3,993 to 4,098 constants (3,698 to 3,799 declaration records), with no new
axiom and no new pinned declaration. Besides the library's own constants, the proofs bring in only `Equivalence`, a few
`Nat.max` lemmas, `Bool.false_ne_true` and `Option`'s no-confusion principle. Measured on 2026-11-11 on the reference
workstation, seven alternating cold starts of Release CLIs carrying the U16 and U4 bundles and sidecars, as above:

| Bundle | Server start, median (range) | GC heap after the request |
|---|---|---|
| M6 U16, 3,993 constants | 4,286 ms (4,037–4,680) | 42–48 MB |
| M6 U4, 4,098 constants | 4,548 ms (4,309–4,689) | 44–47 MB |

U4 stays under M6 KTD3's 5 s threshold, about 0.45 s below it against this session's figures (U16's bundle measured
0.35 s slower here than in the session above, so the machine's run-to-run noise is of the same size as the margin).

### The monadic translation (M6 U9)

M6 U9's roots are the constants the monadic translation and pure division emit: `pure` and `>>=` through `ClrM σ`'s
`Monad` instance, `Unit`, `Option.rec`, `Option.isNone` and the `HDiv`/`HMod` instances of `Int32` and `Int64`.
All but `Option.isNone` were already in the closure, so the bundle grew by that one definition, from 4,098 to 4,099
constants (3,799 to 3,800 declaration records), appended at the end of the file, with no new axiom and no new pinned
declaration. A single small definition is far below the run-to-run noise of the start-time measurements above, so it
was not measured again.

Regenerate `warrant-semantics.ndjson.gz` with `scripts/export-semantics.sh` after changing `lean/`.
The export is deterministic: an unchanged library gives a byte-identical file.

## The attribute sidecar

`warrant-attributes.ndjson.gz` holds the Lean attributes of the constants in
`warrant-semantics.ndjson.gz`, which lean4export does not carry. Its first line is a
header with the format version, the Lean githash and the SHA-256 of the bundle
`.gz` file it was made for; every other line is one entry, and every name in it is a
constant of the bundle. `tools/warrant-attrs/Main.lean` documents each kind's fields.

| Kind | Entries |
|---|---|
| `simp` (default simp set, with priority, direction, `←` and Lean's keys) | 530 |
| `congr` | 3 |
| `instance` (with class, priority and declaration order) | 204 |
| `reducibility` (every status other than semireducible; M6 U9's `Option.isNone` is implicit-reducible) | 735 |
| `defeq` | 94 |
| `matcher` | 400 |
| `class` (with out-parameter positions) | 77 |
| `spec` (`mvcgen`'s `@[spec]` lemmas, triple or equation, with priority; format 2): 13 from `Std.Do`, 14 of M6 U3 (`ClrM.throw` and the raising models), 4 of M6 U16 (the raising nullable reads and `Math.Abs`), 2 of M6 U4 (`decimal` `+` and `-`) | 33 |

Regenerate it with `scripts/export-attributes.sh` after regenerating the bundle.
The export is deterministic: an unchanged library and bundle give a byte-identical file.
