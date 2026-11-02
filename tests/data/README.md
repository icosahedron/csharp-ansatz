# Test corpus

lean4export NDJSON files used by the reader, writer and (later) kernel tests.

| File | Format | Source | License |
|---|---|---|---|
| `Nat.add_succ.ndjson` | 3.0.0 | [leanprover/lean4export](https://github.com/leanprover/lean4export) `examples/`, commit `df81913` | Apache-2.0 |
| `init-medium.ndjson.gz` | 3.1.0 | [replikativ/ansatz](https://github.com/replikativ/ansatz) `resources/ansatz/`, commit `662ac21`; an export of part of Lean 4.33.1's `Init` | Apache-2.0 (Ansatz, Lean 4) |
| `arena/001_basicDef`, `002_badDef`, `141_falseFromUnsafe`, `proj-of-subst-prop`, `rec-of-subst-prop` | 3.1.0 | [leanprover/lean-kernel-arena](https://github.com/leanprover/lean-kernel-arena), via Ansatz `test-data/arena/` | Apache-2.0 |
| `arena/sparse-name-index.ndjson` | 3.1.0 | Hand-written by Ansatz (`test-data/arena/`): non-contiguous table indices | Apache-2.0 |

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
