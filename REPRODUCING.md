# Reproducing LeanSharp's results

This guide covers two things:

1. **How the work was done**: the process, the sources, and the checks used at
   each step.
2. **How to duplicate it**: commands that rebuild everything and reproduce
   every result, from a clean machine.

For the design itself, see [docs/design.md](docs/design.md). For the kernel port,
see [docs/kernel.md](docs/kernel.md). The full conversation is in
[docs/history/](docs/history/README.md).

---

## Part 1: How it was done

### Starting point

The project began as a conversation with ChatGPT
([transcript](docs/history/2026-10-31-chatgpt-recommend-csharp-frontend.md))
about making C# a frontend for a Lean kernel, in the spirit of
[Ansatz](https://github.com/replikativ/ansatz), which does this for Clojure. It
continued in a Claude Code cloud session
([full transcript](docs/history/2026-10-31-claude-code-session-transcript.md)).

### Design (milestone 0)

1. **Check the claims before building on them.** Claude cloned Ansatz (commit
   `662ac21`) and compared ChatGPT's statements with the source. Several were
   wrong: the kernel node list (it has `Proj`, and has no `MVar`), the location
   and size of init-medium, and the Mathlib counts. The corrections are recorded
   in [design Appendix A](docs/design.md#appendix-a-facts-checked-against-ansatz).
2. **Make the central decision explicit.** Ansatz goes *verified source → CIC →
   generated code*. The author chose the opposite direction, **verify existing
   C#**, because that covers real code with database calls (decision D1).
3. **Write it down.** The decisions, architecture (with a verification server),
   semantic models, trusted base, milestones and open questions are in
   `docs/design.md`.

### Milestone 1: terms and the lean4export format

1. **Read the authoritative format spec**, lean4export's `format_ndjson.md`.
   Ansatz's parser was used as a second opinion.
2. **Read the format's git history as well as the spec.** The committed
   `Nat.add_succ` example turned out to be format **3.0.0**, which groups mutual
   definitions in arrays and uses different keys (`axiomInfo`,
   `inductiveVals`, …). The reader supports both versions.
3. **Get expected numbers from an independent oracle.** A short Python script
   (`scripts/count-export.py`) counts every file's records directly from the
   JSON. The C# tests assert those numbers, so they can't simply agree with
   themselves.
4. **Test the round trip.** Every constant survives import → export → import, and
   export → import → export is byte-identical.

### Milestone 2: the kernel

1. **Port against the exact version that produced the data.** init-medium's
   metadata names Lean commit `819816b`, which is tag **v4.33.1**. Lean's
   `src/kernel/` was checked out at that tag and ported file by file
   (`level.cpp` → `LevelOps.cs`, `type_checker.cpp` → `TypeChecker*.cs`,
   `inductive.cpp` → `Inductive.cs`, …). Ansatz's Java kernel served as a second
   reference.
2. **Match Lean's notion of equality.** The C++ kernel's `==` ignores binder
   names and binder info, so LeanSharp's caches and comparisons do too
   (`Expr.AlphaEquals`).
3. **Rebuild declarations from the export instead of trusting it.** The
   checker admits inductive types from their types and constructors only, then
   compares the recursors it derives with the exported ones. It generates the
   quotient package and compares that too.
4. **Test rejections as hard as acceptances.** Besides the corpus, the tests
   tamper with real declarations (wrong proofs, flipped K flag, swapped
   computation rules, forged quotient, …). Each must be rejected for the expected
   reason, and each has a positive control.
5. **Go past the committed corpus.** Lean 4.33.1's full `Init` library was
   exported with lean4export and checked: all 57,977 declarations are accepted.

### Notes on the environment

- The cloud container had no .NET; the SDK was installed with Microsoft's
  `dotnet-install.sh`.
- Pushing to GitHub needed the Claude GitHub App to have access to the
  repository.
- Building lean4export runs a downloaded toolchain. Claude Code's auto mode
  blocked that, so the session was switched to **Accept edits** mode to approve
  it.

---

## Part 2: How to duplicate it

### 1. Prerequisites

| Tool | Needed for | Notes |
|---|---|---|
| [.NET 10 SDK](https://dotnet.microsoft.com/download) | building and testing | Any 10.0.1xx or later works (`global.json` rolls forward) |
| git | cloning | |
| Python 3 | the independent count check (optional) | standard library only |
| curl, unzip, ~4 GB of disk | exporting Lean libraries (optional) | the Lean toolchain is about 3 GB unpacked |

Installing .NET on Linux without root:

```sh
curl -sSfL https://dot.net/v1/dotnet-install.sh -o dotnet-install.sh
bash dotnet-install.sh --channel 10.0 --install-dir "$HOME/.dotnet"
export PATH="$HOME/.dotnet:$PATH"
dotnet --list-sdks
```

### 2. Build and test

```sh
git clone https://github.com/icosahedron/csharp-ansatz.git
cd csharp-ansatz
git checkout claude/ansatz-csharp-design-00846r   # until merged
dotnet build
dotnet test
```

Expected result: **136 tests pass and one is skipped** (`AcceptsFullInit`, which
needs the full Init export; see step 5). That's 31 Cic, 42 Lean4Export and 64
Kernel tests, with the whole suite taking well under a minute.

### 3. Run the kernel on the committed corpus

The `leansharp` command-line tool checks any lean4export file. Its exit codes
follow the Lean Kernel Arena convention: 0 means everything was accepted, 1 means
something was rejected, and 2 means the input was unreadable or a resource limit
was hit.

```sh
alias leansharp='dotnet run -c Release --project src/LeanSharp.Cli --'

leansharp stats tests/data/init-medium.ndjson.gz
leansharp check tests/data/init-medium.ndjson.gz --quiet     # exit 0
leansharp check tests/data/arena/002_badDef.ndjson           # exit 1
```

Expected verdicts:

| File | Expected |
|---|---|
| `init-medium.ndjson.gz` | accepted 4,631, rejected 0 (5,118 constants), a few seconds |
| `Nat.add_succ.ndjson` | accepted 19, rejected 0 |
| `arena/001_basicDef.ndjson`, `arena/sparse-name-index.ndjson` | all accepted |
| `arena/002_badDef.ndjson` | `badDef` rejected (type mismatch) |
| `arena/141_falseFromUnsafe.ndjson` | `unsafeLoop` accepted, `falseFromUnsafe` rejected |
| `arena/proj-of-subst-prop.ndjson` | `PR14806Subst.observe` rejected, everything else accepted |
| `arena/rec-of-subst-prop.ndjson` | `Issue.forallFalse` rejected, everything else accepted |

### 4. Verify the test data and its counts independently

The test data comes from upstream projects (provenance in
[tests/data/README.md](tests/data/README.md)). To confirm the files are unchanged:

```sh
sha256sum tests/data/*.ndjson* tests/data/arena/*.ndjson
```

| File | SHA-256 |
|---|---|
| `Nat.add_succ.ndjson` | `4ef6d64908b3b120c23fb383eea6a56b059efc51c87b01b39d1427e4e39bf49b` |
| `init-medium.ndjson.gz` | `8ec11981455e9c8a046731fc84af424151a02014e788a26ec085cf01617da8e7` |
| `arena/001_basicDef.ndjson` | `82023f63efe0d75e9966621bfc69033ccd1333e8d0d989b3d54a79859e9da0ce` |
| `arena/002_badDef.ndjson` | `d1342aceb5741fc040523d3b4bd5e1ae3160dc17213d1dc0f6d766559a93a227` |
| `arena/141_falseFromUnsafe.ndjson` | `ef646a5368b95ad4021069a0c9906a6b5e11c0abcfd22673821e6bd20f26e0a8` |
| `arena/proj-of-subst-prop.ndjson` | `1c9d8a266c198b7d4a1cfbe3fffd2de2d2b75e603fb3cedfa5d5309f7b295b9d` |
| `arena/rec-of-subst-prop.ndjson` | `fa498cf880a5390e65c3990e8361829a5012de4fae133dbfcd6a81af26f74ca8` |
| `arena/sparse-name-index.ndjson` | `3279c9c8ae24d5b3a8433ddee5d4a421c4e15e3cd84117fb4873d1284112b96d` |

To fetch the originals and compare:

```sh
git clone --depth 1 https://github.com/leanprover/lean4export   # examples/Nat.add_succ.ndjson
git clone https://github.com/replikativ/ansatz && git -C ansatz checkout 662ac21
#   resources/ansatz/init-medium.ndjson.gz, test-data/arena/*.ndjson
```

The independent counts (the numbers the tests assert) come from:

```sh
python3 scripts/count-export.py tests/data/Nat.add_succ.ndjson tests/data/init-medium.ndjson.gz tests/data/arena/*.ndjson
```

### 5. Export and check the full Init library

```sh
scripts/export-lean-library.sh Init init.ndjson
```

The script downloads the Lean 4.33.1 toolchain (about 900 MB as a zip), builds
lean4export at commit `15f6055` (the last one pinned to Lean v4.33), and runs
`lean4export Init`. The export takes about 20 seconds and produces a 348 MB file
with 57,977 declaration records.

```sh
python3 scripts/count-export.py init.ndjson     # 59,433 constants
leansharp check init.ndjson --quiet             # accepted 57,977, rejected 0 (about 75 s)
LEANSHARP_INIT_EXPORT=$PWD/init.ndjson dotnet test --filter AcceptsFullInit
```

The script runs code downloaded from GitHub (the Lean toolchain, lean4export), so
review it before running. In a Claude Code session, auto mode may block it;
approve it in **Accept edits** mode.

### 6. Re-derive the port from its sources (optional)

To compare the kernel with the C++ it was ported from:

```sh
git clone --depth 1 --branch v4.33.1 --filter=blob:none --sparse https://github.com/leanprover/lean4
git -C lean4 sparse-checkout set src/kernel
```

[docs/kernel.md](docs/kernel.md) maps each C++ file to its C# counterpart and
lists the deliberate differences: fuel, no native reduction, a large-stack
thread, and macro scopes in generated names not being modelled.

### 7. Mathlib (not yet done)

The same export script should work from a Mathlib checkout pinned to v4.33.1.
For example, run `lake env <path>/lean4export Mathlib > mathlib.ndjson` inside
`mathlib4` after `lake exe cache get`. Ansatz reports 707,508 declarations, all
verified by its kernel. LeanSharp has not run this yet; expect a multi-gigabyte
export, and memory use that has not been measured at that scale.

---

## Repository map

| Path | Contents |
|---|---|
| `src/LeanSharp.Cic` | CIC terms: names, levels, expressions, constants, declarations |
| `src/LeanSharp.Lean4Export` | lean4export reader (3.0.0, 3.1.0) and writer (3.1.0) |
| `src/LeanSharp.Kernel` | the type-checking kernel and the export checker |
| `src/LeanSharp.Cli` | the `leansharp` tool (`check`, `stats`) |
| `tests/` | unit, corpus and soundness tests; `tests/data` is the corpus |
| `scripts/` | `export-lean-library.sh`, `count-export.py` |
| `docs/` | design, kernel notes, conversation history |
