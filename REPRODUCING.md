# Reproducing Warrant's results

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
   names and binder info, so Warrant's caches and comparisons do too
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

### Milestone 3: cross-checking

1. **Run Lean's own kernel on the same data.** `tools/lean-replay` combines
   lean4export's parser with `Lean.Environment.replay`, the routine lean4checker
   uses. Lean's verdicts on the corpus match Warrant's exactly.
2. **Have Lean re-check what Warrant admitted.** `warrant export` writes the
   kernel's own generated constructors and recursors. Replay demands they equal
   Lean's, so this checks the recursor generation itself. It holds for the
   corpus, full Init, and new types built in C# (mutual, nested, structure,
   universe-polymorphic, K-like). Tampering with one recursor makes Lean reject
   the file, which shows the harness can fail.
3. **Property-based tests** (FsCheck) compare the kernel with independent
   meanings: level evaluation, BigInteger arithmetic, and the typing rules of a
   small generated language. They found that Lean's level normalization isn't
   idempotent (incomplete but sound, and matched exactly); see
   [docs/kernel.md](docs/kernel.md#property-based-tests-milestone-3).

### Milestone 4: translating C#

The plan is [docs/plans/2026-11-02-1245-feat-m4-pure-subset-plan.md](docs/plans/2026-11-02-1245-feat-m4-pure-subset-plan.md),
and the design is explained chapter by chapter in [docs/m4/](docs/m4/README.md).

1. **Model C# with Lean's own types, and prove the facts in Lean.** C# `int`,
   `long` and `bool` are Init's `Int32`, `Int64` and `Bool`. The `lean/`
   project states the CLR facts the translator relies on as theorems, and
   `scripts/export-semantics.sh` exports it, with every Init constant the
   translator emits, as the committed bundle
   `tests/data/warrant-semantics.ndjson.gz`.
2. **Write the corpus before the extractor.** `tests/corpus/m4/` holds the
   accepted, refuted and rejected C# members, and `expected.json` the outcome
   of each, so every rule had a failing test first.
3. **Copy Lean's term shapes.** Each operator, condition and proof term was
   elaborated in Lean 4.35.0 and printed with `pp.all`, and translation emits
   the same shapes.
4. **Test the model against the CLR.** CLR-agreement tests compare every
   operator with unchecked C# on boundary and random operands, and
   differential tests compare each translated method with the compiled one.
5. **Have Lean re-check the result.** `warrant translate --out` writes the
   bundle and every translated declaration and proved theorem, and Lean's
   kernel checks that file in `scripts/cross-check.sh`.

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

Expected result: **538 tests pass and four are skipped**. The skipped ones are
opt-in tests that need external files or tools: `AcceptsFullInit` and
`WritesFixturesForLean` (the kernel's Lean cross-checks), the export-script test
(needs `LEAN_TOOLCHAIN_BIN`), and the differential-cost measurement (needs
`WARRANT_DIFFERENTIAL_COST`). By project: 31 Cic, 36 Vir, 208 Extraction,
65 Semantics, 42 Lean4Export, 85 Kernel, 64 Engine and 7 Cli. No Lean toolchain
is needed; the whole suite takes about a minute.

### 3. Run the kernel on the committed corpus

The `warrant` command-line tool checks any lean4export file. Its exit codes
follow the Lean Kernel Arena convention: 0 means everything was accepted, 1 means
something was rejected, and 2 means the input was unreadable or a resource limit
was hit.

```sh
alias warrant='dotnet run -c Release --project src/Warrant.Cli --'

warrant stats tests/data/init-medium.ndjson.gz
warrant check tests/data/init-medium.ndjson.gz --quiet     # exit 0
warrant check tests/data/arena/002_badDef.ndjson           # exit 1
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

The script downloads the Lean 4.35.0 toolchain, builds lean4export at commit
`5a9a355` (the one built for Lean v4.35.0), and runs `lean4export Init`. The
export takes about 15 seconds and produces a 346 MB file with 57,919
declaration records.

On Windows, run the scripts from Git Bash and point them at a toolchain
installed with elan instead of the Linux download:

```sh
elan toolchain install leanprover/lean4:v4.35.0
export LEAN_TOOLCHAIN_BIN="$(cygpath -u "$(lean +leanprover/lean4:v4.35.0 --print-prefix)")/bin"
```

```sh
python3 scripts/count-export.py init.ndjson     # 59,349 constants
warrant check init.ndjson --quiet             # accepted 57,919, rejected 0 (about 45 s)
WARRANT_INIT_EXPORT=$PWD/init.ndjson dotnet test --filter AcceptsFullInit
```

The script runs code downloaded from GitHub (the Lean toolchain, lean4export), so
review it before running. In a Claude Code session, auto mode may block it;
approve it in **Accept edits** mode.

### 6. Regenerate the semantics bundle

The bundle that the M4 tests and `warrant translate` load is committed, so
nothing here is needed to run the tests. To rebuild it from `lean/`:

```sh
scripts/export-semantics.sh                     # writes tests/data/warrant-semantics.ndjson.gz
scripts/export-semantics.sh /tmp/bundle.ndjson.gz   # or anywhere else
```

The script uses the same Lean 4.35.0 toolchain and lean4export `5a9a355` as
step 5 (set `LEAN_TOOLCHAIN_BIN` on Windows), builds the library with
`lake build`, and exports the 74 roots in `lean/bundle-roots.txt` with their
dependency closure. It fails if a root does not exist or if anything depends on
`sorryAx`. The output is deterministic: with an unchanged `lean/`, it is
byte-identical to the committed file. Check the counts independently with:

```sh
python3 scripts/count-export.py tests/data/warrant-semantics.ndjson.gz   # 2,483 constants
```

### 7. Translate C# with `warrant translate`

```sh
warrant translate tests/corpus/m4/accepted                      # exit 0
warrant translate tests/corpus/m4/refuted                       # exit 1, WRT0001
warrant translate tests/corpus/m4/rejected                      # exit 1, WRT0002 to WRT0009
warrant translate tests/corpus/m4/accepted --report report.md --out m4.ndjson
```

The verb compiles every `.cs` file under the directory, translates the
`[Verified]` members and `[Theorem]`s, and prints one line per unit and any
diagnostics. On `accepted/` it ends with:

```text
65 unit(s): 32 translated, 33 proved, 0 false, 0 undecided, 0 failed, 0 skipped; 0 error(s), 0 warning(s)
```

On `refuted/` it reports both theorems as false, for example:

```text
tests/corpus/m4/refuted/Increment.cs(12,18): error WRT0001: Theorem 'NeverWraps' is false.
  Claim:  Increment(int.MaxValue) > int.MaxValue
  Values: Increment(int.MaxValue) = -2147483648, int.MaxValue = 2147483647
```

`--report` writes the assumption report as Markdown, and `--out` writes the
bundle followed by every admitted declaration as lean4export NDJSON, which
`tools/lean-replay` accepts (2,576 constants for `accepted/`). Running
`rejected/` as one directory compiles `rejected/CheckedProject.cs` without
overflow checking, so its members translate there; the corpus tests compile
that file on its own with overflow checking on, as `expected.json` says. The
exit codes are 0 when everything
translated and every theorem was proved, 1 otherwise, and 2 for bad arguments
or unreadable input.

### 8. Cross-check against Lean's own kernel

```sh
scripts/cross-check.sh
WARRANT_INIT_EXPORT=$PWD/init.ndjson scripts/cross-check.sh   # include full Init
```

The script uses the same Lean 4.35.0 toolchain (downloaded if needed; set
`LEAN_TOOLCHAIN_BIN` to reuse one) and builds
[`tools/lean-replay`](tools/lean-replay/README.md), a small Lean program that
checks an NDJSON file with Lean's kernel. For every corpus file it compares Lean's
verdict with Warrant's. It then has Lean re-check what Warrant admitted
(`warrant export`), the declarations built from scratch in C#
(`CrossCheckFixtures.cs`), and the translated M4 corpus: `warrant translate
tests/corpus/m4/accepted --out` must exit 0, and Lean must accept the file it
writes. Expected output ends with:

```
FILE                         LEAN      WARRANT LEAN(EXPORT)   RESULT
init-medium.ndjson.gz        accept    accept    accept         ok
Nat.add_succ.ndjson          decline   accept    accept         ok
001_basicDef.ndjson          accept    accept    accept         ok
002_badDef.ndjson            reject    reject    accept         ok
141_falseFromUnsafe.ndjson   reject    reject    accept         ok
proj-of-subst-prop.ndjson    reject    reject    accept         ok
rec-of-subst-prop.ndjson     reject    reject    accept         ok
sparse-name-index.ndjson     accept    accept    accept         ok
C# fixtures                  -         accept    accept         ok
M4 corpus                    -         accept    accept         ok

all verdicts agree
```

Lean declines the original `Nat.add_succ` only because its parser reads format
3.1.0. Warrant's export of it is 3.1.0, and Lean accepts that. With the full
Init export included, Lean accepts all 59,349 constants Warrant writes.

### 9. Re-derive the port from its sources (optional)

To compare the kernel with the C++ it was ported from:

```sh
git clone --depth 1 --branch v4.33.1 --filter=blob:none --sparse https://github.com/leanprover/lean4
git -C lean4 sparse-checkout set src/kernel
git -C lean4 fetch --depth 1 origin tag v4.35.0
git -C lean4 diff v4.33.1 v4.35.0 -- src/kernel   # what changed since the port
```

[docs/kernel.md](docs/kernel.md) maps each C++ file to its C# counterpart and
lists the deliberate differences: fuel, no native reduction, a large-stack
thread, and macro scopes in generated names not being modelled.

### 10. Mathlib (not yet done)

The same export script should work from a Mathlib checkout pinned to the same Lean version (v4.35.0).
For example, run `lake env <path>/lean4export Mathlib > mathlib.ndjson` inside
`mathlib4` after `lake exe cache get`. Ansatz reports 707,508 declarations, all
verified by its kernel. Warrant has not run this yet; expect a multi-gigabyte
export, and memory use that has not been measured at that scale.

---

## Repository map

| Path | Contents |
|---|---|
| `src/Warrant.Cic` | CIC terms: names, levels, expressions, constants, declarations |
| `src/Warrant.Lean4Export` | lean4export reader (3.0.0, 3.1.0) and writer (3.1.0) |
| `src/Warrant.Kernel` | the type-checking kernel and the export checker |
| `src/Warrant` | the user package: `[Verified]`, `[Theorem]`, `[Closed]`, `Prove`, `Spec` |
| `src/Warrant.Vir` | VIR: the model, its canonical JSON encoding and its hashes |
| `src/Warrant.Frontend` | the Roslyn compilation that extraction reads |
| `src/Warrant.Extraction` | C# (Roslyn `IOperation`) to VIR, and the M4 subset checks |
| `src/Warrant.Semantics` | VIR to CIC: types, definitions and theorem statements |
| `src/Warrant.Engine` | admission, proofs, read-back, assumption reports and NDJSON output |
| `src/Warrant.Cli` | the `warrant` tool (`check`, `stats`, `export`, `translate`) |
| `lean/` | the semantics library, proved in Lean, and the bundle roots |
| `tools/lean-replay` | Lean program: check an NDJSON file with Lean's own kernel |
| `tests/` | unit, corpus and soundness tests; `tests/data` is the kernel corpus and the semantics bundle, `tests/corpus/m4` the C# corpus |
| `scripts/` | `export-lean-library.sh`, `export-semantics.sh`, `cross-check.sh`, `count-export.py`, shared `lib/lean-toolchain.sh` |
| `docs/` | design, kernel notes, conversation history |
