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

### Milestone 5a: proofs about every input, in the build

The plan is [docs/plans/2026-11-03-0838-feat-m5a-meta-tactics-plan.md](docs/plans/2026-11-03-0838-feat-m5a-meta-tactics-plan.md),
and the design is explained chapter by chapter in [docs/m5a/](docs/m5a/README.md).

1. **Port Lean's own Meta layer, function by function.** `Warrant.Meta`
   (metavariable contexts, `whnf`, `isDefEq`, `inferType`, discrimination
   trees, instance resolution, the tactics, `simp` and `omega`) follows Lean
   4.35.0's sources, so it builds the proofs Lean would. The kernel rejects
   any term with a metavariable, so the port stays outside the trusted base.
2. **Export what the bundle lacks from Lean itself.** `tools/warrant-attrs`
   exports the simp, instance, reducibility and matcher attributes of the
   bundle's constants as the committed sidecar
   `tests/data/warrant-attributes.ndjson.gz`, which names the bundle's hash.
3. **Use Lean as the oracle.** The discrimination-tree keys Warrant computes
   are compared with the keys Lean exported for all 346 simp lemmas, and the
   failure messages of `omega` and the other tactics are compared with Lean's
   text for the tested goals.
4. **Write the corpus first.** `tests/corpus/m5a/` holds the exit criterion as
   accepted, refuted and rejected C#.
5. **Run the real build.** The build integration tests pack the `Warrant` and
   `Warrant.Build` packages, consume them from sample projects, and build them
   with `dotnet build`, Visual Studio 2026's MSBuild and Visual Studio 2022's
   MSBuild.
6. **Compare with other kernels.** `scripts/cross-kernel.sh` puts Warrant's
   verdicts next to Lean's, Ansatz's and the lean-kernel-arena's published
   ones; the results are in [docs/kernel.md](docs/kernel.md).

### Milestone 5b, first step: Mathlib

Store v1 could not be laid out until the cost of holding Mathlib was known, so
M5b began by checking it ([docs/mathlib.md](docs/mathlib.md)).

1. **Export it with the same tools as `Init`.** Mathlib v4.35.0 through the
   same lean4export build: 712,205 declarations, 729,263 constants, 6.3 GB.
2. **Measure while checking.** `warrant check` accepts all of it in 26 minutes.
   A sampling script recorded the peak memory, 12.6 GB, and the new
   `--slowest` option recorded which declarations take longest.
3. **Have Lean agree twice.** Lean's kernel accepts the export, and it accepts
   the file `warrant export` writes from it.

### Milestone 5b: a server, a cache and a store

The plan is [docs/plans/2026-11-05-1640-feat-m5b-server-cache-store-plan.md](docs/plans/2026-11-05-1640-feat-m5b-server-cache-store-plan.md),
and the design is explained chapter by chapter in [docs/m5b/](docs/m5b/README.md).

1. **One service, two hosts.** The verification moved into a
   `VerificationService` that the server and the CLI's in-process path both
   run, and a parity test compares their output byte for byte, ten times over,
   on the M4 and M5a corpora.
2. **Make every run give the same answer.** Theorems run in parallel, a cached
   result must equal a fresh one, and the server must agree with the
   in-process path, so the counterexample search lost its clock and a script's
   `Lean.Const` may no longer reach a constant it does not depend on.
3. **Keep cancellation reject-only.** The kernel polls a cancellation token
   where it already checked its deadline; tests show a cancelled check can
   only reject, and that Meta does not turn it into "not proved".
4. **Cache, then make CI distrust the cache.** Entries are keyed by the
   closure hash, the toolchain identity and the bundle's and sidecar's hashes;
   `WarrantRecheck` re-checks every cached proof against a statement rebuilt
   from the current code. A test swaps one cached proof for another theorem's
   and expects WRT0010.
5. **Lay the store out against Mathlib.** Store v1 was measured on all of
   Mathlib (a 1.45 GB store, a 21 MB managed heap after 1,000 lookups), and
   the Init + semantics store passes `check-store` with the kernel.
6. **Write the exit criterion as tests.** Each item of design §11's M5b row
   is a test in `M5bExitTests`, and `scripts/measure-m5b.sh` records the
   baselines M9 starts from.

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
| Visual Studio 2026 and 2022 | the build integration tests on Visual Studio's MSBuild (optional) | found with `vswhere`; a missing one is reported as not run |
| Java and the Clojure CLI, an Ansatz checkout | the Ansatz column of the cross-kernel harness (optional) | without them that column says SKIPPED |

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

Expected result on Windows: **1,209 tests pass and 29 are skipped**. The
skipped ones are opt-in tests that need external files or tools:
`AcceptsFullInit` and the two Init store tests (need `WARRANT_INIT_EXPORT`,
steps 5 and 7d), `WritesFixturesForLean` (used by `scripts/cross-check.sh`),
the export-script test (needs `LEAN_TOOLCHAIN_BIN`), the two differential-cost
measurements (need `WARRANT_DIFFERENTIAL_COST`), the 18 build tests that pack
the packages and run real builds (need `WARRANT_BUILD_INTEGRATION=1`, step 7b),
and four server tests of Unix socket directories, which run only on Linux and
macOS (where one Windows-only server test is skipped instead). With
`WARRANT_BUILD_INTEGRATION=1` and `WARRANT_INIT_EXPORT` set, 1,230 pass and 8
are skipped. By project, with both set: 33 Cic, 44 Vir, 339 Extraction,
82 Semantics, 122 Meta, 42 Lean4Export, 114 Kernel, 262 Engine, 21 Store,
13 Server, 11 Analyzers and 4 more under Roslyn 4.8, 87 Cli and 56 Build. The
build reports no warnings. No Lean toolchain is needed. Without the opt-ins the
whole suite takes about five minutes on a 32-core machine, most of it the CLI
tests, which start real servers; each of them shuts its server down, so no
`warrant-server` process is left afterwards.

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
`5a9a355` (the one built for Lean v4.35.0), and runs `lean4export --export-mdata Init`. The
export takes about 15 seconds and produces a 348 MB file with 57,919
declaration records. Metadata is exported as it is for the semantics bundle, so the
Init constants the bundle repeats are identical to these and the two files can be
imported into one store (`EXPORT_MDATA=0` exports without it). An Init export
made before the script did this (commit `3d0566f`) has no metadata, and
importing it with the bundle fails with "'Nat.beq' differs from the constant of
that name an earlier file declared"; export it again.

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
step 5 (on Windows, see `scripts/lib/lean-toolchain.sh` for how the toolchain
is found), builds the library with `lake build`, and exports the 605 roots in
`lean/bundle-roots.txt` with their dependency closure. It exports with
`--export-mdata`, so the `no_index` markers simp needs survive. It fails if a
root does not exist or if anything depends on `sorryAx`. The output is
deterministic: with an unchanged `lean/`, it is byte-identical to the
committed file. Check the counts independently with:

```sh
python3 scripts/count-export.py tests/data/warrant-semantics.ndjson.gz   # 4,109 constants
```

The attribute sidecar that tactics read is exported from the same library and
bundle, after the bundle:

```sh
scripts/export-attributes.sh                    # writes tests/data/warrant-attributes.ndjson.gz
```

It is deterministic too, and its header records the bundle's SHA-256, which
`warrant verify` checks.

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
79 unit(s): 46 translated, 33 proved, 0 false, 0 unproved, 0 undecided, 0 internal error(s), 0 failed, 0 skipped; 0 error(s), 0 warning(s)
```

On `refuted/` it reports both theorems as false, for example:

```text
tests/corpus/m4/refuted/Increment.cs(12,18): error WRT0001: Theorem 'Increments.NeverWraps()' is false.
  Claim:  Increment(int.MaxValue) > int.MaxValue
  Values: Increment(int.MaxValue) = -2147483648, int.MaxValue = 2147483647
```

`--report` writes the assumption report as Markdown, and `--out` writes the
bundle followed by every admitted declaration as lean4export NDJSON, which
`tools/lean-replay` accepts (2,956 constants for `accepted/`). Running
`rejected/` as one directory compiles `rejected/CheckedProject.cs` without
overflow checking, so its members translate there; the corpus tests compile
that file on its own with overflow checking on, as `expected.json` says. The
exit codes are 0 when everything
translated and every theorem was proved, 1 otherwise, and 2 for bad arguments
or unreadable input.

### 7a. Prove theorems with `warrant verify`

```sh
warrant verify tests/corpus/m5a/accepted                        # exit 0
warrant verify tests/corpus/m5a/refuted                         # exit 1, WRT0001
warrant verify tests/corpus/m5a/rejected                        # exit 1, WRT0002 and WRT0004
warrant verify tests/corpus/m5a/accepted --report report --out m5a.ndjson
```

`warrant verify` is M5a's verb: it compiles, extracts, translates and proves,
running each theorem's `.By(...)` script. On a directory it compiles every
`.cs` file under it as `translate` does. On `accepted/` it ends with:

```text
Warrant: 20 verified units, 7 theorems proved, 0 not proved.
```

From M5b it runs in-process unless `--server auto` is given, and uses a result
cache only with `--cache-dir`:

```sh
warrant verify tests/corpus/m5a/accepted --server auto --cache-dir /tmp/m5a-cache --timings
warrant verify tests/corpus/m5a/accepted --server auto --cache-dir /tmp/m5a-cache            # (10 from cache)
warrant verify tests/corpus/m5a/accepted --server auto --cache-dir /tmp/m5a-cache --recheck  # (10 from cache, 10 rechecked)
warrant explain AlwaysLarger --sources tests/corpus/m5a/refuted                              # each tactic with its goals
warrant server status
warrant server shutdown
```

The first starts a verification server (about 3 seconds, most of it loading
and checking the semantics bundle) and ends with
`Warrant: 20 verified units, 7 theorems proved, 0 not proved. [server]`, then
`--timings`' lines. The second takes its theorems and recursive methods from
the cache and runs no tactics; the third has the kernel re-check each cached
proof. `server status` prints the server's memory and cache counters.

On `refuted/` it reports `AlwaysLarger` with the counterexample
`x = 2147483647` and `Bad`'s decrease obligation, each with `omega`'s
constraints and the goal ([docs/m5a/README.md](docs/m5a/README.md) shows the
output). `--report <dir>` writes `report.md` and `report.json`; `--out` writes
the bundle and every admitted declaration (2,879 constants for `accepted/`).

The build runs the same verb with `--csc-args`, the compiler's own argument
list, which the `Warrant.Build` task writes to `obj/…/warrant.csc.args`
([docs/m5a/07](docs/m5a/07-verify-and-build.md)). The options and exit codes
are in [the reference](docs/proving/reference.md#cli).

### 7b. Build integration tests

The `Warrant.Build.Tests` project packs the `Warrant` and `Warrant.Build`
packages and builds sample projects that reference them. These tests are
opt-in, because they run real builds:

```sh
WARRANT_BUILD_INTEGRATION=1 dotnet test tests/Warrant.Build.Tests
```

They build the `Increment` sample with `dotnet build`, Visual Studio 2026's
`MSBuild.exe` (a `net10.0` sample) and Visual Studio 2022's `MSBuild.exe` (a
`net8.0` sample pinned to SDK 9 by its own `global.json`, because SDK 10 needs
MSBuild 18), each through a verification server of its own that the test shuts
down afterwards, and expect the same WRT0001 diagnostics, with goal and
counterexample, from each. They find Visual Studio with `vswhere`; a version
that is not installed is reported as not run, never as passed. Other tests
cover a green build, a second build, design-time builds, multi-targeting, an
`#if` that differs between frameworks, a missing `Warrant.Build` (WRT0011),
a library consumed by an application, and code that needs the SDK's regex
source generator, which the CLI runs. From M5b they also build a green sample
three times (the second from the cache, the third with `WarrantRecheck=true`),
check that `dotnet clean` deletes the cache and nothing else, and that the IDE
analyzer runs only in design-time builds.

How Visual Studio's Error List shows a multi-line WRT0001 is checked by hand,
in the IDE; that check has not been done yet.

### 7c. Long property runs

The differential tests are FsCheck properties with a pinned seed. For a
longer search, 10,000 cases per function:

```sh
WARRANT_PBT_LONG=1 dotnet test --filter Differential
```

A failure prints `Replay with WARRANT_PBT_SEED=seed,gamma`; set that variable
to replay it. `WARRANT_PBT_SEED=random` draws a new seed, and
`WARRANT_PBT_COUNT` sets the count ([tests/Warrant.Engine.Tests/Differential/README.md](tests/Warrant.Engine.Tests/Differential/README.md)).

### 7d. M5b's exit criterion

```sh
dotnet test tests/Warrant.Cli.Tests --filter M5bExit
WARRANT_INIT_EXPORT=$PWD/init.ndjson dotnet test tests/Warrant.Cli.Tests --filter M5bExit
```

Each item of design §11's M5b row is one test in `M5bExitTests`
([docs/m5b/08](docs/m5b/08-testing-and-baselines.md#the-exit-criterion-as-tests)),
each against a `warrant-server` process of its own. Without
`WARRANT_INIT_EXPORT`, 8 pass and the Init + semantics store test is skipped;
with the Init export of step 5, all 9 pass. That test imports Init and the
bundle into a verified store and runs `check-store` on it, which took about
2 minutes 50 seconds on a 32-core machine. Analyzer determinism is tested in
`Warrant.Analyzers.Tests`
(`TwentyConcurrentRunsGiveByteIdenticalDiagnosticsAndTheAnalyzerNeverThrows`),
and the build matrix through the server in step 7b.

To build the same store by hand:

```sh
warrant import init.ndjson tests/data/warrant-semantics.ndjson.gz --store init-semantics --verified
warrant check-store init-semantics --quiet      # accepted 57,944, rejected 0; 59,374 constants
```

### 8. Cross-check against Lean's own kernel

```sh
scripts/cross-check.sh
WARRANT_INIT_EXPORT=$PWD/init.ndjson scripts/cross-check.sh   # include full Init
```

The script uses the same Lean 4.35.0 toolchain (downloaded if needed, or set
`LEAN_TOOLCHAIN_BIN` to reuse one; on Windows, see
`scripts/lib/lean-toolchain.sh` for how the toolchain is found) and builds
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
M5a corpus                   -         accept    accept         ok
M5a tampered                 -         reject    reject         ok

all verdicts agree
```

The last two rows are M5a's: `warrant verify tests/corpus/m5a/accepted --out`
must exit 0 and Lean must accept its certificate, and a copy whose last
theorem's proof is swapped for the one before it must be rejected by both
kernels. On Windows (Git Bash, 2026-11-07) every row agrees.

Lean declines the original `Nat.add_succ` only because its parser reads format
3.1.0. Warrant's export of it is 3.1.0, and Lean accepts that. With the full
Init export included, Lean accepts all 59,349 constants Warrant writes.

### 8a. Compare with other kernels

```sh
scripts/cross-kernel.sh
```

The harness puts one verdict per kernel on each row: Lean's kernel (through
`tools/lean-replay`), Warrant's, Ansatz's `arena-check`, and the verdicts the
lean-kernel-arena publishes for the official kernel, nanoda and lean4lean. It
downloads the arena's tests and `results.json` at a recorded commit, and skips
any test whose SHA-256 does not match. It exits 1 only when Warrant
contradicts an expected outcome or Lean rejects something Warrant wrote.

The Ansatz column needs Java, the Clojure CLI (`clojure` on `PATH`; on Windows,
deps.clj installed as `clojure.exe` works) and an Ansatz checkout built once
with `clojure -T:build javac`, in `../ansatz` or wherever `ANSATZ_DIR` points.
Without them, that column says SKIPPED and the rest still runs. A full run
takes about an hour, most of it Ansatz; `ARENA_ONLY=1` runs only the arena
tests, and `KERNEL_TIMEOUT` sets the per-kernel timeout in seconds (900 by
default). The table is also written to `cross-kernel/verdicts.tsv` in the work
directory. The recorded results and every disagreement are in
[docs/kernel.md](docs/kernel.md).

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

### 10. Mathlib

Step 5 builds lean4export at `<workdir>/lean4export/.lake/build/bin/lean4export`
(the work directory defaults to `$TMPDIR/warrant-lean`). Step 8 builds
`tools/lean-replay`. Export Mathlib v4.35.0, the release for the same Lean version:

```sh
git clone --depth 1 --branch v4.35.0 https://github.com/leanprover-community/mathlib4
cd mathlib4
lake exe cache get                                   # prebuilt .olean files
# about 5 minutes; writes 6.3 GB
lake env <workdir>/lean4export/.lake/build/bin/lean4export Mathlib > mathlib.ndjson
```

```sh
python3 scripts/count-export.py mathlib.ndjson        # 729,263 constants
warrant check mathlib.ndjson --quiet --slowest 20     # accepted 712,205, rejected 0 (about 26 min)
warrant export mathlib.ndjson mathlib.warrant.ndjson --quiet
tools/lean-replay/.lake/build/bin/lean-replay mathlib.ndjson          # accepted: 729263 constants
tools/lean-replay/.lake/build/bin/lean-replay mathlib.warrant.ndjson  # accepted: 729263 constants
```

Use the Release build, and allow about 13 GB of memory for the check. The
times, the peak memory and the slowest declarations from one run are in
[docs/mathlib.md](docs/mathlib.md). Windows does not report a process's
peak memory once it exits, so that run sampled it while the check ran.

### 11. Baselines for M9

```sh
scripts/measure-m5b.sh                         # the latency and server memory tables
MEASURE_DIR=/big/disk scripts/measure-m5b.sh mathlib.ndjson   # and the Mathlib store
```

The script builds the CLI in Release and, for each M5a sample, runs
`warrant verify --timings` cold (it starts a server), warm, from the cache,
with `--recheck` and in-process, on a server of its own that it shuts down at
the end. Given the Mathlib export of step 10, it also imports it into a
trusted store in `MEASURE_DIR` (allow about 1.5 GB) and opens it with
`warrant sample-store`. It prints Markdown tables; the run recorded in
[docs/m5b/08](docs/m5b/08-testing-and-baselines.md#baselines-for-m9) and
design §11 was made on a 32-core Windows workstation, from Git Bash; its
Mathlib import took 139 s.

---

## Repository map

| Path | Contents |
|---|---|
| `src/Warrant.Cic` | CIC terms: names, levels, expressions, constants, declarations |
| `src/Warrant.Lean4Export` | lean4export reader (3.0.0, 3.1.0) and writer (3.1.0) |
| `src/Warrant.Kernel` | the type-checking kernel and the export checker |
| `src/Warrant` | the user package: `[Verified]`, `[Theorem]`, `[Closed]`, `Prove`, `Spec`, `Tactic`, `Lean`, and the WRT0011 check in `build/` |
| `src/Warrant.Vir` | VIR: the model, its canonical JSON encoding and its hashes |
| `src/Warrant.Frontend` | the Roslyn compilation that extraction reads |
| `src/Warrant.Extraction` | C# (Roslyn `IOperation`) to VIR, and the M4 subset checks |
| `src/Warrant.Semantics` | VIR to CIC: types, definitions and theorem statements |
| `src/Warrant.Meta` | the untrusted Meta layer: metavariables, reduction and unification, the attribute sidecar, the tactics, `simp` and `omega` |
| `src/Warrant.Engine` | admission, proofs, proof scripts, counterexamples, read-back, assumption reports and NDJSON output; the `VerificationService`, its worker pool and the result cache (`Service/`) |
| `src/Warrant.Server` | `warrant-server`: the endpoint, the JSON-RPC methods, the lifecycle and the log |
| `src/Warrant.Store` | store v1: the writer, the reader and the kernel's lazy constant source |
| `src/Warrant.Analyzers` | the IDE analyzer, which compiles in the Extraction and Vir sources |
| `src/Warrant.Cli` | the `warrant` tool (`check`, `stats`, `export`, `translate`, `verify`, `explain`, `server`, `import`, `check-store`, `sample-store`), the server client and launcher |
| `src/Warrant.Build` | the MSBuild task and targets that run `warrant verify` after `CoreCompile`, and delete the result cache on `Clean` |
| `lean/` | the semantics library, proved in Lean, and the bundle roots |
| `tools/lean-replay` | Lean program: check an NDJSON file with Lean's own kernel |
| `tools/warrant-attrs` | Lean program: export the attribute sidecar |
| `tests/` | unit, corpus and soundness tests; `tests/data` is the kernel corpus, the semantics bundle and the attribute sidecar, `tests/corpus/m4` and `tests/corpus/m5a` the C# corpora |
| `scripts/` | `export-lean-library.sh`, `export-semantics.sh`, `export-attributes.sh`, `cross-check.sh`, `cross-kernel.sh`, `measure-m5b.sh`, `count-export.py`, shared `lib/lean-toolchain.sh` and `lib/arena.sh` |
| `docs/` | design, kernel notes, conversation history |
