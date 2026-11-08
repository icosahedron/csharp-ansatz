# 8. Testing and baselines

> Part of the [M5b design](README.md). Decisions: KTD28 to KTD30.

## Parity

The server and the in-process fallback run the same `VerificationService` (chapter 1), so their output should be identical.
A test makes sure (KTD28, `ParityTests`): it runs the M5a exit corpus, the M4 corpus and a project built from a Csc argument file through a server and in-process, ten times over, and compares the `--format msbuild` output byte for byte.
Outcomes decided by a wall-clock limit are excluded, because they depend on the machine's load, which is also why they are never cached (chapter 4).
So are the parts of the output that report where results came from: the summary's cached count and `[server|in-process]` tag, and the message a fallback logs, whose absence on the server path is checked, so the comparison really is between the two paths.

## The exit criterion as tests

Each item of design §11's M5b row is its own test in `M5bExitTests`, so a failure names the item.
Each test runs `warrant verify` against a `warrant-server` process of its own, which the CLI starts on a unique endpoint, and checks that the process is gone once the server is shut down.
`dotnet test --filter M5bExit` runs them: 9 tests, all passing on Windows with `WARRANT_INIT_EXPORT` set; without it the Init store test is skipped.

| Item | Test |
|---|---|
| The M5a result through the server | `TheM5aExitCorpusVerifiesThroughTheServerWithM5aExpectedOutcomes`: the 33 members of the exit corpus get M5a's expected outcomes and diagnostics, read back from the server's `report`. |
| A second build is served from the cache without running tactics | `ASecondVerifyComesFromTheCacheWithNoTacticRuns`: every theorem and recursive method comes from the cache (10 entries for `accepted`, 2 for `refuted`), with the same diagnostics, and the server's tactic counter does not move. |
| `WarrantRecheck=true` re-checks cached certificates with the kernel alone | `ARecheckVerifyReportsEveryProvedUnitRecheckedWithNoTacticRuns`, and `ARecheckRejectsACachedProofSwappedForAnotherTheoremsWithWrt0010ForThatUnitOnly`: one cached proof replaced by another theorem's is WRT0010 for that unit and no other. |
| The Init + semantics store passes `check-store` in verified mode | `TheInitAndSemanticsStorePassesCheckStore`, opt-in with `WARRANT_INIT_EXPORT`; `TheBundleStorePassesCheckStore` runs always. |
| `cancel` aborts a running verify | `ServerCancelStopsALongDecideWithinASecondAndTheNextRequestSucceeds`. |
| A unit over its budget reports a timeout | `ATheoremADefinitionAndADecreaseProofEachOverABudgetReportWrt0006` (chapter 3 shows the messages). |
| No server is left running | `NoServerProcessRemainsOnItsEndpointOnceTheServerIsShutDown`. |
| Analyzer output is identical across runs | `Warrant.Analyzers.Tests`' `TwentyConcurrentRunsGiveByteIdenticalDiagnosticsAndTheAnalyzerNeverThrows` (chapter 6), in a project of its own because the CLI tests must not reference the analyzer; it is not in `--filter M5bExit`. |

The build integration tests (`WARRANT_BUILD_INTEGRATION=1`) build M5a's `Increment` sample through a server of its own with `dotnet build`, Visual Studio 2026's MSBuild and Visual Studio 2022's, and expect the same diagnostics from each.
`TrueTheoremsBuildGreenThenComeFromTheCacheAndRecheckWithTheKernel` builds a sample three times, expecting `(3 from cache)` and then `(3 from cache, 3 rechecked)` in the summary, and `DotnetCleanRemovesTheCacheAndTheNextBuildHasNoCachedResults` checks `dotnet clean`.

## Servers in tests

A server left running outlives the test run, and the plan feared it would hold files the tests delete: `PackedPackages` packs to a temporary folder and deletes it (KTD29).
The CLI starts the server from a per-user copy of its files (chapter 1), so a server never holds that folder, and the `dotnet build` integration test checks it by moving the package's `tools` folder after its server has shut down.
So:

- Unit tests host the server class inside the test process on a unique endpoint.
- Process tests start `warrant-server` with `WARRANT_SERVER_ENDPOINT` set to a unique name and always shut it down.
- Build integration tests set `WarrantUseServer=false`, except the samples that test the server, which shut it down at the end.

The suite's definition of done includes "no server process left running".

## Baselines for M8

M8 has no exit criterion yet; design §12 Q15 says its latency and memory budgets start from what M5b measures.
`scripts/measure-m5b.sh [MATHLIB_NDJSON]` measures them (KTD30).
For each M5a sample (`tests/corpus/m5a/accepted`, `refuted` and `rejected`: 20, 3 and 2 units) it runs `warrant verify <sample> --timings`, the CLI the build task runs, in each mode, and reads the CLI's `--timings` lines:

| Mode | What runs |
|---|---|
| cold | No server running: the CLI starts one. The "connect" column is starting the server, which loads and checks the bundle before it listens, and connecting, as one figure. |
| warm | The server running, an empty cache. |
| cache hit | The same cache again: lookups only. |
| recheck | The same cache with `--recheck`: the kernel checks every cached proof again. |
| in-process | `--server off` and no cache: M5a's path. The wall time includes loading and checking the bundle. |

"Wall" is the CLI process's wall time; "request" is the server's (or the in-process service's) time for the whole request; the per-unit columns are each unit's time from when a worker started it.
Server memory comes from `warrant server status`, after the server starts on an empty project and after the warm, cache-hit and recheck runs of every sample.
Given a Mathlib export, the script also imports it into a trusted store and runs `warrant sample-store` on it.
GC heap and working set are reported separately: pages of a mapped store count in the working set and are not managed memory, so the working set alone would make a store-backed process look like it leaks.

The run that design §11 records (*ran*, `MEASURE_DIR=D:/warrant-mathlib/measure bash scripts/measure-m5b.sh D:/warrant-mathlib/mathlib.ndjson` from Git Bash, with the CLI built in Release) was made on 2026-11-07 on a Windows 11 Pro workstation with 32 logical cores and 64 GB of memory, .NET SDK 10.0.403:

| Mode | Sample | Wall (ms) | Connect (ms) | Request (ms) | Units | Mean per unit (ms) | Max per unit (ms) |
|---|---|---:|---:|---:|---:|---:|---:|
| cold | accepted | 4879 | 2921.1 | 624.1 | 20 | 41.6 | 175.0 |
| cold | refuted | 4053 | 2730.2 | 256.1 | 3 | 53.5 | 112.5 |
| cold | rejected | 4116 | 2880.6 | 38.7 | 2 | 1.1 | 2.1 |
| warm | accepted | 2065 | 103.2 | 630.3 | 20 | 45.7 | 175.5 |
| cache hit | accepted | 1440 | 99.7 | 39.1 | 20 | 0.0 | 0.2 |
| recheck | accepted | 1711 | 105.9 | 239.3 | 20 | 11.1 | 49.7 |
| warm | refuted | 1211 | 103.2 | 51.8 | 3 | 12.2 | 23.0 |
| cache hit | refuted | 1159 | 98.2 | 1.7 | 3 | 0.0 | 0.0 |
| recheck | refuted | 1145 | 101.5 | 1.2 | 3 | 0.0 | 0.1 |
| warm | rejected | 1255 | 103.0 | 0.8 | 2 | 0.0 | 0.0 |
| cache hit | rejected | 1215 | 103.3 | 0.6 | 2 | 0.0 | 0.0 |
| recheck | rejected | 1184 | 96.6 | 0.7 | 2 | 0.0 | 0.0 |
| in-process | accepted | 4380 | - | 547.9 | 20 | 41.4 | 160.9 |
| in-process | refuted | 3621 | - | 155.1 | 3 | 42.1 | 103.8 |
| in-process | rejected | 3535 | - | 22.9 | 2 | 1.1 | 2.3 |

| Server memory | GC heap | Working set | Counters |
|---|---|---|---|
| after start (empty project) | 37.1 MB | 109.9 MB | 0 hits, 0 misses, 0 tactic runs, 0 rechecked |
| after the corpus (warm, cache hit and recheck of every sample) | 64.8 MB | 150.4 MB | 24 hits, 51 misses, 12 tactic runs, 10 rechecked |

| Mathlib store (mathlib.ndjson) | Time | Size or memory |
|---|---|---|
| import (trusted) | 138.7 s | store 1.45 GB |
| open, then 1,000 random lookups | open 69.3 ms, lookups 114.1 ms (1,004 records decoded) | GC heap 21.0 MB, working set 87.7 MB |

What the figures say:

- A cold build spends about 2.9 s starting the server, nearly all of it loading and checking the bundle; every later build connects in about 0.1 s.
- On the accepted sample the server's request takes 630 ms warm, 39 ms from the cache and 239 ms with recheck: recheck is kernel time only, under two fifths of finding the proofs.
  On the refuted sample recheck costs no more than a cache hit, because a not-proved outcome has no proof to re-check.
- Every run still pays 1.1 to 1.4 s of CLI wall time for the .NET start, the compilation and extraction; the server takes the bundle's load (about 3 s) out of each build, not the compile.
- The in-process path does a warm server's work in about the same time, after loading the bundle itself.
- The server holds a 37 MB managed heap after start and 65 MB after the corpus.
- The trusted Mathlib import of 712,205 declarations (729,263 constants) took 138.7 s, and its store opens in 69 ms; 1,000 random lookups leave a 21 MB managed heap and an 88 MB working set, against the 12.6 GB peak of holding all of Mathlib in memory ([Checking Mathlib](../mathlib.md)).
