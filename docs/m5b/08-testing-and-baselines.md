# 8. Testing and baselines

> Part of the [M5b design](README.md). Decisions: KTD28 to KTD30.

## Parity

The server and the in-process fallback run the same `VerificationService` (chapter 1), so their output should be identical.
A test makes sure (KTD28): it runs the M5a exit corpus and the CLI fixtures through a server and in-process, ten times each, and compares the `--format msbuild` output byte for byte.
Outcomes decided by a wall-clock limit are excluded, because they depend on the machine's load, which is also why they are never cached (chapter 4).
So are the parts of the output that report where results came from: the summary's cached count and `[server|in-process]` tag, and the message a fallback logs.

## The exit criterion as tests

Each item of design §11's M5b row is its own test in `M5bExitTests`, run against a server on a unique endpoint, so a failure names the item:

| Item | Test |
|---|---|
| The M5a result through the server | The exit corpus verifies through the server with M5a's expected outcomes. |
| A second build is served from the cache without running tactics | A second verify reports every unit from the cache; the server's tactic counter does not move. |
| `WarrantRecheck=true` re-checks cached certificates with the kernel alone | A recheck verify reports every proved unit as rechecked with zero tactic runs; with one cached proof swapped for another theorem's, it reports WRT0010 for that unit. |
| The Init + semantics store passes `check-store` in verified mode | Opt-in with `WARRANT_INIT_EXPORT`; the bundle-only store runs always. |
| `cancel` aborts a running verify | `warrant server cancel` stops a request running a long `decide` within a second, and the next request succeeds. |
| A unit over its budget reports a timeout | A theorem, a definition and a decrease proof each exceed a small budget and report WRT0006. |
| Analyzer output is identical across runs | 20 concurrent runs, byte-identical sorted output (chapter 6). |

The build integration matrix from M5a (`dotnet build`, Visual Studio 2026's and 2022's MSBuild) gains a second build that must come from the cache, a recheck build, and `dotnet clean` removing the cache.

## Servers in tests

A server left running would hold files the tests want to delete: `PackedPackages` packs to a temporary folder and deletes it, and a server started from that folder keeps its assemblies open (KTD29).
So:

- Unit tests host the server class inside the test process on a unique endpoint.
- Process tests start `warrant-server` with `WARRANT_SERVER_ENDPOINT` set to a unique name and always shut it down.
- Build integration tests set `WarrantUseServer=false`, except the samples that test the server, which shut it down at the end.

The suite's definition of done includes "no server process left running".

## Baselines for M8

M8 has no exit criterion yet; design §12 Q15 says its latency and memory budgets start from what M5b measures.
`scripts/measure-m5b.sh` builds the M5a samples in each mode and records (KTD30):

| Measure | How |
|---|---|
| First build, no server running (cold) | Wall time of `dotnet build`; server start, bundle load and connect timed separately from the CLI's `--timings`. |
| First build, server running (warm), empty cache | Per-unit server time from the response timings. |
| Second build (cache hit) | Per-unit time; should be lookup only. |
| Recheck build | Per-unit kernel time. |
| In-process (`WarrantUseServer=false`) | The M5a path, for comparison. |
| Server memory | GC heap and working set from `warrant server status`, after start and after the corpus. |
| Mathlib store | Import time and size; memory after opening it and looking up 1,000 random constants. |

GC heap and working set are reported separately: pages of a mapped store count in the working set and are not managed memory, so the working set alone would make a store-backed process look like it leaks.

The table goes here and into design §11's M5b row, with the machine and date, as the Mathlib run's figures did.
