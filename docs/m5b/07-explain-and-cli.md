# 7. `explain`, `export`, `report` and the CLI verbs

> Part of the [M5b design](README.md). Decisions: KTD24 to KTD26, KTD20.

## `warrant explain`

A failed proof in M5a shows the goal where the script stopped.
That is often enough, and sometimes it is not: a `simp` that rewrote the goal into something `omega` cannot use looks like an `omega` failure.
`explain` shows every step (KTD24).

```text
warrant explain <unit> [--project-dir <dir>] [--csc-args <file>] [--sources <dir>] [--server auto|off]
```

It finds the build's most recent `warrant.csc.args` under the project's `obj/` (or takes one, or compiles a `--sources` directory as `verify <directory>` does), compiles and extracts as the build does, and picks the unit by the name the diagnostic printed (`Increments.AlwaysLarger(int)`), by any dotted end of its display name with or without the parameters (`AlwaysLarger`), or by its documentation-comment ID (`M:Increments.AlwaysLarger(System.Int32)`), trying those in turn.
An unknown name lists the units it found, and an ambiguous one lists the units it could mean.
It then verifies that one unit and its closure with a trace recorder, through the server or in-process, and never reads or writes the cache, because an explanation must come from running the tactics.

Before M5b, `TacticRunner` remembered only the tactic that failed.
The recorder (`TacticRecorder`, `TacticStep`) is untrusted, like the rest of the tactic layer, and records for each tactic its name, its node ID (mapped to a line by the client, as in chapter 2), its depth inside `AllGoals` and `Try`, and the goals before and after it or why it failed, printed as M5a prints goals.
The client prints each tactic as its source reads, then the unit's outcome as `verify` reports it, so the counterexample appears once, in the diagnostic.
The M5a refuted sample, copied to a working directory and explained through the server (*ran*; the diagnostic's constraints and goal, which repeat step 2's, are abridged):

```text
$ warrant explain AlwaysLarger --sources m5a/refuted --server auto
verifying 2 file(s) in m5a/refuted
explaining Corpus.Refuted.Increments.AlwaysLarger(int)  m5a/refuted/Increment.cs(12,18)

[1] Tactic.Unfold(nameof(Increment))   m5a/refuted/Increment.cs(14,18)
  before:
    x : Int32
    ⊢ Increment x > x
  after:
    x : Int32
    ⊢ x + 1 > x
[2] Tactic.Omega()   m5a/refuted/Increment.cs(14,52)
  before:
    x : Int32
    ⊢ x + 1 > x
  failed:
    omega could not prove the goal:
    a possible counterexample may satisfy the constraints
      b ≥ 0
      -2147483648 ≤ a ≤ -1
      -6442450943 ≤ a + 4294967296*b ≤ -2147483648
    where
     a := if (x.toInt + ↑1) % ↑(2 ^ 32) < (↑(2 ^ 32) + 1) / 2 then (x.toInt + ↑1) % ↑(2 ^ 32) else (x.toInt + ↑1) % ↑(2 ^ 32) - ↑(2 ^ 32)
     b := (x.toInt + ↑1) / 4294967296

  Corpus.Refuted.Increments.Increment(int)     translated
  Corpus.Refuted.Increments.AlwaysLarger(int)  unproved
m5a/refuted/Increment.cs(14,52): error WRT0001: Theorem 'Increments.AlwaysLarger(int)' could not be proved: omega could not prove the goal. Counterexample: x = 2147483647.
  …
Warrant: 2 verified units, 0 theorems proved, 1 not proved. [server]
```

Only `AlwaysLarger` and the unit it needs are verified, so the sample's other unit, `Bad`, does not appear.
`explain` verifies in-process unless `--server auto` is given, and exits 0 when the unit verified, 1 when it did not, and 2 for bad arguments or an unknown unit.

A step inside `AllGoals` or `Try` is numbered under it (`[3.1]`, `[3.2]`), and a failure inside `Try` is shown and the script goes on.

## `export` and `report`

`export(request)` verifies a request and returns, with the response, a certificate file Lean's kernel can check on its own: the bundle, then every declaration the run admitted, as lean4export NDJSON, gzip-compressed for the wire (about 1.5 MB instead of 10) (KTD25).
It verifies without the cache, because a cached unit admits nothing it could export; KTD25's reading of certificates from cache entries was not built, since nothing needs it.
`warrant verify --out` uses it on either path and writes the same bytes it wrote in M5a, so `scripts/cross-check.sh` is unchanged, and `--out` no longer forces an in-process run.

`report(project)` returns the JSON assumption report of the project's last verify, which the server keeps per project directory; `warrant server report <project dir>` prints it.
The report quotes each theorem's claim, which is source text, so the client sends the claims, the overflow setting and the bundle's name with every request (`VerifyRequest.Report`).
Both ends build the report from the response's wire outcomes with the same code, so the server's copy is the `report.json` the client writes, and `verify --report` works through the server too.

## `warrant server`

```text
warrant server status
warrant server cancel <request-id>
warrant server shutdown
warrant server report <project-dir>
```

`dotnet build-server shutdown` cannot stop a third-party server: the SDK lists MSBuild, the compiler server and Razor and has no way to add another (KTD26).
These verbs find the server for the installed toolchain, as a build does (chapter 1), and none of them starts one.
With no server running, each says so; `status` and `shutdown` then exit 0, and `cancel` and `report` exit 1.
`status` after verifying the M5a accepted sample three times (cold, from the cache, and with `--recheck`) on an endpoint of its own (*ran*):

```text
process      290688
endpoint     warrant-u18-39954
toolchain    8a1f35d26e995f989e9c6bb80268c08a2f08ba7a7ef94f76949888b9adaec069
uptime       0.00:00:06
bundle       cc74b3a23fc7588b48eefb5f24c72d3d2960258244ee2b28e2a607c50fb58777
GC heap      70.8 MB
working set  148.9 MB
cache        20 hits, 40 misses, 10 tactic runs, 10 rechecked
requests     none active
```

The counters add up every request the server answered.
A unit counts as a miss whenever its outcome did not come from the cache, so the ten units that are never cached (non-recursive definitions, records and enums) are misses in every request, and the second and third requests' ten hits are the seven theorems and three recursive methods.
A running request is listed with its id, its unit count, its age and its project directory.
On Windows the endpoint is the pipe's name; elsewhere it is the socket's path.

`cancel` exists for the exit criterion and for a stuck request; builds cancel by disconnecting (chapter 1).

## `warrant import`, `warrant check-store` and `warrant sample-store`

Chapter 5 covers the store; the verbs are listed here with the others:

```text
warrant import <file.ndjson[.gz]>... --store <dir> [--verified] [--fuel N]
warrant check-store <dir> [--fuel N] [--quiet]
warrant sample-store <dir> [--count N] [--seed N]
```

All three are offline: they do not use the server.
`check-store` exits 0 when every declaration is accepted, 1 when one is rejected and 2 when one is declined, as `warrant check` does.
`sample-store` measures a store (chapter 8): it opens the current version as the kernel's lazy base, looks up N distinct constants chosen at random by name (1,000 and seed 1 by default), and prints the time each step took, the managed heap after a full collection and the working set.
On the Mathlib store (*ran*, from `scripts/measure-m5b.sh`):

```text
opened store D:\warrant-mathlib\measure\mathlib-store (v1-cc3d1e2673d6, 729,263 constants) in 69.3 ms
looked up 1,000 random constants (seed 1) in 114.1 ms, decoding 1,004 records
GC heap 21.0 MB, working set 87.7 MB
```

## `warrant verify --timings`

`--timings` prints, after the summary, how long reaching the server took, the request's time on the server or in-process, and each unit's time from when a worker started it, with where its result came from (`server`, `in-process`, `cache` or `rechecked`).
`scripts/measure-m5b.sh` reads these lines.
The accepted sample's second verify through a running server (*ran*, abridged):

```text
Warrant: 20 verified units, 7 theorems proved (10 from cache), 0 not proved. [server]
timings (server): connected to the running server in 112.9 ms
timings (server): 42.8 ms for the request
         0.1 ms  server      Corpus.Clamps.Clamp(int)
         0.0 ms  cache       Corpus.Clamps.AtMostOneHundred(int)
         …
         0.0 ms  cache       Corpus.Quantifiers.RankIsSmall(Corpus.Light)
```

A first verify, which starts the server, says `started the server and connected in …` instead; that time includes loading and checking the bundle, because the server does so before it listens.
