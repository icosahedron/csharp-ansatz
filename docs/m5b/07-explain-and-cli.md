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
The M5a refuted sample (abridged where omega's constraints are):

```text
explaining Corpus.Refuted.Increments.AlwaysLarger(int)  tests/corpus/m5a/refuted/Increment.cs(12,18)

[1] Tactic.Unfold(nameof(Increment))   tests/corpus/m5a/refuted/Increment.cs(14,18)
  before:
    x : Int32
    ⊢ Increment x > x
  after:
    x : Int32
    ⊢ x + 1 > x
[2] Tactic.Omega()   tests/corpus/m5a/refuted/Increment.cs(14,52)
  before:
    x : Int32
    ⊢ x + 1 > x
  failed:
    omega could not prove the goal:
    a possible counterexample may satisfy the constraints
      …

  Corpus.Refuted.Increments.Increment(int)     translated
  Corpus.Refuted.Increments.AlwaysLarger(int)  unproved
tests/corpus/m5a/refuted/Increment.cs(14,52): error WRT0001: Theorem 'Increments.AlwaysLarger(int)' could not be proved: omega could not prove the goal. Counterexample: x = 2147483647.
  …
Warrant: 2 verified units, 0 theorems proved, 1 not proved.
```

A step inside `AllGoals` or `Try` is numbered under it (`[3.1]`, `[3.2]`), and a failure inside `Try` is shown and the script goes on.

## `export` and `report`

`export(request)` verifies a request and returns, with the response, a certificate file Lean's kernel can check on its own: the bundle, then every declaration the run admitted, as lean4export NDJSON, gzip-compressed for the wire (about 1.5 MB instead of 10) (KTD25).
It verifies without the cache, because a cached unit admits nothing it could export; the plan's reading of certificates from cache entries is left for when a run needs it.
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
These verbs find the server for the installed toolchain, as a build does (chapter 1).
`status` with no server running says so and exits 0 (illustrative):

```text
warrant-server 41528 on \\.\pipe\warrant-Qm9Cx2vT8yPLa0ZkNw3eRf
toolchain 9c41e0d2…  up 00:12:41  bundle warrant-semantics sha256:51b2c9e0a4f1
memory: GC heap 412 MB, working set 655 MB
cache: 4,096 in memory; 1,284 hits, 37 misses, 37 tactic runs
active: 1 request
  b3c1…  D:\src\Payments  6 units, 2 running, started 00:00:04 ago
```

`cancel` exists for the exit criterion and for a stuck request; builds cancel by disconnecting (chapter 1).

## `warrant import` and `warrant check-store`

Chapter 5 covers the store; the verbs are listed here with the others:

```text
warrant import <file.ndjson[.gz]>... --store <dir> [--verified] [--fuel N]
warrant check-store <dir> [--fuel N] [--quiet]
```

Both are offline: they do not use the server.
`check-store` exits 0 when every declaration is accepted and 1 otherwise, as `warrant check` does.
