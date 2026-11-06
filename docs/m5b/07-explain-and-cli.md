# 7. `explain`, `export`, `report` and the CLI verbs

> Part of the [M5b design](README.md). Decisions: KTD24 to KTD26, KTD20.

## `warrant explain`

A failed proof in M5a shows the goal where the script stopped.
That is often enough, and sometimes it is not: a `simp` that rewrote the goal into something `omega` cannot use looks like an `omega` failure.
`explain` shows every step (KTD24).

```text
warrant explain <unit> [--project-dir <dir>] [--csc-args <file>] [--server auto|off]
```

It finds the build's most recent `warrant.csc.args` under the project's `obj/` (or takes one), compiles and extracts as the build does, and picks the unit by the name the diagnostic printed (`Increments.AlwaysLarger(int)`) or by its documentation-comment ID (`M:Increments.AlwaysLarger(System.Int32)`).
An unknown name lists the units it found.
It then verifies that one unit and its closure with a trace recorder, through the server or in-process, and never reads or writes the cache, because an explanation must come from running the tactics.

No trace exists today: `TacticRunner` remembers only the tactic that failed.
The recorder is untrusted, like the rest of the tactic layer, and records for each tactic its name, its node ID (mapped to a line by the client, as in chapter 2) and the goals before and after it, printed as M5a prints goals (illustrative):

```text
Increments.AlwaysLarger(int)  Increments.cs(13,5)

[1] Unfold(nameof(Increment))   Increments.cs(15,12)
  before:
    x : Int32
    ⊢ Increments.Increment x > x
  after:
    x : Int32
    ⊢ x + 1 > x

[2] Omega()   Increments.cs(15,43)
  failed: omega could not prove the goal. Counterexample: x = 2147483647.
  a possible counterexample may satisfy the constraints
    …
```

## `export` and `report`

`export(units)` returns a certificate file Lean's kernel can check on its own: the bundle, then the certificates of the units' closures, then the units' own (KTD25).
`warrant verify --out` uses it, and writes the same declarations it wrote in M5a, so `scripts/cross-check.sh` is unchanged.

`report(project)` returns the JSON assumption report of the project's last verify, which the server keeps per project directory.
`verify --report` still renders both reports in the client, because the Markdown report quotes source text the server does not have.

## `warrant server`

```text
warrant server status
warrant server cancel <request-id>
warrant server shutdown
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
