# lean-replay

Checks a lean4export NDJSON file (format 3.1.0) with **Lean's own kernel**.

It parses the file with lean4export's parser (pinned to commit `15f6055`, the last
one built for Lean v4.33) and replays every constant into an empty environment
with `Lean.Environment.replay`, the routine lean4checker uses. Replay sends each
declaration to the official kernel. For inductive types it admits only the
types and constructors, then requires every constructor and recursor in the file
to be `==` to the ones Lean generates, so it checks LeanSharp's recursor
generation directly.

It's used by [`scripts/cross-check.sh`](../../scripts/cross-check.sh), which
compares LeanSharp's verdicts with Lean's and has Lean re-check everything
LeanSharp admits.

## Build and run

You need the Lean 4.33.1 toolchain on `PATH`. `scripts/lib/lean-toolchain.sh`
downloads it.

```sh
lake build
.lake/build/bin/lean-replay FILE.ndjson     # exit 0 accepted, 1 rejected, 2 unreadable
```

## Limitations (from `Environment.replay`)

- Unsafe and partial constants are skipped, so a safe declaration that uses one
  fails with "unknown constant".
- The first failure stops the run, so verdicts are per file, not per declaration.
- Quotient constants in the file are not compared with the generated ones
  (LeanSharp's own checker does compare them).
- Only format 3.1.0 is read. Convert older files with
  `leansharp export OLD.ndjson NEW.ndjson`.
