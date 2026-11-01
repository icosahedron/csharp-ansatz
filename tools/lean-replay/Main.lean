/-
lean-replay: check a lean4export NDJSON file (format 3.1.0) with Lean's own kernel.

The file is parsed with lean4export's parser and every constant is replayed into an empty
environment with `Lean.Environment.replay`, which sends each declaration to the official kernel,
re-derives inductive types' constructors and recursors and compares them with the file's.
Unsafe and partial constants are skipped (as `replay` does), so safe declarations that use them
fail with an unknown constant.

Exit codes follow the Lean Kernel Arena convention: 0 accepted, 1 rejected, 2 unreadable.
-/
import Export.Parse
import Lean.Replay

open Lean

def main (args : List String) : IO UInt32 := do
  let [path] := args
    | IO.eprintln "usage: lean-replay FILE.ndjson"; return 2
  let exported ← try
      let h ← IO.FS.Handle.mk path .read
      Export.parseStream (IO.FS.Stream.ofHandle h)
    catch e =>
      IO.eprintln s!"declined: {e}"; return 2
  let env ← mkEmptyEnvironment
  try
    let _ ← env.replay exported.constMap
    IO.println s!"accepted: {exported.constMap.size} constants"
    return 0
  catch e =>
    IO.println s!"rejected: {e}"
    return 1
