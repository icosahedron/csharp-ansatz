# 5. Store v1

> Part of the [M5b design](README.md). Decisions: KTD17 to KTD20; Key Decision on lazy loading.

Warrant reads Lean libraries as lean4export NDJSON, and every load today parses the whole file and keeps every constant in memory.
For the 2,835-constant semantics bundle that takes about a second.
For all of Mathlib it takes 26 minutes and 12.6 GiB ([Checking Mathlib](../mathlib.md)).
Store v1 is the on-disk form that lets a process use a large library without loading it: constants are read by name the first time something asks for them.

## What M5b uses it for

In M5b the verification environment stays the shipped bundle, verified when the server starts (KTD19).
When a store does become a verification base, its record decoder decides what the kernel sees, so it becomes trusted code and joins the toolchain identity.
No C# that Warrant translates names a constant outside the bundle until M6 brings in Lean's Std, so moving verification onto the store now would change the trusted base (a trusted import instead of today's verified load) and gain nothing a user could see.
The store arrives with its verbs and its kernel seam, tested on Init and measured on Mathlib, ready for M6 and M8.

## Layout

```text
<store>/
  current                 one line: the active version directory
  .lock                   held by the one import writing the store
  v1-3f9a12c4be07/
    manifest.json
    names.idx             header; sorted (name key -> record offset, length, kind)
    decls.bin             header; one length-prefixed record per declaration
```

A version's name is `v1-` and twelve hex digits of the SHA-256 of its records' hashes and its manifest, so the same input imported twice makes the same version, byte for byte; importing it into a store that already holds it keeps the version readers may have open.

A store is never rewritten in place (KTD17).
Each `warrant import` writes a new version directory and then replaces `current`, a one-line file that is read once and never mapped, so replacing it is atomic.
This is forced by Windows, which refuses to overwrite or rename over a file another process has mapped.
Readers open the version `current` names and keep it until they are disposed; the next `import` deletes versions nobody holds.

`names.idx` is mapped read-only; `decls.bin` is read by offset, one record at a time, with positional reads that many threads can make at once.
Mapping the records as well would save a copy per record, but it would mean decoding through pointers, and the record decoder becomes trusted code when a store becomes a verification base (KTD19); positional reads keep it in safe, bounds-checked code, and a file truncated under a reader becomes an error rather than SIGBUS.
Both files are opened with `FileShare.Read | FileShare.Delete`, so an old version can be deleted while it is read.
On Unix, `import` deletes every other version as soon as `current` names the new one, and a reader holding an old one keeps reading it until it closes its files; on Windows a version whose files are open stays until a later `import` deletes it.
A reader that reads `current` just before an import deletes the version it names opens `current` again.

Every file starts with a magic number (`WRTD`, `WRTI`), a format version and its length, and a reader checks them before reading any record, so a truncated, foreign or newer file is rejected with a message naming it.
The manifest's `format` is checked the same way.

### Records

`decls.bin` holds one record per declaration.
A record is self-contained: it has its own small tables of names, levels and expressions, and its terms refer to those tables by index, the way lean4export's lines refer to earlier lines.
That keeps the sharing inside a declaration (a proof term's repeated subterms are stored once) without tying records together, so one record can be read without reading any other.
Identical records are stored once, keyed by their SHA-256.

The encoding is binary (`RecordCodec`): a record kind, then the names (each a string or number component on an earlier name), the levels and the expressions, each table entry referring only to earlier entries, then the declaration's constants with every field `ConstantInfo` has.
Decoding checks every index, enumeration value, boolean and length, and that the record ends where its last field does, so a damaged record is an error, never a different declaration.
Free variables and metavariables cannot be stored; no admitted declaration has one.

The index sorts names by a key of their components from the root (a tag byte, then the string's UTF-8 bytes or the number), compared as bytes, so a lookup is a binary search with no name parsing.

The cost is sharing across declarations: a subterm that a thousand Mathlib lemmas mention is stored, and materialized, once per lemma.
Chapter 8's baselines measure what that costs; it does not touch verification in M5b.

### The manifest

The manifest of the Init + semantics store (hashes shortened):

```json
{
  "format": 1,
  "lean": "4.35.0",
  "lean4export": "3.1.0",
  "sources": [
    { "file": "init.ndjson", "sha256": "f4c6…" },
    { "file": "warrant-semantics.ndjson.gz", "sha256": "cc74…" }
  ],
  "mode": "verified",
  "verifiedBy": "648c…",
  "quotientsInitialized": true,
  "declarations": 57944,
  "constants": 59374
}
```

The source hashes include the bundle file's, the value the attribute sidecar's header names, so a store holding the bundle keeps the sidecar's binding (design §7.3).
`verifiedBy` is the toolchain identity that checked a verified store; nothing trusts it automatically, and `check-store` re-checks regardless.

## The kernel's lazy base

The kernel reads constants only through `KernelEnvironment.Find`, `Get`, `CheckName` and `IsQuotInitialized`, and nothing in the kernel, Meta or the engine enumerates an environment.
So one fall-through in `Find` is enough to put a store underneath an environment (KTD18):

```csharp
// Shape only: Warrant.Kernel.
public interface IConstantSource
{
    bool TryGet(Name name, [NotNullWhen(true)] out ConstantInfo? constant);
    int Count { get; }
    bool QuotientsInitialized { get; }
}

// KernelEnvironment.Find: own constants, then parents, then the base source.
```

The store's adapter, in the new `Warrant.Store` project, materializes a record the first time its name is asked for, remembers it, and interns names so that the same `Name` object is shared across records.
Many threads may look up constants at once (chapter 3's workers), so the memo is thread-safe; the kernel itself never writes to the source, so a frozen environment is still frozen.

A source is a trusted import: the kernel believes what it returns, exactly as `ExportChecker(admitRejected: true)` does today.
Only a store creates one.

One input is not a lookup: the quotient flag.
When it is set, the kernel reduces quotient recursors, and `Quotient.Add` skips its checks because it believes the quotient constants are already there (`Kernel.cs`).
A store that claimed quotients were initialized while holding different `Quot` constants would widen what the kernel accepts.
So the flag is set only when the source claims it and holds the quotient constants exactly as `Quotient.ExpectedConstants` defines them (up to binder names, as an exported quotient constant is compared), whatever the manifest says (KTD18).
The kernel makes that check itself, in `KernelEnvironment`'s constructor, rather than taking it from the store's code.

This is a change to a trusted file, so it gets reject-only tests: a declaration whose dependency is missing from the store is still rejected, and an environment without a source behaves exactly as before.

## Importing and checking

```text
warrant import <file.ndjson[.gz]>... --store <dir> [--verified] [--fuel N]
warrant check-store <dir> [--fuel N] [--quiet]
```

`import` reads its files in order (KTD20) and writes a new version holding exactly those files: a store is a snapshot of the sources its manifest lists, not a library that grows.
A constant may appear again in a later file only if it is the same constant (up to binder names, as the kernel compares an exported constant with its own) and the store keeps the first; that is what lets the Init + semantics store be built from the full Init export followed by the bundle, whose Init closure repeats Init's constants and adds the `Warrant` library's.
Metadata counts: the bundle is exported with `--export-mdata`, so Init must be too, and `scripts/export-lean-library.sh` does that by default; an Init exported without it differs from the bundle's copy at `Nat.beq`, whose `@&` borrow annotations are metadata, and the import fails naming it.
All files of a store must come from one Lean version.
In verified mode each declaration goes through the kernel first, and the store keeps what the kernel admitted, including the constructors and recursors it generates itself, as `warrant export` does.
In trusted mode the declarations are stored as read.

`check-store` reads the records back in their stored order into a fresh environment, checks each with the kernel, and prints the same summary as `warrant check`:

```text
$ warrant import init.ndjson warrant-semantics.ndjson.gz --store init-semantics --verified
importing 2 file(s) into init-semantics (verified)
  init.ndjson: 57,919 declarations stored, 0 repeated
  warrant-semantics.ndjson.gz: 25 declarations stored, 2,574 repeated
wrote v1-e9a37ed70edb: 57,944 declarations, 59,374 constants in 147.2s
$ warrant check-store init-semantics --quiet
checking store /…/init-semantics (v1-e9a37ed70edb, Lean 4.35.0)
accepted 57,944, rejected 0, declined 0; 59,374 constants in 138.2s
```

The Init + semantics store passing `check-store` is M5b's exit criterion for the store, and it does.
Measured on Linux with a Debug build of the CLI: the import peaked at 0.96 GB and `check-store` at 1.4 GB (a fresh environment holds every constant it checks); the version is 80 MB (`decls.bin` 78.5 MB, `names.idx` 4.4 MB) against the export's 348 MB.
The full Init export is not committed, so that test is opt-in through `WARRANT_INIT_EXPORT` (`StoreCommandTests.AStoreOfInitAndTheBundlePassesCheckStore`), as M3's full-Init test is; the default run builds and checks a store of the bundle alone.
