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
  v1-3f9a12c4be07/
    manifest.json
    names.idx             header; sorted (name -> record offset, length, kind)
    decls.bin             header; one record per declaration
```

A store is never rewritten in place (KTD17).
Each `warrant import` writes a new version directory and then replaces `current`, a one-line file that is read once and never mapped, so replacing it is atomic.
This is forced by Windows, which refuses to overwrite or rename over a file another process has mapped.
Readers open the version `current` names and keep it until they are disposed; the next `import` deletes versions nobody holds.

Files are mapped read-only, opened with `FileShare.Read | FileShare.Delete` so an old version can be deleted while it is still mapped (the space is freed when the last reader closes it).
Every file starts with a magic number, a format version and its length, and a reader checks them before reading any record, because reading a truncated mapped file on Unix raises SIGBUS instead of an exception.

### Records

`decls.bin` holds one record per declaration.
A record is self-contained: it has its own small tables of names, levels and expressions, and its terms refer to those tables by index, the way lean4export's lines refer to earlier lines.
That keeps the sharing inside a declaration (a proof term's repeated subterms are stored once) without tying records together, so one record can be read without reading any other.
Identical records are stored once, keyed by their SHA-256.

The cost is sharing across declarations: a subterm that a thousand Mathlib lemmas mention is stored, and materialized, once per lemma.
Chapter 8's baselines measure what that costs; it does not touch verification in M5b.

### The manifest

An illustrative manifest for the Init + semantics store:

```json
{
  "format": 1,
  "lean": "4.35.0",
  "lean4export": "3.1.0",
  "sources": [
    { "file": "init.ndjson", "sha256": "…" },
    { "file": "warrant-semantics.ndjson.gz", "sha256": "51b2…" }
  ],
  "mode": "verified",
  "verifiedBy": "9c41…",
  "quotientsInitialized": true,
  "declarations": 60212,
  "constants": 61690
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
So the reader sets the flag only when the store holds the quotient constants exactly as `Quotient.ExpectedConstants` defines them, whatever the manifest says (KTD18).

This is a change to a trusted file, so it gets reject-only tests: a declaration whose dependency is missing from the store is still rejected, and an environment without a source behaves exactly as before.

## Importing and checking

```text
warrant import <file.ndjson[.gz]>... --store <dir> [--verified] [--fuel N]
warrant check-store <dir> [--fuel N] [--quiet]
```

`import` reads its files in order (KTD20).
A constant may appear again in a later file only if it is identical; that is what lets the Init + semantics store be built from the full Init export followed by the bundle, whose Init closure repeats Init's constants and adds the `Warrant` library's.
In verified mode each declaration goes through the kernel first, and the store keeps what the kernel admitted, including the constructors and recursors it generates itself, as `warrant export` does.
In trusted mode the declarations are stored as read.

`check-store` reads the records back in their stored order into a fresh environment, checks each with the kernel, and prints the same summary as `warrant check`:

```text
checking store D:\stores\init-semantics (v1-3f9a12c4be07, Lean 4.35.0)
accepted 60,212, rejected 0, declined 0; 61,690 constants in 52.3s
```

(Illustrative; the Init figures from the Mathlib run suggest about 50 seconds.)

The Init + semantics store passing `check-store` is M5b's exit criterion for the store.
The full Init export is 346 MB and not committed, so that test is opt-in through `WARRANT_INIT_EXPORT`, as M3's full-Init test is; CI runs the same test on a store of the bundle alone.
