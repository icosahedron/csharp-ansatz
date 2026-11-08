# 1. The semantics library

> Part of the [M4 design](README.md). Decisions: KTD1, KTD2 in the [plan](../plans/2026-11-02-1245-feat-m4-pure-subset-plan.md).

The semantics library says which Lean definitions model C# (design D10).
For M4's types the answer turned out to be Lean's own: C# `int`, `long` and `bool` are Init's `Int32`, `Int64` and `Bool`, unchanged (KTD1).
So the M4 library adds no new types or operations.
Its job in M4 is to fix the exact set of Init constants the translator may emit, to record the CLR facts those constants must satisfy as Lean theorems, and to produce the bundle the tests load.

## Why Init's types, and not new ones

Design D7 requires `int` to wrap around the way the CLR does in unchecked code.
Init's `Int32` already does: it is a structure over `UInt32`, which is a structure over `BitVec 32`, and every arithmetic operation is defined on `BitVec` and wraps modulo 2³².
Each claim in this table was checked against Lean 4.35.0 by evaluating it and by proving it with `decide`:

| C# (unchecked) | Lean 4.35.0 | Same as the CLR? |
|---|---|---|
| `int.MaxValue + 1` | `-2147483648` | yes |
| `int.MinValue - 1` | `2147483647` | yes |
| `int.MinValue * -1`, `-int.MinValue` | `-2147483648` | yes |
| `-1 < 1` (signed comparison) | `true` | yes |
| `long.MaxValue + 1` | `-9223372036854775808` | yes |
| `(int)3000000000L` | `-1294967296` | yes |
| `1 << 33`, `-8 >> 33` | `2`, `-4` (count masked to 5 bits) | yes, but M4 rejects shifts |
| `-7 / 2`, `-7 % 2` | `-3`, `-1` | yes, but M4 rejects `/` and `%` |
| `int.MinValue / -1` | `-2147483648` | **no**: the CLR throws `OverflowException` |
| `x / 0`, `x % 0` | `0`, `x` | **no**: the CLR throws `DivideByZeroException` |
| `x >>> n` on `int` | arithmetic shift | **no**: C#'s `>>>` is a logical shift |

The first rows are what M4 needs, and they hold.
The last three rows are why M4 rejects `/`, `%` and shifts (KTD15): modelling them faithfully needs exceptions (M6) or a definition Init does not have.
Defining a fresh `Warrant.Int32` would have meant re-proving everything Init already proves about `Int32` (about 340 `Int32.*` theorems in `Init.Data.SInt.Lemmas` and 445 across Init, including the `toInt` bridges M5a's `omega` preparation will need), for no gain in faithfulness.

One more trap applies to literals: Lean's `OfNat` instance for `Int32` wraps out-of-range numbers silently, so `(4294967295 : Int32)` is `-1`.
The translator therefore takes every literal from Roslyn's typed constant value and range-checks it itself (chapter 5); it never relies on Lean to reject a literal.

## What the library contains

```text
lean/
├── lean-toolchain            leanprover/lean4:v4.35.0, the repository pin
├── lakefile.toml             package warrant-semantics, library Warrant, no dependencies
├── Warrant.lean              imports every module below
├── Warrant/Clr/Int32.lean    CLR facts about int, as theorems
├── Warrant/Clr/Int64.lean    CLR facts about long, as theorems
├── Warrant/Clr/Bool.lean     CLR facts about bool, as theorems
└── bundle-roots.txt          every constant the translator may emit, one per line
```

The library has no `require` lines: it imports only Init, implicitly.
It needs neither Std nor Mathlib in M4.

### CLR facts as theorems

Each fact the translator relies on is written down once, in Lean, and proved there.
The kernel re-checks the proofs when it loads the bundle, so a Lean upgrade that changed `Int32`'s behaviour would fail in Warrant's own test run, not silently.
Part of `Warrant/Clr/Int32.lean` (the file also proves `int.MinValue * -1` and `-1 < 1`):

```lean
namespace Warrant.Clr.Int32

/-- `int.MaxValue + 1 == int.MinValue`. -/
theorem maxValue_add_one : Int32.maxValue + 1 = Int32.minValue := by decide

/-- `int.MinValue - 1 == int.MaxValue`. -/
theorem minValue_sub_one : Int32.minValue - 1 = Int32.maxValue := by decide

/-- `-int.MinValue == int.MinValue`. -/
theorem neg_minValue : -Int32.minValue = Int32.minValue := by decide

/-- `(int)(long)x == x`: widening then narrowing is the identity. -/
theorem toInt64_toInt32 (x : Int32) : x.toInt64.toInt32 = x := Int32.toInt32_toInt64 x

end Warrant.Clr.Int32
```

The last theorem is quantified, so `decide` cannot prove it; Init already proves it as `Int32.toInt32_toInt64`, and the library restates it in C#'s terms.
Quantified proofs from Init can rest on Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`); this one does.
That is fine for documentation theorems, and it does not leak into translated code: the proof terms the engine emits for C# theorems use no axioms (chapter 6).
No library declaration may depend on `sorryAx`, and the export script checks that (plan, U2).
Loading checks the axioms again, because `--bundle` accepts any file: a bundle that declares any other axiom is rejected, and so is one whose `propext`, `Classical.choice` or `Quot.sound`, or the `Eq`, `Iff` or `Nonempty` their statements mention, differs from Lean 4.35.0's (`src/Warrant.Engine/StandardAxioms.ndjson`, taken from the committed bundle).
The assumption report lists the three axioms as a global assumption.

These theorems are documentation that a machine checks.
They are not what makes the model faithful.
That job belongs to the CLR-agreement tests, which run the same operations on the CLR and in the kernel and compare (chapter 7).

### The bundle roots

`bundle-roots.txt` lists every constant the translator or the engine may put into a term: the types (`Int32`, `Int64`, `Bool`, `Nat`), the operators and their instances (`HAdd.hAdd`, `instAddInt32`, …), the decision procedures (`Int32.decLt`, `instDecidableEqInt32`, `Nat.beq`, …), the logic (`Eq`, `ite`, `of_decide_eq_true`, …), the constants read-back reduces (`BitVec.toNat`, `Int32.toBitVec`, …), and every `Warrant.*` theorem.
The committed file has 74 roots.
Chapter 5's operator table is the source of truth for the Init names; a test checks that each name the translator can emit appears in this file and in the bundle (chapter 7).

## The bundle

`scripts/export-semantics.sh` builds the library with `lake build`, then runs lean4export (pinned to `5a9a355`) from inside `lean/`, passing the roots after `--`.
lean4export then writes those declarations **and their whole dependency closure**, including the parts of Init they use, in dependency order.
That is what the tests and Lean's `lean-replay` both need: a file that loads into an empty environment.

```text
LEAN_ABORT_ON_PANIC=1 lake env <lean4export> Warrant -- $(cat bundle-roots.txt) > warrant-semantics.ndjson
```

Two details of lean4export matter here, and both were found by testing it:

- A root that does not exist does not fail the export.
  lean4export prints `PANIC … Constant … not found` on stderr, exits 0 and writes the other roots.
  The script therefore sets `LEAN_ABORT_ON_PANIC=1`, which makes the panic exit non-zero, and also fails on any `PANIC` in stderr (KTD2).
- Roots are parsed as Lean name literals, so a name with a character that is not valid in an identifier must be quoted with `«»`.
  No M4 root needs that; Warrant's own `$` names are never roots, because they are generated per translation, not shipped.

The research run of this exact pattern, over 315 test theorems about `Int32`, `Int64`, structures and enums, produced 2,362 constants that Warrant's kernel checked in about 1.5 seconds.
The committed bundle has 2,483 constants in 2,258 declaration records.
The full-module alternative, exporting `Warrant` without `--`, drags in all of Init: about 6.46 million lines, which is too large to commit.

The output is committed gzipped as `tests/data/warrant-semantics.ndjson.gz`, with its provenance (Lean version, lean4export commit, root count) in `tests/data/README.md` and its record counts checked by `scripts/count-export.py`, like the existing corpus files.
It replaces `init-medium` for every M4 test: init-medium is a Lean 4.33.1 subset without `Int32` or `Int64`, and loading both would clash on constant names.

The script must be deterministic.
lean4export's output is byte-identical across runs, and the gzip step omits timestamps, so regenerating the bundle without changing the library gives the same file.
The test that loads the bundle also compares the root list in `bundle-roots.txt` with the constants the translator can emit, so a forgotten re-export shows up as a failing test even where no Lean toolchain is installed.

## What is trusted

The library's trusted part is its *definitions*: the claim that these Lean constants model C#.
In M4 every such definition is Init's (`Int32.add`, `Int32.decLt`, …), so the claim being trusted is "Init's `Int32` is C#'s `int` in unchecked code".
The `Warrant.Clr` theorems are proved, not trusted.
Chapter 7's CLR-agreement tests are the mitigation for the trusted part, as design §9 requires.
