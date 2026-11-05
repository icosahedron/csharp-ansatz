# 4. VIR

> Part of the [M4 design](README.md). Decisions: KTD5, KTD21 in the [plan](../plans/2026-11-02-1245-feat-m4-pure-subset-plan.md).

VIR is the verification IR between extraction and translation (design §4.1).
It is shaped like C#, with every implicit thing made explicit: types are resolved, conversions are nodes, overflow behaviour is a field, and calls say what they call.
From M5b on it is the wire format between the build task and the server, and its hash keys the server's cache (design §8.2), so M4 fixes its shape, its encoding and its hashes now.

It lives in `src/Warrant.Vir`, with no Roslyn dependency: the server only ever sees VIR (design §3.2).

## How VIR grows

VIR contains only the nodes M4 needs (KTD5).
Later milestones add node kinds and fields; they never change the encoding of a node kind that already exists.
Every unit records the VIR schema version it was written with, and the version is part of the hash, so a unit written by a newer extractor never collides with one written by an older one.

This is enough to keep old hashes valid, because a new node kind cannot change the bytes of a unit that does not use it.
Declaring the later milestones' nodes now would not help with that, and it would freeze shapes the design has not settled: the heap model (design §12 Q6) and region syntax (Q4) are both open until M7.
The additions already known are:

- **M5a:** binders and quantifiers, for `Spec.ForAll`, `Spec.Exists` and theorems with parameters; proof hints, for `.By(...)`; `decreases`.
  M5a added them as schema version 2 (docs/m5a/01): `forall` and `exists` expressions, a `decreases` statement, and a theorem's `params`, `script` and `budget`. A unit that uses none of them encodes as below apart from its `vir` field.
- **M6:** contracts, `throw`, `null`, `await` and calls to externals.
- **M7:** loops, heap reads and writes, object creation and regions.

## Units

A unit is a member, a theorem or a type (KTD21).

| Field | Meaning |
|---|---|
| `vir` | The schema version. `1` in M4; M5a writes `2` (docs/m5a/01). |
| `key` | The documentation-comment ID, e.g. `M:Payouts.PayoutRules.Payout(System.Int32,System.Int32,System.Int32)` or `T:Payouts.Payment`. |
| `kind` | `function` (a `[Verified]` method or property), `theorem`, or `type`. |
| `self` | For an instance member of a record, the record's type key. |
| `params` | Name and type of each parameter. Theorems have none in M4. |
| `returns` | Return type. |
| `body` | A block of statements, or a single expression for an expression-bodied member. |
| `statement` | For a theorem, the claim as an expression. |
| `definition` | For a type unit, the type: a record's fields, an enum's members, a closed type's members. |
| `assumptions` | Chapter 3's list. |
| `facts` | What changes the meaning of the unit beyond its text: `overflow` (`wrap` or `checked`), the language version, the extractor version and the Roslyn version. |
| `deps` | The keys of the units this one calls or whose types it mentions, sorted. |

Types are units because a record or an enum is used by many members and must be translated once, from one place.
In the unit that uses it, a type is a reference by key.

## Types

| Type | Notes |
|---|---|
| `bool` | |
| `int32`, `int64` | Other widths and unsigned types are added when a milestone needs them. |
| `ref{key}` | A record, open enum or closed type, by its type unit's key. |

A type unit's `definition` is one of:

- `record{fields}`: name and type of each field, in primary-constructor order;
- `enum{underlying, members}`: name and value of each member, for an open enum;
- `closed{members}`: the members in declaration order, for a `[Closed]` enum (name and value) or a `[Closed]` class (name).

## Expressions

Every expression node has a type and a node ID.

| Node | Notes |
|---|---|
| `lit{type, value}` | The value as a decimal string, so 64-bit values survive any JSON reader. |
| `param{index}`, `local{id}`, `self` | |
| `unary{op, overflow}`, `binary{op, overflow}` | `op` is `neg`, `plus`, `add`, `sub`, `mul`; `overflow` is always `wrap` in M4, but it is a field, so M6 can add `checked` without a new node. |
| `logical{op}` | `and`/`or`, short-circuit, and `and-eager`/`or-eager`/`xor` for `&`, `\|`, `^` on `bool`. Kept as nodes rather than lowered to `if`, so that M6 can treat a right-hand side that throws. |
| `not` | |
| `compare{op, kind}` | `kind` is `int`, `enum`, `bool`, `record` or `closed`, so translation never re-derives what `==` means. |
| `convert{from, to, overflow}` | Roslyn's implicit conversions become these nodes too. |
| `cond{c, then, else}` | |
| `call{target, args}` | `target` is a unit key. |
| `new{type, args}`, `get{type, field}`, `with{base, updates}` | Records only. |
| `member{type, name}` | An enum member or a closed-class instance. |
| `switch{scrutinee, arms}` | Each arm is a pattern and a value. |
| `implies{a, b}` | Theorem statements only. |

Patterns are `const`, `discard`, `relational{op, value}`, `and`, `or` and `not`.

## Statements

| Node | Notes |
|---|---|
| `decl{local, name, init}` | |
| `assign{local, value}` | Extraction lowers compound assignment and `++`/`--` to this. |
| `if{c, then, else?}` | |
| `switch{scrutinee, sections}` | Each section has its `labels` (patterns, with `discard` for `default`) and a `body`. Extraction drops a section's final `break`, so a body that does not end in `return` continues after the `switch`; C# forbids falling into the next section. |
| `return{value}` | |
| `block{stmts}` | |

Locals are identified by an ID, not versioned.
A local can be assigned more than once; giving each assignment its own binder is the translator's job (chapter 5), because it falls out of the continuation-passing translation for free and VIR then stays a direct picture of the source.

## Encoding

VIR has one canonical JSON encoding:

- fields in the order of this chapter's tables, never sorted by a library;
- no insignificant whitespace;
- program values (literal values, enum member values) as decimal strings, so 64-bit values survive any JSON reader; structural integers (the schema version, parameter indexes, local IDs) as JSON numbers;
- every expression as an object whose first field is its `type`, so a reader never has to infer one;
- node IDs not written: a node's ID is its position in pre-order;
- strings escaped by a fixed rule: `"` and `\` with a backslash, control characters as `\u00XX`, and nothing else, so non-ASCII identifiers are written as UTF-8;
- UTF-8 throughout.

The writer is hand-written rather than built on `System.Text.Json`, because that library's default escaping (of `+`, `<`, `>`, `&`, `'` and non-ASCII characters) has changed between releases, and the netstandard2.0 build of `Warrant.Vir` and a net10.0 server would otherwise risk writing the same unit differently (KTD5).
A test writes the same units from both target frameworks and compares the bytes.
The reader, which only the engine and later the server need, is built for net10.0 only and uses the in-box `System.Text.Json`; reading is not where the bytes are decided.

A binary encoding (design §4.1) waits until the server needs one.

## Hashes

Each unit has two SHA-256 hashes (KTD21).

- The **unit hash** covers the unit's own canonical encoding.
- The **closure hash** covers the unit hash followed by the closure hashes of its `deps`, in key order.

Design §8.2 planned to key the cache on a unit and the *statements* of what it depends on.
That is not enough under a shallow embedding: `CappedAtTheLimit` is proved by computing `Payout`, so editing `Payout`'s body can turn a proved theorem false without changing the theorem's own text.
The closure hash changes whenever anything the unit reaches changes, which is the key M5b's cache needs; design §8.2 now says so.
The graph is acyclic, because M4 rejects recursion and cyclic record types (chapter 3).

Source spans are in neither hash.
They live in a side table keyed by node ID, where node IDs are assigned in pre-order.
Without that split, adding a comment line above a method would move every span below it and change every hash.
The engine's results refer to node IDs (the two sides of a false claim, for example) and get their spans from the side table of the current extraction, so a result cached by M5b's server will never point at stale lines.
Extraction's own diagnostics carry source locations directly, because they are produced from the current compilation and never cached.

## The running example in VIR

`Payout`'s unit as M4 wrote it, laid out for reading (the canonical form has no whitespace; it is `tests/Warrant.Vir.Tests/golden/payout.json`, which since M5a has `"vir": 2` and is otherwise the same):

```json
{
  "vir": 1,
  "key": "M:Payouts.PayoutRules.Payout(System.Int32,System.Int32,System.Int32)",
  "kind": "function",
  "params": [
    { "name": "loss", "type": "int32" },
    { "name": "deductible", "type": "int32" },
    { "name": "limit", "type": "int32" }
  ],
  "returns": "int32",
  "body": { "block": [
    { "if": {
        "c": { "compare": { "type": "bool", "op": "le", "kind": "int",
                "l": { "param": { "type": "int32", "index": 0 } },
                "r": { "param": { "type": "int32", "index": 1 } } } },
        "then": { "block": [ { "return": { "lit": { "type": "int32", "value": "0" } } } ] }
    } },
    { "decl": { "local": 0, "name": "covered",
        "init": { "binary": { "type": "int32", "op": "sub", "overflow": "wrap",
                "l": { "param": { "type": "int32", "index": 0 } },
                "r": { "param": { "type": "int32", "index": 1 } } } } } },
    { "return": { "cond": { "type": "int32",
        "c": { "compare": { "type": "bool", "op": "gt", "kind": "int",
                "l": { "local": { "type": "int32", "id": 0 } },
                "r": { "param": { "type": "int32", "index": 2 } } } },
        "then": { "param": { "type": "int32", "index": 2 } },
        "else": { "local": { "type": "int32", "id": 0 } } } } }
  ] },
  "assumptions": [],
  "facts": { "overflow": "wrap", "language": "14", "extractor": "0.1.0", "roslyn": "5.0.0" },
  "deps": []
}
```

The `overflow` field on `sub` is what tells translation to use wrapping subtraction; if the project had overflow checking on, extraction would have rejected the node before it got here (chapter 3).
`CappedAtTheLimit`'s unit has `Payout`'s key in its `deps`, so its closure hash changes when `Payout` does.
