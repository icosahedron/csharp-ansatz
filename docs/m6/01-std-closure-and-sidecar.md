# 1. The Std closure and the sidecar

> Part of the [M6 design](README.md). Decisions: KTD1, KTD2, KTD3, KTD6, KTD15 and KTD17. Units: U1 (PR #130), U2.

Contracts are stated and proved with Lean's `Std.Do`: Hoare triples, weakest preconditions and `@[spec]` lemmas over
monads (KTD1).
`Std.Do`'s definitions and lemmas are stable in Lean 4.35.0; only its tactic, `mvcgen`, is deprecated there
(`Std/Tactic/Do/Syntax.lean:440`), and Warrant does not use the tactic (chapter 7).
`Std.WP`, the newer framework, is marked experimental and changed in 4.35, so M6 does not build on it.
The walker's structural rules are named in one place, `src/Warrant.Engine/Contracts/SpecTable.cs`, so a later move to
`Std.WP` changes names there and not the walker's structure.

Before M6 the semantics bundle held Init's part that `lean/bundle-roots.txt` reaches and the Warrant library.
M6 adds the `Std.Do` constants the models and the walker mention, the effect monad and its models, and the walker's
rules, all through the same roots file.

## Roots, not modules

`scripts/export-semantics.sh` exports the roots and their dependency closure (M4 KTD2), and M6 keeps that: it adds
`Std.Do` names to `lean/bundle-roots.txt`, not the `Std.Do` module (KTD2).
All of `Std.Do` would add 1,443 constants to Init, 937 of them theorems; the roots add only what the effect monad
`ExceptT ClrExn (StateM σ)` needs: the structural spec lemmas (`Spec.pure`, `Spec.bind`, `Spec.map`, `Spec.seq`), those of
`StateT`, `ExceptT` and `MonadExcept`, the `SPred` and `PredTrans` lemmas of the VC simp set (chapter 7), and what they
mention.
`Std.Do`'s loop, iterator, `ReaderT`, `OptionT` and `EStateM` specs are left out until M7 needs them.

Nothing `Std.Do` brings in is an axiom, an `extern` or an `implemented_by`, so the bundle check of #26 holds unchanged:
`SemanticsBundle.AxiomProblem` still allows only `propext`, `Classical.choice` and `Quot.sound`, and the declarations of
those axioms and of every constant the kernel computes with by name must be exactly Lean's, as
`src/Warrant.Engine/PinnedDeclarations.ndjson.gz` records them.
The pin file is regenerated with the bundle (`dotnet run scripts/pin-kernel-declarations.cs`); it changed with U1's
and U2's bundles, and no later unit added a pinned declaration.

How the bundle grew, unit by unit (counts from `scripts/count-export.py`, `tests/data/README.md`):

| After | Roots | Constants | What came in |
|---|---|---|---|
| M5b | 394 | 2,835 | |
| U1 | 445 | 3,210 | the `Std.Do` roots |
| U2 | | 3,920 | the division bridges and the `BitVec`, `Nat` and `Int` lemmas Init's `sdiv`/`srem` proofs use |
| U3 | 504 | 3,973 | `ClrExn`, `ClrM`, `throw`, `ClrExn.Allowed`, the `ite`/`dite` triple rules, the raising integer models |
| U16 | 526 | 3,993 | the nullable and `Math` models on `int` and `long`, `Option` |
| U4 | 583 | 4,098 | the `decimal` model and `Math` on `decimal` |
| U9 | 605 | 4,099 | `Option.isNone`, the one constant the monadic translation emits that was not already there |
| U10 | | 4,099 | the triple's constants, all already in the closure |
| U11 | | 4,109 | the walker's rules in `lean/Warrant/Vc.lean` |
| U20 | 630 | 4,112 | three simp lemmas for a nullable `Spec.Ensures` meeting a constructor |
| #182 | 641 | 4,125 | `Spec.NoThrow`: `ClrExn.External`, its equations, `ClrExn.allowed_of_external`, `Vc.callExternal`, `Vc.callPure` |
| #244 | 660 | 4,165 | the models of default-context `+ - *` and unary `-` in a body that can raise, and `Int.instAdd`, `Int.instSub`, `Int.instMul` |

No unit added an axiom.

## `@[spec]` in the sidecar

Lean marks a model operation's triple `@[spec]`, and `mvcgen` finds it through that attribute.
lean4export does not carry attributes, so M5a's attribute sidecar (`tests/data/warrant-attributes.ndjson.gz`, docs/m5a/05)
carries them, and M6 adds a `spec` kind (KTD15):

```text
{"kind":"spec","name":N,"prio":P,"form":"triple"|"equation","module":M}
```

`tools/warrant-attrs/Main.lean` writes one entry per `@[spec]` lemma among the bundle's constants, in registration order:
a triple from `mvcgen`'s spec map, or an equation from its simp set.
The sidecar's format goes to 2 (`Sidecar.FormatVersion`); a format-1 sidecar is refused.
`scripts/export-attributes.sh` imports `Std.Do`, and `src/Warrant.Meta/Attributes/Sidecar.cs` parses the kind.
The sidecar now has 33 `spec` entries: 13 from `Std.Do`, 14 from U3 (`ClrM.throw` and the raising integer models), 4
from U16 (the raising nullable reads and `Math.Abs`) and 2 from U4 (`decimal` `+` and `-`).

The walker reads them by the head constant of the program it is looking at (chapter 7).
That is the only place a model operation's spec comes from: `SpecTable` names the structural rules and nothing else.
A discrimination tree is not needed, because the walker knows each node's head.

The result cache already keys every entry on the bundle's and the sidecar's SHA-256 (M5b,
`src/Warrant.Engine/Service/Cache/CacheKey.cs`), so each regeneration invalidated M5b's entries without a cache change.

## Division for `omega`

M6 models C#'s truncating `/` and `%` (KTD6, chapter 2), and a division VC is only useful if `omega` can read it.
Two things stood in the way, and U2 fixed both before any division VC was attempted (KTD17).

**#41: `int.MinValue` was an opaque atom.**
The compiler folds `int.MinValue` to `-(2147483648 : Int32)`.
In the omega-prep set, `Int32.toInt_neg` and `Warrant.Int32.toInt_neg_ofNat_lit` match that term under the same
discrimination-tree keys, and at equal priority the earlier-added `toInt_neg` won, leaving `(2147483648 : Int32).toInt`,
which no literal lemma evaluates.
Every `MinValue / -1` guard mentions that literal.
The literal lemmas now have priority 1001; the translator is unchanged.

**Truncating division.**
Lean's `Int32` division is `BitVec.sdiv`, which truncates, as C# does.
Warrant's `omega` reads neither `Int.tdiv`/`Int.tmod` nor `Int.sign`, so `lean/Warrant/Checked.lean` proves bridges that
state the result with `Int.ediv`/`Int.emod` and `Int`-valued `if`s on the operands' signs, with no side conditions:
`Warrant.Int32.toInt_div`, `toInt_mod` and their `Int64` twins, from Init's `toInt_div_of_ne_left`,
`toInt_div_of_ne_right` and `toInt_mod`.
They join the omega-prep set with `Int.ediv_neg` and `Int.emod_neg`, which move a negative literal divisor's sign where
`omega` reads it.
Those proofs pull in about 700 constants of Init (the table above), most of them `BitVec` lemmas.

`omega` reads a division by a literal.
It cannot relate `a / b` to `a` and `b` for a symbolic `b`, so a contract that needs that takes a `Spec.Assert` or a
`[ProofFor]` script (chapter 7).

## A verified load, measured

M5b KTD19 deferred to M6 the choice between loading the bundle verified, re-checking every declaration when the server
starts, and a trusted store base.
KTD3 keeps the verified load unless server start crosses 10 seconds on the reference workstation of docs/m5b/08 (a
32-core Windows 11 machine whose M5b start was 2.9 s), because a trusted base widens the trusted computing base (design
§9).
The threshold was 5 seconds until the owner raised it to 10 on 2026-11-11 (#178): a slower start is better than giving
up a verified load over a limit that is, for now, arbitrary. The measurements below were made against 5 seconds.
Every unit that grew the bundle measured again: seven alternating cold starts of Release CLIs carrying the two bundles
compared, `warrant verify tests/corpus/m5a/rejected --server auto --timings` ("started the server and connected in").

| Bundle | Constants | Server start, median | Measured against, same session |
|---|---|---|---|
| U2 | 3,920 | 4,152 ms | U1's 3,210: 3,147 ms |
| U3 | 3,973 | 4,217 ms | U2's: 4,303 ms |
| U16 | 3,993 | 3,936 ms | U3's: 4,095 ms |
| U4 | 4,098 | 4,548 ms | U16's: 4,286 ms |
| complete (U14) | 4,112 | 4,053 ms | M5b's 2,835: 2,807 ms |

The complete M6 bundle starts 1.25 s (44%) slower than M5b's in the same session and adds about 10 MB of GC heap, and
it stays under the threshold by about 0.95 s against the 5 seconds then in force, and by about 5.95 s against 10.
The run-to-run noise on that machine is a few hundred milliseconds (U16's bundle measured 3,936 and 4,286 ms in two
sessions), so the units that added a handful of constants (U9, U11, U20) were not measured separately.
The bundle stays a verified load. The full tables are in `tests/data/README.md`.
