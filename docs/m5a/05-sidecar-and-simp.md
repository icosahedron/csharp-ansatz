# 5. The attribute sidecar and simp

> Part of the [M5a design](README.md). Decisions: KTD5, KTD9 to KTD11, Key Decisions in the [plan](../plans/2026-11-03-0838-feat-m5a-meta-tactics-plan.md).

`simp` rewrites a goal with a set of lemmas until nothing more applies.
To behave like Lean's, it needs to know which lemmas are simp lemmas, with what priority and direction, which definitions it may see through, and which instances exist.
None of that is in the NDJSON bundle, which holds only declarations.
This chapter covers the file that carries it, the two lookup structures built from it, and the simplifier.

## The sidecar

`tests/data/warrant-attributes.ndjson.gz` sits next to the bundle and is exported from the same Lean toolchain and roots (KTD9).
A Lean program in `tools/warrant-attrs/`, modelled on Ansatz's `scripts/dump_attrs.lean` and `dump_instances.lean`, imports Init and the semantics library and writes one line per entry (`scripts/export-attributes.sh`).
These lines are from the committed file, the header's hashes shortened:

```json
{"kind":"header","format":1,"lean":"eb6cafb…","bundleSha256":"cc74b3a…"}
{"kind":"simp","name":"Int32.not_le","prio":1000,"post":true,"inv":false,"module":"Init.Data.SInt.Lemmas","leanKeys":["Not","LE.le","Int32","*","*","*"]}
{"kind":"congr","name":"ite_congr","fn":"ite","prio":1000,"hyps":[9,10,11]}
{"kind":"instance","name":"instDecidableEqInt32","class":"DecidableEq","prio":1000,"order":1700}
{"kind":"reducibility","name":"Int.bmod","status":"implicitReducible"}
{"kind":"matcher","name":"Int32.decEq.match_1","numParams":0,"numDiscrs":2,"uElimPos":0,"discrNames":[null,null],"alts":[{"numFields":2,"numOverlaps":0,"unitThunk":false}],"overlaps":[]}
{"kind":"class","name":"HAdd","outParams":[2]}
```

`leanKeys` are Lean's keys printed with `DiscrTree.Key.format`, which leaves out each key's arity.
The committed sidecar has 346 simp entries, 3 congruence lemmas, 142 instances, 575 reducibility entries, 324 matchers and 57 classes.

The exporter reads each extension's entries module by module, because after `importModules` the extension's state misses scoped entries (a lesson from Ansatz).
It keeps only names in the bundle's closure, so no entry points outside the checked environment, and the header records the bundle's hash, which the loader checks.
The assumption report still names only the bundle; adding the sidecar's hash to it, as KTD9 planned, is not built.

Four kinds deserve a note:

- **Reducibility.** Ansatz never exports it and guesses from definitional heights, which misses a `@[reducible] def`. Warrant exports every non-default status, including 4.x's `instanceReducible` and `implicitReducible` (chapter 2).
- **Priorities.** `Bool.false_eq` and `Bool.true_eq` rewrite each other's output and are confluent only because they have low priority; without priorities, `simp` loops.
- **Matchers.** Init definitions use compiled `match` functions, which are not reducible; Meta reduces them only with their matcher info.
- **Lean's keys.** The lookup keys Lean computed are kept, but only as a test oracle (below).

`no_index` is metadata (`MData`) on a lemma's statement, and lean4export drops metadata by default, so `scripts/export-semantics.sh` exports the bundle with `--export-mdata` to keep it.
In that export a true `Bool` value appears as `Lean.DataValue.ofBool true`.

Translated declarations have no Lean attributes, so the engine adds their entries when it admits them: every translated `abbrev` (an open enum and its members) is reducible, recursive definitions irreducible, and generated `casesOn` reducible (chapters 3 and 4).

The sidecar can only select which kernel-checked lemmas tactics try.
A stale or wrong sidecar can make a proof fail; it cannot make a false claim pass.

## Discrimination trees

`simp` must find, among hundreds of lemmas, those whose left side might match a subterm.
Lean indexes lemmas in a discrimination tree: each left side becomes a path of keys (constants, literals, `*` for anything), and a lookup walks the subterm's keys.
Warrant ports `Lean/Meta/DiscrTree/` and recomputes every key from the lemma's type in the bundle, at `reducible` transparency (KTD9).
The rules that matter most:

- instance and proof arguments are ignored, so `@HAdd.hAdd Int32 Int32 Int32 inst a b` keys on `HAdd.hAdd`, `Int32` and its two operands;
- `@OfNat.ofNat Int32 5 _` keys as the literal `5`;
- a term marked `no_index` keys as `*`.

U16's test recomputes the keys of every simp entry and compares them with `leanKeys`; they agree on all 346.
A port bug in key computation would otherwise make `simp` silently miss lemmas.

## Instances

`simp` needs instances: its `decide` step needs `Decidable (InvalidAmount = Valid)`, and a lemma's instance arguments that matching did not fill must be found.
Warrant indexes the sidecar's instances in a discrimination tree whose keys, like the simp keys, are recomputed from the instances' kernel types; an instance of `DecidableEq α` is indexed under `Decidable (Eq …)`, as in Lean.
It resolves a goal by depth-first search, highest priority first and most recent first among equals, with Lean's handling of out-parameters (`HAdd α β ?γ`), inside a nested metavariable depth so the search cannot assign the goal's holes (KTD10).
The search stops at a nesting depth of 32 or after 10,000 instances tried.
Lean's resolver is tabled, which matters for loops and diamonds in Mathlib's class hierarchy; Init's instances for `Int32`, `Int64`, `Int`, `Nat` and `Bool` are a few levels deep.

Open enums matter here: `DecidableEq PaymentResult` resolves only because `PaymentResult` is a reducible abbreviation of `Int32`, so the search reaches `instDecidableEqInt32`.

## simp

`simp` is ported from `Lean/Meta/Tactic/Simp/` (KTD11): `Main.lean`'s traversal, `Rewrite.lean`'s lemma application, `Types.lean`'s results and congruence, and the structural simprocs `reduceIte` and `reduceDIte`.
Each step returns a `Result`: a new term and, unless the change was by definition, a proof that the old term equals the new one.
Proofs compose with `Eq.trans`, and congruence lifts a rewrite inside an application with `congrArg`, `congrFun` and `congr`, under an implication with `implies_congr`, and under `ite` with the `@[congr]` lemma `ite_congr`.
The goal is replaced through `Eq.mpr`, and a goal that simplifies to `True` is closed with `of_eq_true`.

What is not ported: Lean's ground arithmetic simprocs (`Int32.reduceAdd`, `Int32.reduceToInt` and about 2,000 lines like them), `simp_all`, `dsimp` (where Lean calls it, Warrant's simp leaves the term as it is), automatically generated congruence lemmas (`mkCongrSimp?`), matcher equations, permutation and AC ordering of rewrites, loop protection, arithmetic normalisation, and unfolding a definition passed to `simp` as an argument.
Two needs those simprocs would serve are met otherwise:

- closed comparisons such as `InvalidAmount = Valid` are decided by `simp`'s `decide` step, which evaluates `Decidable.decide` in the kernel;
- `Int32` literals under `toInt` are rewritten by Warrant lemmas whose left side is marked `no_index`:

  ```lean
  theorem Warrant.Int32.toInt_ofNat_lit (n : Nat) (h : n < 2^31) :
      (no_index (OfNat.ofNat n : Int32)).toInt = n
  ```

  Without `no_index`, the lemma's left side keys on `OfNat.ofNat` with a variable, while a literal in the goal keys as the number itself, so the lemma never fires (*ran*).
  The side condition `h` is discharged by `decide`.

## The default simp set

`Tactic.Simp()` does not use Lean's defaults (Key Decisions).
Run on the translated `ValidImpliesPositive`, Lean's `unfold Validate; simp` stops at

```lean
(if p.Amount ≤ 0 then InvalidAmount else if p.Status = Pending then Valid else InvalidStatus) = Valid
  → 0 < p.Amount
```

(*ran*), for three reasons.
Init has no lemma that splits an equation whose left side is an `if`; Mathlib's `ite_eq_iff` does.
`InvalidAmount = Valid` is a closed comparison of two literals, which only a simproc or `decide` settles.
And the last step, from `0 < a → s = Pending → 0 < a`, needs `contextual`, which uses an implication's premise while simplifying its conclusion.

So Warrant's defaults are (`DefaultSimpSet`):

- the 54 Init lemmas listed under "Default simp set" in `lean/bundle-roots.txt` (logic, `Bool`, `ite`, `decide`, `gt_iff_lt` and `ge_iff_le`, and the `Int32`/`Int64` lemmas `not_le`, `not_lt`, `lt_irrefl` and `le_refl`), each with its sidecar priority;
- six lemmas from `lean/Warrant/Simp.lean`: `Warrant.ite_eq_iff`, `Warrant.dite_eq_iff` and the four literal lemmas (`Warrant.Int32.toInt_ofNat_lit`, `toInt_neg_ofNat_lit` and their `Int64` versions). They carry no `@[simp]`; the default set and the omega-prep set name them.

  ```lean
  theorem Warrant.ite_eq_iff [Decidable p] {a b c : α} :
      (if p then a else b) = c ↔ (p ∧ a = c) ∨ (¬p ∧ b = c)
  ```

- the semantics library's own `@[simp]` lemmas, of which there are none yet;
- `decide` and `contextual` on.

The plan's Key Decisions estimated about 120 Init lemmas; 54 cover the M5a corpus.
Before the engine marked translated `abbrev`s reducible, Warrant's `simp` stopped on `ValidImpliesPositive` exactly where Lean's default `simp` stops.
With the defaults, the rewrite closes the goal (*ran*, with the same lemmas in Lean, and in Warrant):

1. `ite_eq_iff` splits the outer `if`: `(a ≤ 0 ∧ InvalidAmount = Valid) ∨ (¬ a ≤ 0 ∧ (if … ) = Valid)`.
2. `decide` turns `InvalidAmount = Valid` into `False`; `and_false` and `false_or` remove the branch.
3. `Int32.not_le` turns `¬ a ≤ 0` into `0 < a`; the inner `if` splits the same way.
4. `gt_iff_lt` turns the conclusion `p.Amount > 0` into `0 < p.Amount`, by definition.
5. `contextual` rewrites `0 < a` in the conclusion to `True` using the premise, and `implies_true` closes the goal.

Warrant's proof term uses `Warrant.ite_eq_iff`, `eq_false_of_decide` and `implies_congr_ctx`, and depends on `propext` only (a test checks both); Warrant's kernel also accepted Lean's version of the proof.
The full Init simp set was not an option: it has 10,301 lemmas, whose closure is about 31,000 constants, twelve times the bundle, re-checked on every load.

A developer changes the defaults per call: `Tactic.Simp(nameof(MyLemma))` adds a theorem, `Tactic.Simp(Lean.Const("Int32.lt_iff_toInt_lt"))` adds a lemma from the bundle (only the bundle's declarations can be named, not all of Init), and `Tactic.Simp().With(decide: false)` or `.With(contextual: false)` turns an option off.
Naming a `[Verified]` method in `Tactic.Simp` does not unfold it; use `Tactic.Unfold`.

## `unfold` on recursive definitions

`Tactic.Unfold(nameof(Sum))` cannot unfold `Sum` by definition: it is irreducible, and unfolding it would expose `Nat.fix`.
It rewrites with `Sum.$eq_def` instead, using `simp`'s traversal with that one lemma, which is what Lean's `unfold` does with `f.eq_def`.
