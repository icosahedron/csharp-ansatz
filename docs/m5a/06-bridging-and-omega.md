# 6. Bridging and omega

> Part of the [M5a design](README.md). Decisions: KTD12, KTD13 in the [plan](../plans/2026-11-03-0838-feat-m5a-meta-tactics-plan.md).

`omega` decides linear arithmetic over `Int` and `Nat`: given hypotheses and a goal built from `+`, `-`, multiplication by constants, `/` and `%` by constants, and comparisons, it either proves the goal or reports that it could not.
Translated C# arithmetic is over `Int32` and `Int64`, which wrap (M4 D7), and `omega` knows nothing about them.
This chapter covers the step that moves a goal from `Int32` to `Int` (design §6.2's bridging), the port of `omega`, and what each running example does.

## From `Int32` to `Int`

Every `Int32` value has an integer value, `Int32.toInt x`, between `-2^31` and `2^31 - 1`.
Init's lemmas restate comparisons and operations through it:

| Lemma (Init, `Data/SInt/Lemmas.lean`) | Statement | `@[simp]`? |
|---|---|---|
| `Int32.lt_iff_toInt_lt` | `x < y ↔ x.toInt < y.toInt` | no |
| `Int32.le_iff_toInt_le` | `x ≤ y ↔ x.toInt ≤ y.toInt` | no |
| `Int32.toInt_add` | `(x + y).toInt = (x.toInt + y.toInt).bmod (2^32)` | yes |
| `Int32.toInt_sub`, `toInt_mul`, `toInt_neg` | the same shape | yes |
| `Int32.toInt_zero`, `toInt_one`, `toInt_minValue`, `toInt_maxValue` | the constants | |
| `Int32.le_toInt`, `Int32.toInt_lt` | `-2^31 ≤ x.toInt`, `x.toInt < 2^31` | |

`Int.bmod x m` is the balanced remainder: the value congruent to `x` modulo `m` in `[-m/2, m/2)`.
That is exactly two's-complement wrap-around, so `toInt_add` states C#'s `x + 1` faithfully.
The `Int64` versions use `2^64` and `2^63`.

`omega` does not understand `Int.bmod` and treats it as an unknown (*ran*: both the true and the false `Increment` goals fail with `bmod` left in).
Init defines it with `Int.bmod_def`:

```lean
Int.bmod x m = if x % m < (m + 1) / 2 then x % m else x % m - m
```

and `omega` handles `%` by a constant and splits an `if` whose branches are integers.
So the omega-prep simp set rewrites `bmod` away (KTD13).

## The omega-prep set

`Tactic.Omega()` runs, at every hypothesis and at the goal, a `simp` with only these lemmas, then `omega`:

```text
gt_iff_lt, ge_iff_le, ne_eq
Int32.lt_iff_toInt_lt, Int32.le_iff_toInt_le, ← Int32.toInt_inj
Int32.toInt_add, toInt_sub, toInt_mul, toInt_neg
Int32.toInt_zero, toInt_one, toInt_minValue, toInt_maxValue, toInt_toInt64
Warrant.Int32.toInt_ofNat_lit, Warrant.Int32.toInt_neg_ofNat_lit       (chapter 5)
apply_ite Int32.toInt
Int.bmod_def
the Int64 versions of all of the above
```

The list lives in one C# table, and each name is a bundle root (KTD29).
This is Lean's `bv_omega` pattern (`simp only [bitvec_to_nat] at *; omega`), which converts `BitVec` to `Nat`; Lean has no `Int32` equivalent, so Warrant writes one.

The range facts `-2^31 ≤ x.toInt` and `x.toInt < 2^31` are not rewrites; `omega` needs them as hypotheses.
Lean's `omega` already adds `BitVec.isLt` whenever it meets a `BitVec.toNat x` atom, and Warrant's port adds the two `Int32` (or `Int64`) range lemmas whenever it meets an `Int32.toInt x` atom (KTD12).

## The true example

`LargerBelowMax` from the corpus: `x < int.MaxValue` implies `Increment(x) > x`.
After `Unfold(nameof(Increment))`, the prep set turns the goal into (*ran*)

```lean
x.toInt < 2^31 - 1 →
  x.toInt < (if (x.toInt + 1) % 2^32 < (2^32 + 1) / 2
             then (x.toInt + 1) % 2^32
             else (x.toInt + 1) % 2^32 - 2^32)
```

`omega` negates the goal, takes `x.toInt`, the `if` and `(x.toInt + 1) / 2^32` as atoms, adds the range facts, splits the `if` into two cases, and finds a contradiction in each.
Warrant's existing kernel accepted Lean's proof of this.

## The false example

`AlwaysLarger` has no premise, and with `x = 2^31 - 1` the goal is false, so `omega` fails (*ran*):

```text
omega could not prove the goal:
a possible counterexample may satisfy the constraints
  b ≥ 0
  -2147483648 ≤ a ≤ -1
  -6442450943 ≤ a + 4294967296*b ≤ -2147483648
where
 a := if (x.toInt + 1) % ↑(2 ^ 32) < … then … else …
 b := (x.toInt + 1) / 4294967296
```

These constraints describe the bad region; they do not name a value.
The build error shows the goal `omega` was given, after `Unfold` and before the prep step, with C# names, and the counterexample `x = 2147483647` from the engine's boundary search (chapter 4), and keeps omega's text, with its atoms printed by the goal printer, as the last part of the message.

## The decrease example

`Sum.$dec_1` from chapter 3:

```lean
∀ (n : Int32), ¬ n ≤ 0 → (n - 1).toInt.toNat < n.toInt.toNat
```

The prep set turns `¬ n ≤ 0` into `¬ n.toInt ≤ 0` and `(n - 1).toInt` into a `bmod`, then an `if`; `omega` handles `Int.toNat` itself (it rewrites `↑(x.toNat)` to `max x 0`), and with the range facts it proves the obligation (*ran*, with the same lemmas in Lean).
Without the guard, `n = int.MinValue` makes `n - 1` wrap to `int.MaxValue`, the obligation is false, and `omega` fails, which is the right answer.

## The port

`omega` is ported from `Lean/Elab/Tactic/Omega/` (KTD12):

| Lean 4.35.0 | Lines | Contents |
|---|---|---|
| `Frontend.lean` | 714 | collecting hypotheses, turning terms into linear combinations over atoms, building the proof |
| `OmegaM.lean` | 262 | atoms, and the facts each new atom contributes |
| `Core.lean` | 578 | the problem, exact elimination of equalities, Fourier–Motzkin elimination, and justifications |
| `MinNatAbs.lean`, `FalseOrByContra.lean` | 150, 73 | helpers; turning the goal into `False` |

Lean's `omega` is exact Fourier–Motzkin without the "dark" and "grey" shadows of the full Omega test: it is sound, and complete when an exact elimination exists, which covers every exit example.
Coefficients use `BigInteger`, because elimination multiplies them.

The proof is reflective.
`omega` records how each derived constraint came from earlier ones (a justification tree), and the proof term restates that tree with lemmas from `Init/Omega/` (`Lean.Omega.tidy_sat`, `Constraint.combine_sat'`, `combo_sat'`, `not_sat'_of_isImpossible`, …) applied to literal lists of integers.
The kernel then recomputes Init's functions on those lists (for example `tidyConstraint`) to check each step.
Two consequences follow:

- the C# code must compute exactly what Init's definitions compute, or the kernel rejects the proof; U18's property tests compare the two on random inputs, so a mismatch is found before a user hits it;
- the kernel does real work, but little: Lean's proofs of the exit examples passed Warrant's kernel at 100,000 fuel per declaration, 200 times below the build budget (*ran*).

An `omega` proof over `Int` alone depends on `propext` and `Quot.sound` (*ran*); `omega` adds `Classical.choice` only when it turns a goal that is not decidable into `False` by classical contradiction (`FalseOrByContra`).
For the exit examples `Classical.choice` comes from Init's `Int32` lemmas that the prep set uses (chapter 3), and the assumption report lists whichever axioms a certificate actually depends on.
