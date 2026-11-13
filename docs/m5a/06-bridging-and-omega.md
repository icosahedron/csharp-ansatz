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
`Int.bmod_def` holds by definition, so this rewrite is a change by definition and leaves no trace in the certificate.

## The omega-prep set

`Tactic.Omega()` first tries `assumption` at reducible and instance transparency, as Lean 4.35.0's `omega` does.
If that does not close the goal, it runs `simp only [prep] at *`, with `decide` on and `contextual` off, where `prep` is only these lemmas, and then `omega`:

```text
gt_iff_lt, ge_iff_le, ne_eq
Int32.lt_iff_toInt_lt, Int32.le_iff_toInt_le, ← Int32.toInt_inj
Int32.toInt_add, toInt_sub, toInt_mul, toInt_neg
Int32.toInt_zero, toInt_one, toInt_minValue, toInt_maxValue
Warrant.Int32.toInt_ofNat_lit, Warrant.Int32.toInt_neg_ofNat_lit       (chapter 5; priority 1001)
Warrant.Int32.toInt_div, Warrant.Int32.toInt_mod                        (M6 U2)
apply_ite Int32.toInt
the Int64 versions of all of the above
Int32.toInt_toInt64, Int64.toInt_toInt32
apply_ite Warrant.Decimal.units                                         (#216)
Int.bmod_def
Int.ediv_neg, Int.emod_neg                                              (M6 U2)
```

The list lives in one C# table (`OmegaPrepSet`), and each name is a bundle root (KTD29).
The literal lemmas are tried before `toInt_neg`, which matches the same terms: otherwise `int.MinValue`, which the compiler folds to `-(2147483648 : Int32)`, becomes `-(2147483648 : Int32).toInt` wrapped by `bmod`, and no literal lemma evaluates `(2147483648 : Int32).toInt`, so `omega` sees an unknown atom (#41).

M6 U2 adds division and remainder (M6 KTD6).
C#'s `/` and `%` truncate toward zero, as Lean's `Int32` operations do, and Init states their values with `Int.tdiv` and `Int.tmod`, which `omega` does not read.
`lean/Warrant/Checked.lean` restates them, without side conditions, with `Int.ediv`/`Int.emod` and `if`s that `omega` splits:

```lean
(a / b).toInt = if a.toInt = -2147483648 ∧ b.toInt = -1 then -2147483648
                else if 0 ≤ a.toInt then a.toInt / b.toInt else -(-a.toInt / b.toInt)
(a % b).toInt = if 0 ≤ a.toInt then a.toInt % b.toInt else -(-a.toInt % b.toInt)
```

The first branch is Lean's wrap-around of `MinValue / -1`, which the CLR throws on instead; a division by zero is `0` (remainder: the dividend), which the CLR also throws on.
`omega` reads a division or remainder only by a literal, and `Int.ediv_neg` and `Int.emod_neg` move a negative literal divisor's sign out, because the literal lemmas write `-5` as `-↑5`, which `omega` does not take as a literal divisor.
So are `Lean.Omega.LinearCombo.coordinate_eval_0` to `coordinate_eval_9`, which `omega`'s proof uses for its first ten atoms.
This is Lean's `bv_omega` pattern (`simp only [bitvec_to_nat] at *; omega`), which converts `BitVec` to `Nat`; Lean has no `Int32` equivalent, so Warrant writes one.

The range facts `-2^31 ≤ x.toInt` and `x.toInt < 2^31` are not rewrites; `omega` needs them as hypotheses.
Lean's `omega` already adds `BitVec.isLt` whenever it meets a `BitVec.toNat x` atom, and Warrant's port adds the two `Int32` (or `Int64`) range lemmas whenever it meets an `Int32.toInt x` atom (KTD12).

## When `omega` alone fails

If the prep step and `omega` do not prove the goal, `Tactic.Omega()` tries it once more with facts that hold in every
case but that `omega` cannot find (`OmegaStrengthened`, `src/Warrant.Meta/Tactic/Omega/Strengthen.cs`; #217, #237,
#257). Each fact is a proved hypothesis or rewrite, so the kernel checks it with the rest of the proof, and the step can
only make a true goal provable. A goal `omega` proves alone gets the same proof as before, and a failure reports the
first attempt's goal and constraints.

In this order:

- **Products.** `omega` reads linear arithmetic only, so `x * y` of two non-literal terms is an atom. For each such
  product, the step reads the tightest literal bound on each side of `x` and `y` that a hypothesis states (`c ≤ x`,
  `x < c`, after the prep step, which a trial run of it shows and then undoes), and adds
  `Warrant.Int.mul_ge_of_ge_of_ge`, `mul_ge_of_le_of_le`, `mul_le_of_ge_of_le` and `mul_le_of_le_of_ge`
  (`lean/Warrant/Checked.lean`) at those bounds: the four corners of `0 ≤ (x - a) * (y - b)`, linear in the atom
  `x * y` (McCormick's inequalities). Each is added as an implication, `a ≤ x → b ≤ y → a * y + b * x - a * b ≤ x * y`,
  which `omega` reads as a disjunction: it uses a corner whose bounds hold and drops one whose bounds it cannot show,
  so no bound needs a proof of its own. From `0 ≤ x ≤ 10000` and `0 ≤ y ≤ 1000` they give `0 ≤ x * y ≤ 10000000`
  (#257); from `-5 ≤ x, y ≤ -1`, `1 ≤ x * y ≤ 25`. A factor whose bound is not a literal (`b ≤ a`) gets none, and
  neither does the outer product of `a * b * c`, whose factor `a * b` has no literal bound. These facts come first, so
  the next step's range proofs have them.
- **Exact values.** For each `int`/`long` `a + b`, `a - b`, `a * b` or `-a` in the goal, a nested `Tactic.Omega()`
  tries to prove the exact result in range, `¬(a.toInt * b.toInt < -2^31 ∨ 2^31 - 1 < a.toInt * b.toInt)`; where it
  does, `Warrant.Int32.toInt_mul_of_range` (and its siblings in `lean/Warrant/Checked.lean`) rewrites
  `(a * b).toInt` to `a.toInt * b.toInt` in the prep step, before `toInt_mul`'s `bmod`. `omega` has no dark shadow,
  so it cannot always rule out the wrap-around from bounds on its own; `x * 3 ≤ y * 3` under `0 ≤ x ≤ y ≤ 1000` is
  the example (#237).
- **`decimal` literals.** After the prep step (whose `decide` would otherwise turn it into `True`), each
  `Warrant.Decimal.units (lit s m e _ _)` with literal arguments gets the hypothesis `units (lit …) = n`, with `n` the
  literal's value in units of 10^-28, proved by `rfl`: the kernel computes it (#217).

The nested range proofs are plain `Tactic.Omega()` runs, never strengthened again, and at most eight terms of each kind
(products, operations, literals) are taken, so the step costs a bounded number of `omega` runs. They are charged to the
unit's tactic fuel: a product bounded on both sides with both bounds used (`1 <= a <= 99`, `1 <= b <= 99`,
`Spec.Ensures(r => r >= 1 && r <= 9801)`) takes most of the default budget.

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
Warrant's kernel accepted Lean's proof of this during planning, and Warrant's own `omega` now proves it: the certificate uses `Int32.toInt_add`, `Lean.Omega.ite_disjunction`, `coordinate_eval_0` and `Int32.le_toInt`, and depends on `Classical.choice`, `Quot.sound` and `propext`.

`Clamp(x) <= 100` (`accepted/Clamp.cs`) goes through the literal lemmas: `Warrant.Int32.toInt_ofNat_lit` turns `(100 : Int32).toInt` into `100`, and `apply_ite` moves `toInt` inside `Clamp`'s two `if`s.

## The false example

`AlwaysLarger` has no premise, and with `x = 2^31 - 1` the goal is false, so `omega` fails.
Lean's text and Warrant's are the same; this is Warrant's (*ran*, `warrant verify tests/corpus/m5a/refuted`):

```text
omega could not prove the goal:
a possible counterexample may satisfy the constraints
  b ≥ 0
  -2147483648 ≤ a ≤ -1
  -6442450943 ≤ a + 4294967296*b ≤ -2147483648
where
 a := if (x.toInt + ↑1) % ↑(2 ^ 32) < (↑(2 ^ 32) + 1) / 2 then (x.toInt + ↑1) % ↑(2 ^ 32) else (x.toInt + ↑1) % ↑(2 ^ 32) - ↑(2 ^ 32)
 b := (x.toInt + ↑1) / 4294967296
```

These constraints describe the bad region; they do not name a value.
The build error's first line names the theorem, `omega`'s first line and the counterexample `x = 2147483647` from the engine's boundary search (chapter 4); `omega`'s constraints follow, with its atoms printed by the goal printer, and then the goal `omega` was given, after `Unfold` and before the prep step, with C# names (chapter 4 shows the whole message).

## The decrease example

`Sum.$dec_1` from chapter 3:

```lean
∀ (n : Int32), ¬ n ≤ 0 → (n - 1).toInt.toNat < n.toInt.toNat
```

The prep set turns `¬ n ≤ 0` into `¬ n.toInt ≤ 0` and `(n - 1).toInt` into a `bmod`, then an `if`; `omega` handles `Int.toNat` itself (it rewrites `↑(x.toNat)` to `max x 0`), and with the range facts it proves the obligation (*ran*, with the same lemmas in Lean, and by Warrant for `Sum`, `Add` and `SumLong`).
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

For the goals the tests cover, Warrant's failure messages match Lean 4.35.0's character for character.

An `omega` proof over `Int` alone depends on `propext` and `Quot.sound` (*ran*); `omega` adds `Classical.choice` only when it turns a goal that is not decidable into `False` by classical contradiction (`FalseOrByContra`).
For the exit examples `Classical.choice` comes from Init's `Int32` lemmas that the prep set uses (chapter 3), and the assumption report lists whichever axioms a certificate actually depends on.
