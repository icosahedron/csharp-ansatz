# 4. Tactics and goals

> Part of the [M5a design](README.md). Decisions: KTD6 to KTD8, KTD19, KTD25, KTD29 in the [plan](../plans/2026-11-03-0838-feat-m5a-meta-tactics-plan.md).

A tactic takes the current goals and replaces them with new ones, filling holes as it goes.
When no goals are left, the theorem's proof is the instantiated term, and the kernel checks it.
This chapter covers the loop that runs a script, the tactics other than `simp` and `omega`, how goals are printed, and what a failure reports.

## The loop

The engine runs each theorem like this (KTD19):

```text
goal ?g : statement                         -- built by Semantics; ?g is synthetic opaque
intro the theorem's parameters              -- in order, under their C# names
for each tactic in the script:
    goals := tactic(goals)                   -- may assign holes, create goals, or fail
    drop goals that unification already solved
if goals remain:              WRT0001 "unsolved goals.", each goal printed
if a tactic failed:           WRT0001 with the tactic's message, and the goal it failed on
otherwise:
    proof := instantiateMVars(?g)
    if proof has a hole:      WRT0010 (an engine bug: a solved goal left a hole)
    Kernel.Add(theorem with proof)
        accepted:             proved
        rejected:             WRT0010 with the kernel's message
```

A theorem runs in its own budget scope, so running out of kernel fuel, tactic fuel or time ends that theorem only, with WRT0006 naming which: `tactic fuel ran out (171,970 steps)`, `kernel fuel ran out (…)` or `the time limit of 30 s was reached`.
Each failure is caught as what it is; M4's pipeline catches only `KernelException`, and an unexpected exception from Meta would otherwise end the whole run.
WRT0010 means Warrant built something its own kernel rejects: a bug in the engine or the translator, never a false claim.
A unit the engine could not translate or admit at all is reported as WRT0010 too.
The outcome names in reports and in `warrant verify`'s unit lines are `unproved` (WRT0001) and `internal` (WRT0010), next to M4's `translated`, `proved`, `false`, `undecided`, `failed` and `skipped`.

`TacticM` holds the goal list, like Lean's `Elab.Tactic.TacticM`, and each tactic is a ported `Meta`-level function lifted over it.
`Tactic.AllGoals(t)` runs `t` on every goal, and `Tactic.Try(t)` runs `t` and keeps the goals unchanged if it fails; both save and restore the metavariable context, which is immutable, so restoring costs nothing.

## The basic tactics

Each is ported from Lean 4.35.0's `Meta`-level implementation, not from the `Elab` tactic a Lean user types, because the `Elab` versions run Lean's term elaborator, which Warrant does not have (KTD6).

| Tactic | Lean source | What it does to `?g : T` |
|---|---|---|
| `Intro(names)` | `Meta/Tactic/Intro.lean` (208 lines) | `T = ∀ x, U`: assigns `?g := fun x => ?g₁` through a delayed assignment; the new goal `?g₁ : U` has `x` in context. One binder per name; without names, one binder under its own name, which is the C# variable's. |
| `Exact(h)` | `Elab/Tactic/ElabTerm.lean` | Infers `h`'s type, unifies it with `T` (goal holes may be assigned), and assigns `?g := h`. For a constant, inserts holes for its implicit and instance arguments first and requires that none remain. |
| `Apply(c)` | `Meta/Tactic/Apply.lean` (380) | Tries `c ?a₁ … ?aₙ` with increasing `n` until its type unifies with `T`; the unassigned `?aᵢ` become new goals, non-dependent first. |
| `Unfold(f)` | `Meta/Tactic/Unfold.lean` (58) | A non-recursive `f`: replaces `f` by its body, a change by definition recorded with `@id`. A recursive `f`: rewrites with `f.$eq_def` using `simp`'s machinery (chapter 5). |
| `assumption`, `rfl` | `Assumption.lean` (38), `Refl.lean` (65) | Used inside `simp`'s side conditions and by `Exact`; `rfl` assigns `@Eq.refl α a`. |

`Intro` on the false theorem, which is what the engine does for a theorem's own parameters before the script starts:

```text
before:   ⊢ ∀ (x : Int32), Increment x > x
after:    x : Int32
          ⊢ Increment x > x
```

A script's `Tactic.Intro` is therefore needed only for binders the statement itself introduces, such as those of `Spec.ForAll` or the premise of `Spec.Implies`.

## `cases` and `induction`

`Cases(x)` replaces a goal by one goal per constructor of `x`'s type; `Induction(x)` does the same with an induction hypothesis in each recursive case.
Both are `MVarId.cases` and `MVarId.induction` from `Meta/Tactic/Cases.lean` (388) and `Induction.lean` (244), with `revert`, `clear` and the field substitution they use.

```text
Cases(b) on b : Bool              →  case false: ⊢ P false       case true: ⊢ P true
Cases(s) on s : ClaimStatus       →  one goal per member, named after it
Cases(p) on p : Payment           →  one goal, with p's fields as hypotheses
Induction(n) on n : Nat           →  case zero: ⊢ P Nat.zero     case succ: n_ih : P n ⊢ P (Nat.succ n)
```

The script names the variable with a string, `Tactic.Cases("b")`, and the induction hypothesis is named after the field it is about, `n_ih`, as Lean names it.

Two things differ from what a Lean user sees.
Lean's `induction` on `Nat` uses a custom eliminator that shows `n + 1`; Warrant has no custom eliminators, so it shows `Nat.succ n` (KTD6).
And only types without indices can be split: `Cases("h")` on `h : a = b` reports ``Tactic `cases` failed: cases on an indexed family is not supported yet``, because it needs Lean's equation-unification machinery and `noConfusion`, which no M5a goal requires.
A `cases` error is reported as it is, not wrapped in Lean's "Tactic `cases` failed with a nested error".
`Induction` on an `int` is legal but useless, because `Int32` is a structure with one field; induction over integers goes through `Int`, which is follow-up work.

`Cases` needs `T.casesOn` for the type it splits, and the kernel generates only `T.rec` (M4 KTD9).
The engine generates `casesOn` and `ctorIdx` for every translated inductive (KTD8):

```lean
-- casesOn: rec with the induction hypotheses dropped, major premise before the minor premises
Cs.Claims.ClaimStatus.casesOn.{u} :
  {motive : ClaimStatus → Sort u} → (t : ClaimStatus) →
  motive Open → motive Paid → motive Denied → motive Withdrawn → motive t

-- ctorIdx: the constructor's position, as a Nat
Cs.Claims.ClaimStatus.ctorIdx : ClaimStatus → Nat
```

In Lean 4.35.0, distinct constructors are told apart with `ctorIdx` and Init's `noConfusion_of_Nat`, so these two are enough for `cases` and for `simp` deciding that `Open = Paid` is false.
They are definitions checked by the kernel and mentioned by no statement, so generating them in the untrusted engine adds nothing to the trusted base.
Lean's own `mkCasesOn` is C++ in 4.35.0; U14's tests generate `casesOn` and `ctorIdx` for Init's own types and compare them with Init's constants, which they match up to binder names, and Lean's kernel accepted the generated ones.
`casesOn` is marked reducible, and Meta treats it as an auxiliary recursor, as Lean does; `ctorIdx` keeps the default status, because Lean's own `ctorIdx` definitions are not reducible.

## How goals are printed

WRT0001 shows goals in Lean's layout, from `Meta/PPGoal.lean` (KTD7):

```text
case zero
⊢ Nat.add Nat.zero Nat.zero = Nat.zero

case succ
n : Nat
n_ih : Nat.add Nat.zero n = n
⊢ Nat.add Nat.zero (Nat.succ n) = Nat.succ n
```

(*ran*: `Induction` on `∀ n : Nat, Nat.add 0 n = n` in `tests/Warrant.Meta.Tests/CasesTests.cs`.)
The case tag appears when the goal has one; consecutive hypotheses with the same type share a line (`loss deductible limit : Int32`); the goal follows `⊢`; goals are separated by a blank line.

The terms themselves go through a small notation printer rather than Lean's delaborator, which is several thousand lines with its parenthesizer:

| Term | Printed |
|---|---|
| `@Eq α a b`, `@Ne α a b` | `a = b`, `a ≠ b` |
| `@LE.le α i a b`, `LT.lt`, `GE.ge`, `GT.gt` | `a ≤ b`, `a < b`, `a ≥ b`, `a > b` |
| `@HAdd.hAdd α α α i a b`, `HSub`, `HMul`, `Neg.neg` | `a + b`, `a - b`, `a * b`, `-a` |
| `And`, `Or`, `Not`, `Iff`, non-dependent `∀` | `∧`, `∨`, `¬`, `↔`, `→` |
| `@OfNat.ofNat Int32 5 i` | `5` |
| `ite c t e`, `dite c t e` | `if c then t else e` |
| `Int32.toInt x`, `Int.toNat i` | `x.toInt`, `i.toNat` |
| `p.2` on a translated record | `p.Amount` |
| `Cs.Claims.PaymentResult.Valid` | `PaymentResult.Valid` |
| `?m` | `?m.3` |

Implicit and instance arguments are hidden, and parentheses follow Lean's precedences.
Type names stay Lean's (`Int32`), because the hypotheses are Lean terms; member and parameter names are C#'s.

## What a failure reports

The two shapes of WRT0001 keep Lean's wording.
The first is a theorem without a script, `Prove.That(Increment(x) > x)`, from `warrant verify`'s tests; the second is the corpus's `AlwaysLarger`, whose `Tactic.Omega()` fails (both shown after the location):

```text
error WRT0001: Theorem 'Increments.AlwaysLarger(int)' could not be proved: unsolved goals. Counterexample: x = 2147483647.
  x : Int32
  ⊢ Increment x > x

error WRT0001: Theorem 'Increments.AlwaysLarger(int)' could not be proved: omega could not prove the goal. Counterexample: x = 2147483647.
  a possible counterexample may satisfy the constraints
    b ≥ 0
    -2147483648 ≤ a ≤ -1
    -6442450943 ≤ a + 4294967296*b ≤ -2147483648
  where
   a := if (x.toInt + ↑1) % ↑(2 ^ 32) < (↑(2 ^ 32) + 1) / 2 then (x.toInt + ↑1) % ↑(2 ^ 32) else (x.toInt + ↑1) % ↑(2 ^ 32) - ↑(2 ^ 32)
   b := (x.toInt + ↑1) / 4294967296

  x : Int32
  ⊢ x + 1 > x
```

A tactic that fails with an error of its own reads like ``Tactic `exact` failed: type mismatch`` followed by Lean's explanation; `omega`'s message is Lean's, which has no such prefix.
For the goals the tests cover, the messages match Lean 4.35.0's text character for character.
The first line of the message ends its sentence, and the later lines (here `omega`'s constraints) come before the goal block.

The theorem is named by its containing types and its parameter types, without the namespace: `'Increments.AlwaysLarger(int)'`; `warrant translate` uses the same form.
The diagnostic's location is the `Tactic.X` call that failed, or the theorem's name when goals remain at the end.
The first line is complete on its own, because Visual Studio's Error List shows one line (chapter 7).

**The counterexample** comes from a search the engine runs after a failure (KTD25).
For a theorem whose parameters are `int`, `long`, `bool` or enums, it evaluates `decide` of the claim in the kernel at boundary combinations (0, 1, -1, `MaxValue`, `MinValue`, `MaxValue - 1` and `MinValue + 1` for integers, both values of `bool`, each enum member) and reports the first assignment that makes the claim false.
`omega` itself reports only constraints, not values (*ran*), which is why the search exists.
The search is untrusted and never changes an outcome: a theorem with no counterexample found fails the same way, without the line.
It runs outside the theorem's budgets, with a cap of 1,000,000 kernel steps per combination and two seconds overall; a combination that hits its cap, such as `Sum(int.MaxValue)`, is skipped (KTD25).

## The tactics' constants

Every Init constant a tactic can put in a proof (`Eq.mpr`, `congrArg`, `of_eq_true`, the `Lean.Omega` lemmas, …) is listed in one C# table, and a test checks that each is a bundle root (KTD29).
M4 has the same test for the translator's constants.
A missing constant would otherwise fail only when a goal first needs it, and a certificate naming it would fail Lean's re-check with "unknown constant", which looks like a kernel disagreement.
