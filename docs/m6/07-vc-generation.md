# 7. VC generation

> Part of the [M6 design](README.md). Decisions: KTD1, KTD12, KTD13, KTD14, KTD15, KTD16 and KTD18. Units: U11, U20.

A contract obligation with no `[ProofFor]` script is proved by the default procedure (R11): the VC walker, then the VC
simp set, then `omega`, under the unit's D14 budgets.
Everything here is in `src/Warrant.Engine/Contracts/` and is untrusted: a bug can make a true claim fail, and the
kernel's check of the finished proof term is what keeps a false one out.

## Why a walker, not `mvcgen`

Lean's own VC generator is `mvcgen`, about 4,800 lines of meta code with `SPred` proof mode and matcher splitting, and it
is deprecated in Lean 4.35; its successor, `vcgen`, needs `Lean.Meta.Sym` and `grind`.
Warrant's translator emits a closed set of program shapes, so a walker over those shapes is enough (KTD13).
A simp-only pipeline over `Std.Do`'s `wp` equations handles straight-line code but cannot apply a dependency's
hypothesis at its call site; that step is what the walker adds.

## The rules

The walker's rules are `Std.Do`'s `bind`, `pure` and consequence rules and U3's `throw` and branch rules, re-stated at
`ClrM σ` with the `WP` instance a contract's triple states, in `lean/Warrant/Vc.lean`.
They are proved in Lean and checked by the kernel with the bundle.
The plan expected to apply `Std.Do`'s rules directly; the re-statement was needed because a model's `@[spec]`
precondition contains the continuation's weakest precondition, so the continuation is never a goal of its own (#212), and
because of #211 (chapter 2).
`SpecTable.cs` is the one place the rules are named (KTD1).

The walk starts with `Vc.pre`, which moves `Requires` into the context, and then proves `⦃⌜True⌝⦄ prog ⦃Q⦄` by the
program's head:

| Head of `prog` | Rule | New goals |
|---|---|---|
| `x >>= f` | `Vc.bind` | `x` with the postcondition `fun a => wp⟦f a⟧ Q` |
| `pure a` | `Vc.pure` | the normal postcondition at `a` |
| `ClrM.throw e` | `Vc.throw` (on `ClrM.throw_spec`) | the exception postcondition at `e`: closes for an allowed one, a VC for an implicit one |
| `if c then t else e`, `dite` | `Warrant.Triple.ite`, `dite` | one goal per branch, with `c` or `¬c` as a path condition |
| `Spec.Assert`'s check node | `Vc.assert` | `c` as a VC at the `Spec.Assert`, then the rest knowing `c` |
| `Option.rec` on a nullable value | `Vc.optionRec` | the `none` and `some v` cases, each with its equation |
| a closed-enum recursor on a variable | `Cases`, then reduction | one goal per member |
| a model operation | `Vc.spec` with its `@[spec]` lemma from the sidecar, by head constant (KTD15) | its precondition at every world, split into one goal per conjunct (`And.intro`); `Vc.resume` turns the part that reaches the rest of the program back into a triple |
| a verified callee | `Vc.call` with the callee's `$contract`; `Vc.callExternal` for a callee with `Spec.NoThrow`, and `Vc.callPure` for a pure callee under a caller's `Spec.NoThrow` (#182) | its `Requires` as a VC at the call; its `Ensures` a hypothesis for the rest; its exceptions allowed by the caller's contract (`ClrExn.allowed_of_external` for a NoThrow callee of a caller without), or under a caller's `Spec.NoThrow` a VC at the call for a raising callee without it |
| a dependency operation | `Vc.call` with its contract hypothesis at the call's arguments and the current world (`Vc.callExternal` under `Spec.NoThrow`) | its `Requires` as a VC at the call; its `Ensures` a hypothesis for the rest; its exception allowed, and recorded |
| anything else | none | a leftover |

The walker picks `Vc.call` or `Vc.callExternal` from the contract's type, not by trying one and then the other:
`Apply` may unify `Vc.call`'s premise with a NoThrow callee's contract when the call's arguments let the callee's body
reduce to `pure v`, since unfolding `Std.Do.Triple` and the program then makes the two triples definitionally equal
(the kernel admits that proof). When `v` is a variable `a` and the callee's `Ensures` is `r = a`, the result
postcondition is solved as `r = r`, which says nothing, the weak postcondition #241 reported
(`VcCallUnificationTests` in `Warrant.Meta.Tests` reproduces it). The assignment is a correct solution found by
unfolding definitions, not a unifier bug.

Between rules the walker does a light reduction: β, projections, `let`s (a join point among them) and
`(⌜p⌝ s).down` to `p`, as Lean's `dsimp only` would (#212); nothing of the default simp set, so the next rule still
matches.
A rule that does not apply leaves the Meta state as it was, and the goal becomes a leftover, never a guessed rule or an
exception (KTD13).

At a dependency call the hypothesis is matched to the operation by position: the statement binds the world, the
operations in dependency and member order, the parameters, then one hypothesis per operation in the same order
(chapter 6).
At `ProcessPayment`'s `GetPayment` call that gives `r = none ∨ r.Id = paymentId` for the rest of the walk; the null
test then splits on `r`, and in the `some v` case the non-null unwraps before `Validate(payment)` and `with` are proved
from `r = some v`.

**Explicit throws.**
At a `throw` whose exception is allowed, the walker first tries to show the path unreachable: `False.elim`, the VC simp
set and `omega` over the path conditions (#92).
If that works, the throw is not reported. Otherwise it is closed by `ClrExn.Allowed` and recorded as a `MayThrow`
(chapter 8).
Under `Spec.NoThrow` (#182, chapter 6) the exception postcondition at an explicit throw is `ClrExn.External (thrown T)`,
which is `False`: a throw not shown unreachable is a `ReachableThrow` VC at the `throw`, never a `MayThrow`.
A verified callee whose triple was used is recorded as a `CalleeContract`, and each dependency call as a possible
external exception.

## Leftovers: the VC simp set, then `omega`

The goals the walker leaves are plain propositions over the path conditions, because every fact a step learns (a
branch's condition, a model's case, a callee's `Ensures`) is a hypothesis of the goals after it.
For each:

1. If the obligation's program is `pure (f params)`, the pure unit under proof is unfolded, as `Tactic.Unfold` does, and
   for each application of a pure verified callee with `Spec.Ensures` the instance of its `$contract_spec` is added as a
   hypothesis; the callee's body is not unfolded (#173). Each such callee is recorded as a `CalleeContract`, since the
   proof may rest on its contract (#223).
2. The VC simp set runs (KTD14, `VcSimpSet.cs`): Warrant's default set plus `Std.Do`'s one-state assertion lemmas
   (`SPred.entails_1`, `apply_pure_cons`, `down_pure_nil`, `and_cons`/`and_nil`, `or_cons`/`or_nil`), the
   `PredTrans.apply_*` equations, the equations of `ClrExn.Allowed` and `ClrExn.External`, and for a nullable `Spec.Ensures` meeting a
   constructor `Option.isNone_some`/`_none`, `Bool.false_eq_true`/`true_eq_false`, `Nullable.coalesce_some`/`_none` and
   `Nullable.some_eq_none` (U20). `SPred.entails_nil` alone never matches a one-state assertion, which is why the
   `_1` and `_cons` forms are listed. The set is kept apart from `Tactic.Simp()`'s default set, as omega-prep is, so
   existing scripts do not change.
3. Path conditions that are equations `x = e` are substituted, where `x` is a variable or a field of one
   (`refund.Original = none`, the null test of a record's nullable field, #218).
   Each read of a nullable value cases on it anew, so two reads of a dependency's result after its null test leave
   `r = some v₁` and `r = some v₂`, which substitution makes `some v₁ = some v₂`. That gives `v₁ = v₂`, proved by
   `congrArg (fun o => Nullable.coalesce o v₁)`, which rewrites every other hypothesis, so a fact about `v₁` (from the
   contract or a null test's `||`) is one about `v₂` (#226).
4. `omega` runs, through the M5a omega-prep set and chapter 1's division bridges, and when that fails, with
   `Tactic.Omega()`'s strengthening facts: in-range exact values, `decimal` literal values and product bounds
   ([docs/m5a/06](../m5a/06-bridging-and-omega.md#when-omega-alone-fails), #217, #237, #257).
5. If `omega` still fails and the goal or a hypothesis states an equation about a `Bool` term not split yet (a `bool`
   parameter, `flagged = false`; a null test, `x.isNone = true`; either side of `f = g`), the goal is split on that
   term with `Bool.casesOn`, each case rewritten with `b = false` or `b = true` as step 3 rewrites, and steps 2 to 5 run
   on each case, up to three terms split on one path (#227, #245): two `bool` parameters, two null tests, or a `bool`
   and a null test are each split. `omega` does not split a `Bool`. A failure reports `omega`'s first goal. A fourth
   `Bool` term on one path is not split.

U3's checkpoint used exactly this list of `SPred` and `PredTrans` lemmas (`EffectCheckpointTests.VcSimpLemmas`), and
the `ULift Prop` assertions of `Std.Do` did not defeat it, so the plan's fallback, a `wp` calculus over plain `Prop`s,
was not needed.

## Failures at their line

Every VC carries the VIR node ID of the operation or `Spec` call that produced it (KTD18, reusing M5b KTD7), so a cached
outcome renders at the current lines.
The program the kernel admits has no node IDs, so Semantics also produces a second translation of a raising unit with
each site's node in `MData`; the engine checks that, stripped of its tags, it equals the definition before walking it,
and strips the tags from every proof.
This is a deviation from the plan, which did not say how node IDs would reach the walker.

Each failing VC is its own WRT0001 at its node, starting with its kind (`VcKinds.Text`), then its path conditions as
hypotheses and its goal after the VC simp set. A hypothesis the simp set rewrote to `True`, such as a `Spec.Requires`
under the branch that settles it, is left out of the goal shown, which is display only (#240):

| Kind | Text |
|---|---|
| `DivisionByZero` | division by zero |
| `Overflow` | overflow in a checked operation (checked arithmetic, narrowing, `MinValue / -1`, `Math.Abs(MinValue)`, `decimal` `+` and `-`) |
| `NullRead` | null read (`Value` of a null `Nullable<T>`, a member access through a null reference) |
| `NullPassed` | null passed where a non-null value is required |
| `CalleePrecondition` | precondition of a callee at this call |
| `DependencyPrecondition` | precondition of a dependency member at this call |
| `Postcondition` | postcondition of the method (reported at the `Spec.Ensures`) |
| `Assert` | Spec.Assert |
| `WellDefinedness` | well-definedness of a Spec expression |
| `Unsupported` | a program shape the VC walker has no rule for (reported where the walk last was, #223) |
| `ReachableThrow` | an explicit throw is reachable under the Requires (Spec.NoThrow) (reported at the `throw`, #182) |
| `CalleeMayThrow` | a callee without Spec.NoThrow may throw explicitly at this call (Spec.NoThrow) (#182); the message goes on to name the callee and the way out, `Spec.NoThrow` on it with a `Spec.Requires` the call meets (#238, chapter 6) |
| `ArithmeticOverflow` | arithmetic overflow: this int/long operation may overflow, where C# would wrap (write unchecked(...) if wrapping is intended) (#244: a default-context operation in a method's body, reported at it; in a method that can raise, the walker maps its model's `assertFailed` at an arithmetic node to this kind) |

From the M6 corpus (*ran*, as `docs/proving/proofs-that-work.md` shows it):

```text
Effects.cs(10,46): error WRT0001: The contract of 'Effects.Ratio(int, int)' could not be proved: division by zero: omega could not prove the goal:
  a b : Int32
  h : b = 0
  ⊢ False
Effects.cs(10,46): error WRT0001: The contract of 'Effects.Ratio(int, int)' could not be proved: overflow in a checked operation: omega could not prove the goal:
```

Unlike a theorem's failure, a VC's carries no counterexample: the boundary search of M5a runs on theorems only.

**After a failed `Spec.Assert`** the walk continues knowing the asserted fact (KTD16: the triple forces it at that point),
so `Spec.Assert(b != 0); return a / b;` with no `Requires` reports the `Spec.Assert` and the division's `MinValue / -1`
overflow, but not its zero divisor.
Both readings of the plan are sound, since the method fails either way; which VCs to report after a failed assertion is
the owner's open decision #221.

## `Tactic.VcGen()`

In a `[ProofFor]` or `Spec.Assert` script, `Tactic.VcGen()` runs the walker on the triple and leaves its leftovers, with
the VC simp set already applied, as the script's goals (KTD16).
`Contracts.Same` in `tests/corpus/m6/accepted/Contracts.cs` is proved by `Tactic.VcGen(), Tactic.Omega()`.
In a theorem's script it is `unsupported script argument`.

## Limits

- `omega` cannot relate `a / b` to `a` and `b` for a symbolic `b`; such a fact needs a `Spec.Assert` with a script, or
  a `[ProofFor]` script.
- A `switch` over a closed enum on a non-variable discriminant has no `generalize` step and becomes a leftover.
- #227 and #245 (fixed after M6): a `bool` postcondition that needs a case split on a `bool` parameter
  (`r => !flagged || r`), or a conditional `Spec.Ensures` over a null test (`r => x is null ? r == 0 : r == x.Value`),
  was left to `omega`, which does not split `Bool`s. Step 5 above splits them.
- #220 (fixed after M6): `warrant translate` loaded no attribute sidecar, so it could not run the default procedure and
  reported a contract that `warrant verify` proves as not proved. It now loads the sidecar beside the bundle, as
  `verify` does.
- #244: `omega` reads only linear arithmetic. Since #257 a product of two variables (`a * b`) is bounded from literal
  bounds on both factors (`0 <= a && a <= 10000` in the `Spec.Requires`), but not from a bound that is not a literal
  (`b <= a`). A `[ProofFor]` script cannot help a pure method there: its no-overflow obligations (`$wd_k`) are proved by
  the default procedure only, before the contract obligation the script proves
  (`AProductWhoseFactorHasNoLiteralBoundFailsEvenWithAProofForScript`). In a method that can raise the operation is a
  site of the contract obligation, so a script reaches it, but the script's tactics have nothing beyond `Tactic.Omega()`
  for a product either. A recursive call's result is unknown, since a recursive method has no `Spec.Ensures` yet
  (chapter 6). These are checker gaps: `unchecked` is only for an intended wrap, since it removes the check. (Fixed: a
  join point's parameters, #255, closed-enum arms, #258, and `Spec.Requires` on a recursive method, #256.)
- #258: a closed-enum section or arm that covers several members knows `s = A ∨ s = B`. Before the VC simp set, the
  default procedure splits such a hypothesis, an equation of a variable with a closed term on each side, with `cases`,
  one goal per member, so that each equation substitutes; `omega` alone does not read `Nat.beq` on member indices.
- #251: a `Spec.Assert` over two implicit locals can run out of tactic fuel. The fuel goes to `omega`, not to the
  walk: each implicit local adds `v = a op b` and `v.toInt = …` to every later `$wd` obligation, the VC simp set
  substitutes the first into the others, and `omega` then expands every nested `toInt` of wrapped arithmetic through
  `Int.bmod`. The main contract's last VC, `-a * 2 + a = -a`, costs as much on its own.
