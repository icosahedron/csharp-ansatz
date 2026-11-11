# 6. Contract obligations

> Part of the [M6 design](README.md). Decisions: KTD9, KTD12, KTD16, KTD25 and KTD26. Units: U10, U19.

What a method must prove is a statement, and the statement is the claim, so Semantics states it and is trusted.
Proving it is the engine's job and is not (design D11).
This is the pattern M5a's decrease obligations already follow (`PipelineScope.ProveDecrease`): Semantics builds the
obligation, the engine proves it, the kernel checks the proof.
`src/Warrant.Semantics/Contracts.cs` states the obligations of a method, and `Dependencies.cs` adds a dependency's
operations and contract hypotheses.

## The triple

A verified function gets a contract obligation when it has a `Spec.Requires` or `Spec.Ensures`, when it can raise
(KTD11), or when it calls a function that has a `Spec.Requires` (KTD12):

```text
f.$contract : ∀ (σ : Type) params,
  ⦃⌜Requires⌝⦄ prog ⦃⇓r => ⌜Ensures r⌝; fun e => ⌜ClrExn.Allowed e⌝⦄
```

- `prog` is `@f σ params` for a raising unit and `pure (f params)` for a pure one, so the walker and call sites see one
  shape.
- `Requires` is the conjunction of the method's `Spec.Requires`, `Ensures` that of its `Spec.Ensures`; a missing one is
  `True`. So a method with no contract that divides by a parameter still has to prove that the divisor is never zero,
  and `int.MinValue / -1` never happens.
- The exception postcondition is `ClrExn.Allowed`: an explicit `throw` and an exception propagated from a dependency.
  Every implicit runtime exception (overflow, a zero divisor, a null read or unwrap, a failed `Spec.Assert`) is
  excluded, so the proof must show none can happen under `Requires`.
- The `WP` instance is the one instance resolution finds for `ClrM σ`.

A pure unit without a contract gets no obligation, so M4's and M5a's declarations are unchanged.

Contracts are total about implicit exceptions and partial about explicit ones.
`Ensures` holds on every normal return, and a path that ends in an explicit `throw` or a dependency's exception
satisfies the triple without saying anything.
So a method that throws on every path proves any `Ensures` (`Closed` in `tests/corpus/m6/accepted/Effects.cs`), and the
report lists each such path (KTD20, chapter 8).
Making a reachable explicit throw fail the build would reject ordinary argument validation; whether to offer an opt-in
way to state that no explicit throw is reachable under `Requires` is the owner's open decision #182.

## With dependencies: the D9 shape

A method that calls dependency members binds one operation per (dependency, member) pair (chapter 5) and takes one
hypothesis per operation: the member's contract over every argument and every world (KTD9, design §6.3):

```text
ProcessPayment.$contract : ∀ (σ : Type)
    (store_GetPayment : Int32 → ClrM σ (Option Payment))
    (store_SavePayment : Payment → ClrM σ Unit)
    (paymentId : Int32),
  (∀ id, ⦃⌜True⌝⦄ store_GetPayment id ⦃⇓r => ⌜r = none ∨ r.Id = id⌝; allowed⦄) →      -- store_GetPayment_spec
  (∀ p,  ⦃⌜True⌝⦄ store_SavePayment p ⦃⇓_ => ⌜True⌝; allowed⦄) →                       -- store_SavePayment_spec
  ⦃⌜True⌝⦄ ProcessPayment store_GetPayment store_SavePayment paymentId
    ⦃⇓r => ⌜r ≠ Result.Success ∨ paymentId > 0⌝; allowed⦄
```

This is the shape, not the exact syntax; the test `DependencyObligationTests` compares `ProcessPayment`'s obligation
with a hand-written statement binder by binder.
Each hypothesis is built from the member's contract unit: its `Spec.Requires` as the precondition, its `Spec.Ensures` as
the normal postcondition, and `ClrExn.Allowed` as the exception postcondition, so a dependency's exceptions are allowed
and reported.
A member whose contract is `=> default!` or `abstract` states `True` for both.
The hypothesis is named after the operation with `_spec` appended (`store_GetPayment_spec`), which a `[ProofFor]` script
can use with `Tactic.Exact`.

The theorem holds for every implementation of the members that keeps their contracts, in every world.
The contract is a hypothesis of this one theorem, never an axiom: a wrong contract weakens the proofs that use it and
cannot be used to prove anything else (design D9).

## Using a callee's contract

A verified callee's proved triple is used at its call sites as a lemma (KTD12): its `Requires` becomes a VC at the call,
and its `Ensures` a fact afterwards (chapter 7).
A pure method with `Spec.Ensures` also gets its contract as a plain proposition,

```text
f.$contract_spec : ∀ params, Requires → Ensures (f params)
```

derived from `f.$contract` and checked by the kernel.
A theorem can apply it without unfolding the method (`docs/proving/proofs-that-work.md`, "A contract proved by a
script"), and the walker adds it as a hypothesis for each application of `f` in a leftover goal (#173).
So a pure callee is known to its callers through its `Ensures` only, not its body: U10's test
`Ensures(r => r == Positive(x))` fails since U11 for that reason.

## Partial operations in a `Spec` expression

`Spec` expressions translate as pure `Prop`s, so `Spec.Requires(a / b > 0)` would mean Lean's total division, which
returns 0 for `b = 0`.
Each operation in a `Spec` expression that can raise (`/`, `%`, `.Value`, a nullable member access, checked or `decimal`
arithmetic) adds a well-definedness obligation (KTD26):

```text
f.$wd_k : ∀ σ params [r], guards → ⦃⌜True⌝⦄ op σ args ⦃⇓_ => ⌜True⌝; allowed⦄
```

where `op` is the operation's raising model and `guards` are the conditions under which the enclosing `&&`, `||`, `?:`,
`??` and `Spec.Implies` evaluate it.
So design §5.2's `r is null || r.Id == id` is well defined: `r.Id` is read only when `r` is not null.
`Spec.Requires(a / b > 0)` fails at its line, and `Spec.Requires(b != 0 && b != -1 && a / b > 0)` proves
(`ADivisionInRequiresFailsAtTheSpecLineWithoutAGuardAndProvesWithOne`); the plan's scenario with only `b != 0` was wrong,
since `int.MinValue / -1` still overflows.
A call in a `Spec` expression to a pure method that has a `Spec.Requires` adds that precondition as a well-definedness
obligation under the same guards, so a contract never speaks about a callee outside the callee's own precondition.
A call to a raising method, or to a dependency, in a `Spec` expression is rejected at extraction (chapter 4).

Arithmetic in a `Spec` expression has C#'s meaning: `int` and `long` wrap.
`Spec.Ensures<int>(r => r == a + b)` wraps on both sides and says nothing about overflow, and "`a + b` fits in an `int`"
has no direct form; preconditions bound each operand instead.
Whether specs get an unbounded integer is the owner's open decision #183 (#160).

## Unsatisfiable contracts

A contradictory `Spec.Requires` would make every obligation of the method hold vacuously, with the same local effect as
an axiom; so would a contract-class member whose `Requires` and `Ensures` admit no result, for every caller after the
call (KTD25).
Each method's `Spec.Requires` prefixes get vacuity checks,

```text
f.$vacuous_k : ∀ params, R₁ → … → Rₖ → False
```

and so does each prefix of a contract member's `Spec.Requires` and `Spec.Ensures`, with the result universally bound
once an `Ensures` is among them.
The engine tries to prove each one, with intro and `omega` under 200,000 steps of tactic fuel: it only looks for an
easy refutation.
If it succeeds, the contract is unsatisfiable, and that is WRT0001 at the `Spec` call that made it so
(`AnUnsatisfiableRequiresIsReportedAtItsLine`; in the corpus, `Impossible` in `refuted/Contracts.cs` and the
`ICounter.Count` member in `refuted/Dependencies.cs`, whose caller `Tally.Size` is then skipped).
A check the engine cannot refute is not an error: proving satisfiability is not required, so a contradiction `omega`
does not find is not caught.

## A script instead of the default procedure

`[ProofFor(nameof(M))]` replaces the default procedure for `M`'s whole obligation with its script (KTD16).
The script starts at the triple, after the obligation's binders are introduced under the names the statement gives them;
`Tactic.VcGen()` runs the walker first and leaves its VCs to the rest of the script (chapter 7).
A script that fails is reported where it fails, as a theorem's is: `Kept` in `refuted/Contracts.cs` at its
`Tactic.Omega()`, and `TwiceScripted` in `refuted/Dependencies.cs`, which ends with goals left, at no line (the CLI
places it at the method). The plan expected the `Ensures` line; whether to map a script's last unsolved goal back to it
is the owner's open decision #224.
A `[ProofFor]` script cannot name a `[Theorem]` with `nameof`, because obligations run in the definition stage, before
theorems (docs/m5b/03).

## What the engine does with them

`src/Warrant.Engine/PipelineContracts.cs` runs a function's obligations after its definition, all in the unit's one
budget:

1. each vacuity check (KTD25);
2. each well-definedness obligation, proved by the default procedure and admitted;
3. the obligation itself, proved by the `[ProofFor]` script or by the default procedure (chapter 7), and admitted as
   `f.$contract`;
4. for a pure method with `Spec.Ensures`, `f.$contract_spec`, derived and admitted.

The first that fails is the unit's outcome, WRT0001 at the node that produced it (KTD18); the default procedure reports
every failing VC, not only the first (chapter 7).
A contract unit gets steps 1 and 2 only.

Obligations are cached with their unit, as decrease proofs are (docs/m5b/04): editing a `Spec.Ensures` changes the
unit's VIR hash and misses the cache, and editing or removing a contract-class member changes every caller's closure
hash, so they are verified again (#166).

A unit that depends on a method whose contract is not proved is skipped, with "it depends on X, whose contract is not
proved", even when it needs only X's definition (U10 chose the conservative rule: an unproved cached unit is not
admitted).
Whether a caller that needs only the definition should go ahead is the owner's open decision #219.
