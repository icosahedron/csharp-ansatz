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
(KTD11), when it calls a function that has a `Spec.Requires` (KTD12), or when its body has default-context `int` or
`long` arithmetic (#244, below):

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
  excluded, so the proof must show none can happen under `Requires`. With `Spec.NoThrow` it is `ClrExn.External`,
  which excludes the explicit throws too (below).
- The `WP` instance is the one instance resolution finds for `ClrM σ`.

A pure unit without a contract and without implicit arithmetic gets no obligation, so its declarations are M4's and
M5a's. One whose body has `+`, `-`, `*` or unary `-` on `int` or `long` in C#'s default context gets one since #244,
whose triple is trivial and whose well-definedness obligations say the arithmetic does not overflow (below); a
recursive method included, after its equation lemma.

Contracts are total about implicit exceptions and partial about explicit ones.
`Ensures` holds on every normal return, and a path that ends in an explicit `throw` or a dependency's exception
satisfies the triple without saying anything.
So a method that throws on every path proves any `Ensures` (`Closed` in `tests/corpus/m6/accepted/Effects.cs`), and the
report lists each such path (KTD20, chapter 8).
Making every reachable explicit throw fail the build would reject ordinary argument validation, so that is opt-in.

## `Spec.NoThrow`: no explicit throw under `Requires` (#182)

`Spec.NoThrow()` states that none of the method's explicit throws is reachable under its `Requires`.
It is a leading `Spec` statement, after every `Spec.Requires` and before any `Spec.Ensures`, at most once (chapter 4).
For a method that can raise, the exception postcondition becomes `ClrExn.External`, which allows only `ClrExn.external`,
an exception propagated from a dependency:

```text
f.$contract : ∀ (σ : Type) params,
  ⦃⌜Requires⌝⦄ prog ⦃⇓r => ⌜Ensures r⌝; fun e => ⌜ClrExn.External e⌝⦄
```

Nothing else in the statement changes, and a method without `Spec.NoThrow` translates as before (`TheM6CorpusTranslates`
checks that no other obligation of the M6 corpus mentions `ClrExn.External`;
`NoThrowStatesTheExternalExceptionPostconditionAndChangesNothingElse` compares a method with its twin without it).
So the proof must show every `throw` statement and `throw` expression unreachable under `Requires`, and one that is not
fails the build at the `throw` (chapter 7) instead of being listed as a `MayThrow` (chapter 8).
`Quotient` in `accepted/Contracts.cs` proves; its twin `QuotientOfAny` in `refuted/Contracts.cs`, without `b != 0` in its
`Requires`, fails at its `throw`.

- A pure method raises nothing, so `Spec.NoThrow` holds of it already: it is accepted and its obligation is the one
  without (`NoThrowOnAPureMethodChangesNothing`).
- A method with dependencies still allows their exceptions, and its hypotheses about them say so: under `Spec.NoThrow`
  each contract hypothesis's exception postcondition is `ClrExn.External` too, since an exception from a dependency is
  `ClrExn.external` (KTD12). With `ClrExn.Allowed` there, a dependency's contract would allow it an explicit throw that
  the method's own contract does not, and no method with dependencies could prove `Spec.NoThrow`. This narrows the
  premises of that one method's theorem only; no other theorem uses them.
- A caller without `Spec.NoThrow` uses a NoThrow callee's contract by consequence, through
  `ClrExn.allowed_of_external : ClrExn.External e → ClrExn.Allowed e`. A caller with `Spec.NoThrow` needs the same of
  every raising verified callee: a callee without it may throw explicitly, which fails at the call.
- `Spec.NoThrow` in a `[ContractFor]` class member is rejected: it is for a verified method's own body, and a
  dependency's exceptions are always allowed.

`ClrExn.External` and its equations are in `lean/Warrant/Effect.lean`, and the walker's rules for a NoThrow callee
(`Vc.callExternal`) and for a pure callee under a NoThrow caller (`Vc.callPure`) in `lean/Warrant/Vc.lean`.

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

Arithmetic in a `Spec` expression must not overflow (owner decision #183): `+`, `-` and `*` on `int` and `long`, and
unary `-`, are partial there even where C# would wrap, since an overflowing spec is almost always a wrong one.
Each adds a well-definedness obligation whose program is the checked model (`Warrant.Int32.addChecked` and so on), under
the same guards as the other partial operations; the value the spec reads is the wrapped one, which agrees with the
mathematical one wherever the obligation holds.
So `Spec.Ensures<int>(r => r == a + b)` fails at its `a + b` with nothing bounding `a` and `b`, and proves with
`Spec.Requires(a < 1000 && a > -1000 && b < 1000 && b > -1000)`
(`ArithmeticInEnsuresThatCanOverflowFailsAtTheEnsuresLineAndProvesWhenBounded`; in the corpus, `SumUnbounded` in
`refuted/Contracts.cs`).
Specs keep C#'s bounded types: there is no unbounded integer and no widening to `long`.
Only C#'s default context has the obligation: arithmetic inside an explicit `unchecked(...)` or `unchecked { }` (VIR
`unchecked`, chapter 4) wraps on purpose and has none, and `checked` arithmetic is a partial operation as before
(`ExplicitUncheckedArithmeticInASpecExpressionWrapsWithNoObligation`).
An explicit unchecked cast such as `(int)l` is left as written, since a narrowing cast is a deliberate truncation.
The rule covers `Spec.Requires` and `Spec.Ensures`, in a method and in a contract-class member, and a `Spec.Assert`'s
condition (#235, below).
A callee's `Spec.Requires`, stated at a call site in a caller's `Spec` expression, adds no obligation of its own there:
the callee's own `$wd` obligations cover it.

**`Spec.Assert` conditions (#235).** A `Spec.Assert` is a statement inside the program, and its condition's
arithmetic stays the wrapping operation there: the CLR compiles `Spec.Assert` out, so a checked model would raise where
the CLR does not, and the differential harness (whose `Contracts.Average` comparison relies on the wrap) would disagree.
Instead its default-context `+`, `-`, `*` and unary `-` get `$wd` obligations of the same kind as a `Spec.Ensures`'s,
numbered after the contract's own: the method's program is translated once more, by `AssertObligations`, with each
`Spec.Assert`'s condition translated as a `Spec` expression, and each obligation is closed over the world, `self` and
the parameters, the values bound by `bind` and join points before the `Spec.Assert`, and the facts known there: the
`Spec.Requires`, the condition of each `if` branch taken, and the conditions of the `Spec.Assert`s before it, then the
guards inside the condition; a local's `let` is unfolded into its value.
A value bound by an implicit operation (#244, below), such as `var s = a + b;`, comes with what its model guarantees
wherever the program continues, since the model continues only where the exact result is in range: `s = a + b` and
`s.toInt = a.toInt + b.toInt` (#246; likewise for `-`, `*`, unary `-` and `long`), so `Spec.Assert(s - b == a)` proves
under bounds on `a` and `b`.
What a VC walk would learn from a callee's `Spec.Ensures` or a model's case is not among the facts, so assert the fact
first (`Spec.Assert(b >= 0 && b <= 100)`) and the next `Spec.Assert` may use it.
The program, its definition and the differential harness are unchanged.
A failing obligation is reported at the operation with this chapter's wording
(`ArithmeticInASpecAssertThatCanOverflowFailsAtTheOperationAndProvesWhenKnownBounded`,
`ASpecAssertsArithmeticHasAnOverflowObligationUnderWhatIsKnownThereAndTheProgramIsUnchanged`,
`ASpecAssertAfterImplicitArithmeticKnowsTheBoundValueAndItsExactValue`).

**Theorem statements (#236).** A `[Theorem]`'s statement follows the same rule, since theorems and code should agree
(owner decision 2026-11-12): it is translated with a world `σ` and a `SpecState` of its own, so its default-context
arithmetic and its calls to pure methods with `Spec.Requires` get `T.$wd_k` obligations over `σ`, the theorem's
parameters and the guards, including `Spec.Implies` and the variable of each enclosing `Spec.ForAll` or `Spec.Exists`
(the obligation holds for every value of it).
The statement itself is the same term as before.
The engine proves each by the default procedure, as a contract's are, before and independently of the theorem's script,
`rfl` or `decide`; the theorem is proved only when all of them are, its certificate holds them before the theorem, and
one that fails is the theorem's WRT0001 at the operation with this chapter's wording
(`ArithmeticInATheoremThatCanOverflowFailsAtTheOperationAndProvesWhenBounded`,
`ATheoremStatementsArithmeticHasAnOverflowObligationUnderItsGuardsAndBinders`).
As for contracts, they are not listed in the assumption report.

**Method bodies (#244).** The one rule reaches a verified method's own code (owner decision 2026-11-12): implicit
`+`, `-`, `*` and unary `-` on `int` and `long` (C#'s default context, VIR `wrap`, which `++`, `--` and compound
assignment also are) must not overflow, explicit `unchecked(...)` and `unchecked { }` wrap with no obligation, and
`checked` raises as before. The value is still the wrapped one, the CLR's, so the model stays faithful; the proof shows
the wrap never happens. A failure is WRT0001 at the operation, `arithmetic overflow` (chapter 7).

- *A pure method* keeps its definition. `OverflowObligations` translates its body once more, as the definition is
  translated but with the whole body treated as a `Spec` expression, and each implicit operation records an
  obligation of kind `NoOverflow`, `f.$wd_k` after the contract's own `Spec` obligations:

  ```text
  f.$wd_k : ∀ σ self params [join-point parameters], facts → guards → ⦃⌜True⌝⦄ checked op σ args ⦃⇓_ => ⌜True⌝; allowed⦄
  ```

  The facts are what the path to the operation knows: the `Spec.Requires`, the condition of each `if` branch taken and
  of each `switch` section taken over an integer or open enum, and over a closed enum that the scrutinee is one of the
  members the section takes, `s = T.A ∨ s = T.B` (#258); the guards are those inside the expression (`&&`, `||`,
  `?:`, `??`, a switch expression's arm, over a closed enum the members it is the first to cover); a local's `let` is
  unfolded into its value.
  A join point's parameters (a value merged after an `if` that changes two locals, or a `switch` with a `return` in
  it) are known by their value on each incoming path (#255): the branches are translated before the join point's
  body, each jump records `∃ ys, facts ∧ x₁ = v₁ ∧ …` over the facts its path added since the branch point and the
  values it passes (an `int` or `long` as `x.toInt = v.toInt`), with `ys` the parameters of join points inside the
  branch, and the join point's parameters are bound with the disjunction of those as a fact. Each disjunct holds on its
  path, and the body runs only after one of the jumps, so the fact holds wherever the body's obligations are used. The
  term this translation builds is discarded; the definition's join point is unchanged. A pure callee's
  `Spec.Ensures` is known through its `f.$contract_spec`, which the default procedure adds for every application of it
  in a goal (chapter 7). A call of a recursive method to itself is its own constant, which the obligations, admitted
  after the definition, can name; nothing is known of its value, so arithmetic on a recursive result fails unless it
  is `unchecked` (a recursive method has no `Spec.Ensures` yet). A recursive method may state `Spec.Requires` (#256):
  its body's obligations assume it, as any method's do, and each call of the method to itself records an obligation
  of kind `CalleePrecondition`, the precondition at the call's arguments under the facts of the path to it, proved by
  `omega` as a callee precondition in a `Spec` expression is. Every outside caller is checked at its call (the call
  makes it raise, KTD11), and a call to itself does not make the method raise. So by well-founded induction on the
  `Spec.Decreases` measure every execution that starts within the `Spec.Requires` stays within it, and the body's
  obligations hold of each. These obligations are stated whenever the method calls itself, even with no implicit
  arithmetic. Once an operation's obligation holds, its exact value
  `(a op b).toInt = a.toInt op b.toInt` is a fact for the obligations after it on the same path, inside the guard it
  was under; `omega` reasons through the wrap-around's `Int.bmod` only by its real shadow, which cannot close nested
  arithmetic such as `a * 3 - b` even under tight bounds (`ANestedProductIsBoundedThroughItsExactValueNotItsWrapAround`).
  The same facts serve a `Spec` expression's arithmetic.
  `omega` reads only linear arithmetic: a product of two variables is never bounded by it, so such a product fails
  unless a `[ProofFor]` script proves it (GitHub #257). `unchecked` states that wrapping is intended; it is not the
  way around a gap. The other gap: a recursive call's result, which needs `Spec.Ensures` on a recursive method.
  `AJoinPointsParametersCarryTheirValueOnEachIncomingPathIntoLaterObligations`,
  `AClosedEnumSwitchArmKnowsItsCase` and `ARecursiveMethodsRequiresIsAssumedByItsBodyAndCheckedAtEachRecursiveCall`
  (`OverflowGapTests`) each pair a bound that proves with a twin where the same fact would be wrong and fails.
- *A method that can raise* has the operation as a site of its program instead: `Warrant.Int32.addImplicit σ a b` and
  likewise for `-`, `*`, unary `-` and `long` (`lean/Warrant/Checked.lean`), which is `pure (a + b)` where the exact
  result is in range and `throw .assertFailed` where the CLR would wrap. `assertFailed` is not allowed, so the contract
  obligation itself requires the operation not to overflow, and the VC walker proves it with everything it knows there:
  the path, a callee's `Spec.Ensures` and a dependency's contract (closed obligations, as for `Spec.Assert` conditions,
  would miss these). The `@[spec]` lemma gives the walk the exact value on the normal path. The differential harness
  skips an input whose model fails a `Spec.Assert` (#186), so it still compares every input where no implicit
  operation overflows, and the model agrees with the CLR wherever it returns. A `Spec.Assert`'s condition is not a
  site: it keeps its own obligations (#235, above).

Callers of a method whose obligation fails are skipped (#219), as for any contract that is not proved
(`ArithmeticInAPureBodyThatCanOverflowFailsAtTheOperationAndProvesWhenBounded`,
`ARecursiveMethodsArithmeticHasObligationsAndItsRecursiveResultIsUnknown`,
`ArithmeticInABodyThatCanRaiseIsCheckedByTheWalkWithEverythingItKnows`,
`APureBodysArithmeticHasAnOverflowObligationUnderThePathToItAndTheDefinitionIsUnchanged`,
`ImplicitArithmeticInARaisingBodyIsASiteThatFailsAsAnAssertWhereTheClrWouldWrap`).

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
A script need not run it (`Tactic.Apply(Lean.Const("Warrant.Vc.pre"))` and the other `Warrant.Vc` rules work by hand);
the assumption report lists the same exceptions and callee contracts either way (chapter 8, #229).
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
