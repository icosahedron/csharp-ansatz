# 6. Theorems

> Part of the [M4 design](README.md). Decisions: KTD8, KTD12, KTD22 in the [plan](../plans/2026-11-02-1245-feat-m4-pure-subset-plan.md).

In M4 a theorem is a claim about concrete values, written as a `[Theorem]` method with no parameters:

```csharp
[Theorem]
static Proof CappedAtTheLimit() =>
    Prove.That(PayoutRules.Payout(loss: 1000, deductible: 250, limit: 500) == 500);
```

Theorems with parameters need tactics, so they wait for M5a; extraction rejects them with WRT0002.
M4 does not search for proofs: a claim with no free variables can be checked by computation alone, and the engine emits one of two fixed proof terms and lets the kernel decide.

## The statement

The argument of `Prove.That` is translated as a condition (chapter 5), which gives a proposition `P` and a `Decidable P` instance `D`.
For `CappedAtTheLimit`, writing `Payout` for the full name `Cs.Payouts.PayoutRules.Payout(System.Int32,System.Int32,System.Int32)`:

```lean
P := @Eq Int32 (Payout 1000 250 500) 500
D := instDecidableEqInt32 (Payout 1000 250 500) 500
```

`P` is the theorem's type, and its name is `Cs.Payouts.PayoutTheorems.CappedAtTheLimit` (chapter 5).
The statement is trusted: if `P` said something other than the C# claim, a proof of it would prove the wrong thing.
So statements are built by `Warrant.Semantics`, with the rest of the trusted translation (KTD22).

Since the M6 follow-ups (#236), the statement is translated as a `Spec` expression is (docs/m6/06): its `+`, `-`, `*`
and unary `-` on `int` and `long` in C#'s default context must not overflow, and a call in it to a pure method with
`Spec.Requires` must be within that precondition.
Each is a well-definedness theorem `T.$wd_k`, proved by M6's default procedure before the theorem, whatever proves the
claim; the theorem is proved only when every one of them is, and one that fails is WRT0001 at the operation, `well-definedness of a Spec expression`.
The statement's own term does not change.
An M4 statement such as `Increment(int.MaxValue) == int.MinValue` has no arithmetic of its own (the wrap is in the
method's body, which #244 covers) and is unaffected; a statement that wraps on purpose writes `unchecked(...)`.

## The two proofs

The reference says that without `.By`, the translator tries `rfl` and then `decide` ([reference.md](../proving/reference.md)).
In M4 those are two terms, built by the proof emitter in `Warrant.Engine`, which is untrusted: the kernel checks whatever it emits, so a bug there can make a true claim fail but never a false one pass.

1. **`rfl`**, only when `P` is an equation `@Eq T a b`, using its left side `a`:

   ```lean
   @Eq.refl T a
   ```

   This has type `a = a`, so the kernel accepts it as a proof of `a = b` exactly when `a` and `b` are definitionally equal, which for closed terms means they compute to the same value.
2. **`decide`**, for any `P`:

   ```lean
   @of_decide_eq_true P D (@Eq.refl Bool Bool.true)
   ```

   `of_decide_eq_true` turns a proof that `decide P` is `true` into a proof of `P`.
   The inner `Eq.refl` has type `true = true`, so the kernel accepts the term exactly when `Decidable.decide P D` computes to `true`.

Both were checked against Lean 4.35.0: Lean's own `rfl` elaborates to `Eq.refl` of the left side, and its `decide` to the second term wrapped in an `id` that only ascribes a type.
The hand-built forms are accepted by Lean, by Warrant's kernel and by `lean-replay`, and neither depends on any axiom; a deliberately mismatched proof was rejected by both kernels.

The engine fills only the proof slot of the theorem declaration that `Warrant.Semantics` built (KTD22).
It reports a theorem as proved only when the kernel admits that exact declaration, so a bug in the engine that put a different type on the theorem, `a = a` for instance, would be reported as a failure, not as a proof.
In Lean 4.35.0 `Decidable` is a structure with one constructor, `Decidable.intro (decide : Bool) (reflects_decide : …)`, and `isTrue`/`isFalse` are definitions, not constructors.
The proof terms above do not depend on that shape, but any code that matches on a `Decidable` value must use the new one.

The kernel computes by unfolding: `Payout 1000 250 500` unfolds to `ite`, the `ite`'s instance `Int32.decLe 1000 250` reduces through `BitVec` to `Nat` comparisons on literals, and the arithmetic reduces to `Nat` addition and modulus on literals, which the kernel performs directly.
Nothing on that path is `opaque` or `implemented_by`, and Warrant's kernel does not support native reduction, so a proof never depends on compiled code.
The research run checked 315 such theorems over `Int32`, `Int64`, records and enums in Warrant's kernel in about 1.5 seconds.

## Outcomes

Each theorem ends in exactly one outcome:

| Outcome | When | Reported as |
|---|---|---|
| Proved by `rfl` | The kernel accepts the first term. | proved |
| Proved by `decide` | The first term was not tried or was rejected, and the kernel accepts the second. | proved |
| False | Both were rejected, and `Decidable.decide P D` computes to `Bool.false`. | WRT0001, "the claim is false" |
| Not decided | Both were rejected, and `decide P D` does not reduce to `Bool.false` within the fuel limit. | WRT0006 |
| Failed | Translation could not build the declaration, or the kernel admitted the theorem with a type other than its statement. | `failed`, with the reason |
| Skipped | A unit the theorem depends on failed or was skipped. | `skipped`, naming the dependency |

Functions and types end in `translated`, `failed` or `skipped` in the same way.

Telling "false" from "not decided" takes one more computation: the engine asks the kernel to reduce `decide P D` to weak head normal form.
A false claim is not a crash or a timeout, and it should read like the counterexample the [tutorial](../proving/tutorial.md) promises.
So for a false claim that is a single `==`, `<`, `<=`, `>` or `>=`, the message also gives the value each side computes to, read back from the kernel (chapter 7).
This is `warrant translate tests/corpus/m4/refuted`, which exits 1, as it runs since M5a:

```text
translating 1 file(s) in tests/corpus/m4/refuted
  Corpus.Refuted.Increments.Increment(int)  translated
  Corpus.Refuted.Increments.NeverWraps()    false
  Corpus.Refuted.Increments.WrongSum()      false
tests/corpus/m4/refuted/Increment.cs(12,18): error WRT0001: Theorem 'Increments.NeverWraps()' is false.
  Claim:  Increment(int.MaxValue) > int.MaxValue
  Values: Increment(int.MaxValue) = -2147483648, int.MaxValue = 2147483647
tests/corpus/m4/refuted/Increment.cs(15,18): error WRT0001: Theorem 'Increments.WrongSum()' is false.
  Claim:  Increment(2) == 4
  Values: Increment(2) = 3, 4 = 4
3 unit(s): 1 translated, 0 proved, 2 false, 0 unproved, 0 undecided, 0 internal error(s), 0 failed, 0 skipped; 2 error(s), 0 warning(s)
```

In M4 the message named the theorem by its short name, `'NeverWraps'`, and the summary had no `unproved` or `internal error(s)` counts; M5a added both (docs/m5a/04).

The location is the theorem's name in its declaration (`NeverWraps` starts at line 12, column 18), and the claim is the source text of the `Prove.That` argument.
Read-back has limits, and the message shows them rather than guessing:

- It reads `int`, `long` and `bool` values, and open-enum values, which it prints as their integer value.
  A side that is a record or a closed-type value, or the two sides of a record or closed-type `==`, is printed as `unknown`, because `$eq` and `$index` compare the operands rather than producing them.
- A false `!=` claim, and any claim that is not a single comparison (`&&`, `Spec.Implies`, a `bool` call), has no `Values` line.

Running out of fuel is never treated as success (design §7.1, WRT0006).

## What gets admitted

A proved theorem is a `TheoremDecl` added to the same environment as the definitions it mentions, and it is exported with them (chapter 7).
A false or undecided theorem is not admitted, and it does not stop the other units: each unit's outcome is independent.
