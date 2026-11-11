# 5. The monadic translation

> Part of the [M6 design](README.md). Decisions: KTD4, KTD5, KTD9, KTD11, KTD16 and KTD22. Units: U9, U19 (dependencies
> and `async`), U21 (`decimal`, chapter 3).

Semantics is trusted: its translation is the claim that a Lean term behaves as the C# does.
M6 adds a second translation beside M4's, and keeps M4's wherever it can.

## Two translations, chosen by effect inference

A unit is translated into `ClrM` exactly when effect inference (chapter 4) says it can raise (KTD11):

```text
f : ∀ {σ : Type} params, ClrM σ R          -- a raising unit
f : params → R                            -- every other unit, as in M4 and M5a
```

Every other unit keeps its M4 translation, so R14 holds by construction: the M4 corpus pins and a new M5a pin, recorded
before any change, still match byte for byte.
Translating every unit monadically would have changed every M4 and M5a declaration for no gain (the plan's Alternative
Approaches).

`/` and `%` by a literal other than 0 and -1 cannot throw, so they stay pure and use Lean's `Int32`/`Int64` division,
which agrees with C#'s there.
`Math.Min` and `Math.Max` are pure models.
A theorem statement may use both (`Prove.That(a / 2 <= a)`), and `omega` reads them through chapter 1's bridges.

## Programs

A raising unit's body becomes a `ClrM σ` program built from `pure` and `>>=` through the `Monad` instance, exactly as
Lean elaborates them, so the walker (chapter 7) meets the terms Lean would produce.

- **Evaluation order.** Operands and arguments are bound left to right, and an operator's own check runs after both
  operands, so the left operand's exception wins, as in C# (#108).
- **Short circuits.** `&&` and `||` bind their right operand only when it is evaluated; `&` and `|` bind both.
- **Raising operations** map to chapter 2's models: checked `+ - *` and negation, `/`, `%`, checked narrowing
  (`toInt32Checked`) and `Math.Abs` on `int` and `long`; `decimal` `+` and `-` to chapter 3's.
- **`throw new T(...)`** is `ClrM.throw (ClrExn.thrown "T:…")`, carrying the thrown type's key. The exception's
  arguments are not modelled; extraction only allows constants and parameters there, so evaluating them cannot fail.
- **`Spec.Assert(c)`** is a check node, `(if c then pure () else ClrM.throw .assertFailed) >>= fun _ => rest` (KTD16).
  The model differs from C# only on a path where the assertion fails, which the method's obligation excludes.
- **Branches.** `if` and `?:` keep their join points. A raising `switch` discriminant is bound; a pure discriminant
  that is not a variable is let-bound.
- **Nullable values** (KTD5). `T?` is `Option T`; `null` is `none`; `T` to `T?` is `some`; `is null` is
  `Option.isNone`; `.Value` and `(T)x` are `Nullable.value`; the non-null unwrap is `Nullable.nonNull`; `??` is
  `Nullable.coalesce`, or an `Option.rec` with a `ClrM` motive when its right side can raise.
- **Calls.** A call to a raising unit is `f σ args`, bound. A call to a pure unit with `Spec.Requires` is
  `pure (f args)`, bound when it is not in tail position, so the walker sees the call and can ask for the callee's
  precondition there; the walker recognises the callee by its head constant (chapter 7).

Programs are checked against the CLR by running them in the kernel from an arbitrary world and comparing the `Except`
part (#110): the differential tests of chapter 8 do this for every M6 corpus function.

## Dependencies and `async` (U19)

A method that calls dependency members is a function of one operation per (dependency, member) pair it calls, bound
after the world and before its own parameters (KTD9). For the running example, in outline:

```text
ProcessPayment : ∀ {σ : Type}
    (store_GetPayment : Int32 → ClrM σ (Option Payment))
    (store_SavePayment : Payment → ClrM σ Unit)
    (paymentId : Int32), ClrM σ Result
```

An external call is the bound operation applied to its arguments.
It runs in the world like any other step, so it may read and change it, and a dependency called twice threads the world
from the first call to the second (a kernel-evaluated test with a counting mock pins this).

`async` is sequencing (KTD22): a `Task<T>` or `ValueTask<T>` result is a `ClrM σ T` program, and a `void`, `Task` or
`ValueTask` one a `ClrM σ Unit` program; `await` binds the awaited call's program, whether it is a dependency call, a
raising verified method or a pure one, and the VC walker checks a verified callee's `Spec.Requires` there as at any
other call (#228).
A discarded call (`F(x);`) is bound and its value dropped.

Translation refuses to translate a call to a method that has dependencies of its own; extraction already rejects it.

## What does not translate

- A record with a nullable field (#218): the record's `$eq` is built field by field and has no case for an
  `Option` field. Extraction accepts such records since U17; translation stops with an error, never a silent pass.
- A contract unit is never a definition, since nothing in a contract class runs: it translates to its checks only
  (chapter 6).
