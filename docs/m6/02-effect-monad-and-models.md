# 2. The effect monad and the models

> Part of the [M6 design](README.md). Decisions: KTD4, KTD5, KTD6, KTD13 and KTD23. Units: U3, U16.

M4's models are pure Lean functions: `int` addition is `Int32.add`, which wraps as the CLR does.
C#'s `checked` addition, `/`, `%`, `x.Value` and `Math.Abs` are not functions in that sense, because each can throw.
M6 gives them a monad to throw in, defines each as a program in it, and states what each does as a `Std.Do` triple.

## `ClrExn` and `ClrM`

`lean/Warrant/Effect.lean` (KTD4):

```lean
inductive ClrExn where
  | overflow            -- System.OverflowException
  | divideByZero        -- System.DivideByZeroException
  | nullReference       -- System.NullReferenceException
  | invalidOperation    -- System.InvalidOperationException: Value of a null Nullable<T>
  | assertFailed        -- a failed Spec.Assert (KTD16)
  | thrown (type : String)  -- an explicit throw, with the thrown type's key, e.g. "T:System.ArgumentException"
  | external            -- an exception propagated from a dependency (KTD9)

abbrev ClrM (σ α : Type) : Type := ExceptT ClrExn (StateM σ) α
```

`ClrM` is an abbreviation over Lean's own transformers, so `Std.Do`'s `WP` and `WPMonad` instances and its `@[spec]`
lemmas for `ExceptT` and `StateT` apply as they are; Warrant proves no instance of its own.

The world `σ` is opaque.
Every obligation quantifies over it (`∀ (σ : Type)`), model operations leave it unchanged, and a dependency's operation
may read and change it.
Without a world, a dependency would be a pure function of its arguments, and a proof could rely on two calls with equal
arguments returning equal results, which a real store breaks.
With it, two calls are unrelated unless a contract relates them; the corpus member that expects two `GetPayment(id)`
calls to agree is refuted for that reason (`tests/corpus/m6/refuted/Dependencies.cs`, chapter 8).

`ClrExn.Allowed` is the exception postcondition every contract states (KTD12, chapter 6): `thrown _` and `external` are
allowed, every other constructor is an implicit runtime exception and is not.
It has one equation per constructor (`ClrExn.allowed_overflow : ClrExn.Allowed .overflow = False`, …) for the VC simp
set.
`ClrExn.External` is the exception postcondition of a contract with `Spec.NoThrow` (#182, chapter 6): only `external`
is allowed. It has the same equations (`ClrExn.external_thrown : ClrExn.External (.thrown t) = False`, …), and
`ClrExn.allowed_of_external` states that every exception it allows `ClrExn.Allowed` allows too.

`ClrM.throw e` is `MonadExceptOf.throw e`, and `ClrM.throw_spec` is its triple.
`Std.Do.Spec.throw_ExceptT` states the same for every `ExceptT`, but at the `WP` instance a `WPMonad` instance gives,
which neither Lean's `apply` nor Warrant's unifies with the instance that instance resolution finds for `ClrM σ` and that
a contract's triple states (#211).
`ClrM.throw_spec` is stated at that instance.

## Null is a value

`T?` is `Option T`, `null` is `none`, and `T` to `T?` is `some` (KTD5).
Putting null in the monad too (an `OptionT` layer) would make "returned null" and "threw" one case of `Std.Do`'s
postconditions.
Two reads raise, and each is a model in `lean/Warrant/Nullable.lean`:

| C# | Model | Raises on null |
|---|---|---|
| `x.Value`, `(T)x` on `int?`, `long?`, … | `Nullable.value` | `invalidOperation`, as `Nullable<T>.Value` does |
| a `T?` used where a `T` is required: a call or constructor argument, a returned value, an explicitly typed local or an assignment to one, a `with` update, the receiver of `p.Id` or `with` | `Nullable.nonNull` | `nullReference` |
| `x ?? d`, `x.GetValueOrDefault()` | `Nullable.coalesce` (pure) | never |

The second row is the unwrap check node of KTD5.
Extraction decides where it goes from the declared types alone (chapter 4); Roslyn's nullable flow state is never
evidence, because `!`, suppressed warnings and oblivious code all defeat it.
A contract cannot allow `nullReference`, so the walker must prove each such value non-null from the path condition
(chapter 7): `Validate(payment)` after `if (payment is null) return …` is this case.

## The raising integer models

`lean/Warrant/Checked.lean` defines, for `Int32` and `Int64`, checked `+`, `-`, `*` and unary `-`, checked `long` to
`int` narrowing, `/` and `%`.
Each tests its throwing cases and then calls Lean's operation:

```lean
def div {σ : Type} (a b : Int32) : ClrM σ Int32 :=
  if b = 0 then ClrM.throw .divideByZero
  else if a = Int32.minValue ∧ b = -1 then ClrM.throw .overflow
  else pure (a / b)
```

C#'s `/` truncates, and so does Lean's `Int32.div` (`BitVec.sdiv`), but Lean's returns 0 for a zero divisor and wraps
`MinValue / -1`.
The model raises `divideByZero` first and `overflow` second, for `MinValue / -1` and `MinValue % -1` alike, which the CLR
throws even in unchecked code (KTD6).
The C# specification ties `x % y` throwing to `x / y` throwing; the agreement rows pin it on the runtime they run on.

Each model has an `@[spec]` lemma whose precondition, at world `s`, is one proposition: for each throwing case, the
exception postcondition at that exception and the unchanged world, and otherwise the normal postcondition at Lean's
result:

```lean
@[spec] theorem div_spec {σ : Type} (a b : Int32) {Q : PostCond Int32 (.except ClrExn (.arg σ .pure))} :
    Triple (div a b)
      (fun s => ⟨(b = 0 → (Q.2.1 .divideByZero s).down) ∧
        (¬b = 0 → a = Int32.minValue ∧ b = -1 → (Q.2.1 .overflow s).down) ∧
        (¬b = 0 → ¬(a = Int32.minValue ∧ b = -1) → (Q.1 (a / b) s).down)⟩) Q
```

A proposition, rather than an `if` over assertions, is what the VC simp set reduces to a goal `omega` reads (chapter 7).
The definitions are trusted: they are the claim that this is what C# does (design §6.2).
The spec lemmas are proved in Lean and checked again by Warrant's kernel with the bundle.

## Modelled `Math` members

The modelled BCL members are a table in Extraction mapped to library definitions in Semantics (KTD23):
`src/Warrant.Extraction/ModelledMembers.cs` lists `Math.Min`, `Math.Max` and `Math.Abs` on `int`, `long` and `decimal`.
Adding one means a table row, a library definition, a CLR-agreement row and a corpus entry.

`lean/Warrant/Math.lean` defines `Min` and `Max` on `int` and `long` as .NET does (`a <= b ? a : b`, `a >= b ? a : b`),
pure, each with a `_def` equation such as `Warrant.Int32.max_def`.
`Math.Abs` on `int` and `long` is a `ClrM` model that raises `overflow` for `MinValue` in any context, as the CLR's
does, with its `@[spec]` lemma.
Its throwing members are listed again in `Warrant.Vir.Effects.ThrowingModelledMembers`, which effect inference reads
(chapter 4); the extraction table must contain them.
`decimal`'s three members are pure (chapter 3).

## Agreement with the CLR

`tests/Warrant.Semantics.Tests/ClrAgreementTests.cs` runs every new model in the kernel and the same operation on the
CLR, on boundary values and 150 random cases per row with the pinned seed, and compares (R5).
A raising model runs from an arbitrary world (σ and the state bound by lambdas the kernel opens), and its `Except`
component is compared: a value, or which exception.
The generators include zero divisors, `MinValue` with `-1`, and null one time in five for nullable operands.
`M6ExitTests.EveryNewModelOperationAgreesWithTheClrOnGeneratorsWithZeroDivisorsMinValueByMinusOneAndRescaledDecimals`
(in `Warrant.Semantics.Tests`) is the exit criterion's fact for this.

## Rules `Std.Do` lacks

`Std.Do` has no triple rule for `if`.
`Effect.lean` adds two, proved in Lean (KTD13):

```lean
theorem Triple.ite … (ht : c → Triple t P Q) (he : ¬c → Triple e P Q) : Triple (if c then t else e) P Q
theorem Triple.dite … (ht : ∀ hc : c, Triple (t hc) P Q) (he : ∀ hc : ¬c, Triple (e hc) P Q) : Triple (dite c t e) P Q
```

The walker applies them at a branch and gets one goal per branch, with the condition or its negation as a hypothesis.
Chapter 7 lists the walker's other rules, which U11 re-stated at `ClrM σ` in `lean/Warrant/Vc.lean`.

## The go/no-go checkpoint

The plan made U3 a gate: before contracts were extracted or translated, three obligations built by hand had to be
proved by Warrant's own `Apply`, simp and `omega` and admitted by its kernel (`EffectCheckpointTests`):
`Ratio`'s division under `b != 0 && b != -1`, a guard with an explicit throw, and a D9-shaped triple with a dependency
`get` and its contract hypothesis used at the call.
If they could not be closed, the plan would have moved to its Alternative C, a `wp` calculus over plain `Prop`s.

All three closed, so M6 continued on `Std.Do`.
Two things had to change on the way, and both reproduce with Lean 4.35's own `apply`:

- `Std.Do.Spec.throw_ExceptT` does not unify with the `WP` instance of `ClrM σ` (#211), hence `ClrM.throw_spec`.
- `PostCond.entails.mk` leaves `(f, g).1 a`, which needs a reduction with no lemmas (`dsimp only`) before the
  consequence rule (#212); the walker's light reduction does this (chapter 7).

Warrant's `Apply` also had to synthesize instance-implicit arguments, as Lean's `synthAppInstances` does
(`synthAssignedInstances := true`), in place of its old "instance synthesis is not available yet" failure.
