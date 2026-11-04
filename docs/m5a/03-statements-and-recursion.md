# 3. Statements and recursion

> Part of the [M5a design](README.md). Decisions: KTD14 to KTD17 in the [plan](../plans/2026-11-03-0838-feat-m5a-meta-tactics-plan.md).

Both halves of this chapter are trusted translation (M4 KTD22): a wrong statement proves the wrong claim, and a wrong definition models the wrong method.
The first half is short, because quantified statements reuse M4's conditions.
The second half is recursion, where the term Lean builds turns out to decide how Warrant tests it.

## Quantified statements

M4 translates a claim to a condition: a proposition `P` and a `Decidable P` instance (M4 KTD8).
A theorem's parameters become fvars while the claim is translated, then outer `∀` binders in order (KTD17):

```lean
-- AlwaysLarger(int x): Increment(x) > x
∀ (x : Int32), @GT.gt Int32 instLTInt32 (Increment x) x

-- ValidImpliesPositive(Payment p)
∀ (p : Cs.Claims.Payment),
  @Eq Int32 (Validate p) Cs.Claims.PaymentResult.Valid →
  @GT.gt Int32 instLTInt32 p.Amount 0
```

An open enum such as `PaymentResult` is an `abbrev` for its underlying type, and `==` on it compares at that type, `@Eq Int32 …`, exactly as M4 translates it (M4 docs/m4/05).

`Spec.ForAll<int>(y => p)` becomes `∀ (y : Int32), P` and `Spec.Exists<int>(y => p)` becomes `@Exists Int32 (fun y => P)`.
A `∀` has no `Decidable` instance in general, so the condition's instance becomes optional.
M4's `rfl` and `decide` proofs need one, so the engine tries them only when the statement has one; a parameterless M4 theorem therefore translates and proves exactly as before.

In a statement that has parameters or contains `Spec.ForAll` or `Spec.Exists`, `>` and `>=` become `GT.gt` and `GE.ge`, the forms Lean elaborates, so that goals read like the C# and `simp`'s `gt_iff_lt` and `ge_iff_le` match them.
A closed statement and every function body keep M4's form, `a > b` as `b < a` with `LT.lt` and `LE.le`, so every M4 theorem translates to exactly the term it did before.
Display names are C# throughout; `Cs.Claims.PaymentResult.Valid` prints as `PaymentResult.Valid` in goals (chapter 4).

## Recursion: the term

`Sum` from the README:

```csharp
[Verified]
public static int Sum(int n)
{
    Spec.Decreases(n);
    if (n <= 0) return 0;
    return n + Sum(n - 1);
}
```

A recursive method cannot be translated to a plain definition: `Sum`'s body would mention `Sum`, which the kernel does not admit for a safe definition.
Lean compiles such a definition to a fixpoint combinator.
For a measure into `Nat`, which `termination_by n.toInt.toNat` is, Lean 4.35.0 does not use `WellFounded.fix` but `WellFounded.Nat.fix` (*ran*: `#print` of the elaborated definition).
Warrant builds the same term directly (KTD14):

```lean
Cs.Sums.Sum(System.Int32) :=
  @WellFounded.Nat.fix Int32 (fun _ => Int32)
    (fun n => Int.toNat (Int32.toInt n))                       -- the measure, from Spec.Decreases(n)
    (fun n rec =>
      @dite Int32 (n ≤ 0) (Int32.decLe n 0)
        (fun h => 0)
        (fun h => n + rec (n - 1) (Sum.$dec_1 n h)))            -- the call, with its decrease proof
```

Four choices are in that term:

- **`Nat.fix`, not `WellFounded.fix`.**
  `WellFounded.fix` recurses on an accessibility proof, which the kernel cannot reduce, so `Sum 5` would not compute.
  `Nat.fix` recurses on a `Nat` counter instead, so the kernel evaluates `Sum 5` to `15` (*ran*: Lean's kernel proved `f 1000 = 1000` by evaluation in 1.2 s, and `f 100000 = 100000` in 31.6 s).
  Warrant's kernel does the same at about 540 fuel per level of recursion, linearly: `Sum 1000` took 530,058 fuel and about 0.6 s in a Debug build (*ran*, `tests/Warrant.Engine.Tests/Differential/README.md`).
  That keeps M4's way of testing translated definitions working for recursive ones (chapter 8).
  A lexicographic measure would need `WellFounded.fix` and would not compute (*ran*), so M5a accepts one integer measure only.
- **The measure clamps.**
  `Int.toNat` maps every negative integer to 0, which is sound: a call from a state whose measure is already 0 or less would need a measure below 0, so its obligation cannot be proved.
  The guard `n <= 0` is what makes `Sum`'s obligation provable.
- **`dite`, not `ite`, on the path to the call.**
  The decrease proof needs to know `¬ n ≤ 0`, which only a dependent `if` provides, as `h`.
  Lean inserts it the same way (its `wf_preprocess` lemma `ite_eq_dite`).
  The same holds for the tests of a `switch` over an integer or open enum, which translate to a chain of `if`s: a level that leads to a recursive call is a `dite`.
  Elsewhere, and in the equation lemma, Warrant keeps M4's `ite`; the two are definitionally equal, so the kernel bridges them.
- **Several parameters pack into a `PSigma`, read by projections.**
  `F` takes one argument, so `g(a, b)` becomes `Nat.fix … (fun x rec => … x.1 … x.2 …) ⟨a, b⟩`.
  Lean packs the same way but reads the pair with `PSigma.casesOn`, which forces it to push `rec` into every branch and undo that when proving equations.
  Projections avoid both, and Lean's kernel accepted the projection form (*ran*).

## Decrease theorems

Each recursive call site has its own theorem, built by Semantics and proved by the engine (KTD15):

```lean
Sum.$dec_1 : ∀ (n : Int32), ¬ n ≤ 0 →
  Int.toNat (Int32.toInt (n - 1)) < Int.toNat (Int32.toInt n)
```

Its binders are the method's parameters, then whatever is in scope at the call: `let`-bound locals stay as `let` binders (substituting them, as Lean does, can grow the statement exponentially), and each enclosing `dite` contributes its hypothesis.
A local whose value contains a recursive call is different: inside `F` its value is `rec …`, which a theorem stated outside `F` cannot name, so it becomes a plain `∀` binder of its type, without its value (KTD15).
In `var a = Fib(n - 1); return a + Fib(n - 2);`, `Fib.$dec_2` therefore quantifies over `a`, which is enough, because the second call's decrease does not depend on `a`.
For the same reason, a hypothesis whose statement mentions a recursive call's result is left out of the obligation.
A recursive call inside another recursive call's argument, `F(F(n - 1))`, would need the inner result's value in the outer obligation, and is rejected (WRT0002 `nested recursion`).
The engine proves each one with the omega pipeline (chapter 6) and admits it before the definition, which refers to it.
A theorem that fails is reported like any other, at the call, with `omega`'s constraints and the goal.
This is `warrant verify tests/corpus/m5a/refuted`:

```text
refuted/Recursion.cs(12,16): error WRT0001: The recursive call 'Bad(n - 1)' could not be shown to decrease 'n': omega could not prove the goal.
  a possible counterexample may satisfy the constraints
    a ≤ 0
    -2147483648 ≤ a ≤ -1
    -6442450945 ≤ a + 4294967296*b ≤ -4294967297
  where
   a := if (n.toInt - ↑1) % ↑(2 ^ 32) < (↑(2 ^ 32) + 1) / 2 then (n.toInt - ↑1) % ↑(2 ^ 32) else (n.toInt - ↑1) % ↑(2 ^ 32) - ↑(2 ^ 32)
   b := (n.toInt - ↑1) / 4294967296

  n : Int32
  ⊢ (n - 1).toInt.toNat < n.toInt.toNat
```

The statement is not soundness-critical: the kernel checks that the definition is well-typed, and any well-typed proof will do, because proofs are irrelevant to `Sum`'s value.
It is built in Semantics because it follows the body's structure, which only Semantics knows.

Three places give a call fewer hypotheses than a developer might expect, and M5a reports rather than rejects them:

| Where the call is | What is missing | What the developer sees |
|---|---|---|
| after a shared fall-through (a join point, M4 docs/m4/05) | facts about values assigned in each branch | the decrease goal without them |
| right of `&&` or `\|\|` | the left side's truth | the decrease goal without it |
| in an arm of a closed-enum `switch` | which arm was taken | the decrease goal without it |

Each shows the goal, and the fix is to put the call under an `if`.
An arm of a `switch` over an integer or open enum does get its test as a hypothesis, because that `switch` is a chain of `if`s.

## The equation lemma

Every recursive definition gets one equation lemma, stating its body with the definition itself in place of `rec`:

```lean
Sum.$eq_def : ∀ (n : Int32), Sum n = if n ≤ 0 then 0 else n + Sum (n - 1)
```

The right side is exactly M4's translation of the body, with `Sum` as an ordinary constant, so it has the same shape a theorem's statement sees, and `Tactic.Unfold(nameof(Sum))` rewrites with it (chapter 5).
`Tactic.Simp(nameof(Sum))` does not: simp does not unfold a definition passed as an argument (chapter 5).
Its proof is one term, the `Nat.fix_eq` instance:

```lean
fun n => @WellFounded.Nat.fix_eq Int32 (fun _ => Int32) μ F n
```

`fix_eq` says `Nat.fix μ F n = F n (fun y _ => Nat.fix μ F y)`.
The kernel unfolds `Sum` on the left, beta-reduces `F` on the right, and sees `dite` against `ite` and `Nat.fix μ F (n - 1)` against `Sum (n - 1)` as equal by definition.
Lean's kernel accepted this bare proof for a hand-built definition (*ran*); Ansatz proves its equations the same way.

A definition whose equation lemma fails to check is a translation error, not a warning (KTD15).
Ansatz logs such failures only in verbose mode, which leaves definitions that `simp` cannot unfold; Warrant does not.

The sidecar marks `Sum` irreducible for Meta, as Lean marks its own well-founded definitions, so `whnf` and `simp` never unfold into `Nat.fix` and its counter; they rewrite with `$eq_def` instead.

## Axioms

| Declaration | Axioms |
|---|---|
| `WellFounded.Nat.fix` | none |
| `Sum.$dec_1` (bridging lemmas, then omega) | `Classical.choice`, `Quot.sound`, `propext` |
| `Sum` | the same three, through `$dec_1` |
| `Sum.$eq_def` | the same three; `Nat.fix_eq` also brings `Quot.sound` |

`Classical.choice` comes from Init's `Int32` lemmas, not from omega (*ran*; a test checks the three sets).
All three are Lean's standard axioms, which M4 already accepts (M4 docs/m4/01), and the assumption report lists them.

## The stack is outside the model

`Nat.fix` always returns a value, but the compiled method may not: `Sum(int.MaxValue)` recurses 2³¹ times and throws `StackOverflowException`, which .NET cannot catch.
A theorem about `Sum` is therefore a theorem about every call that returns.
The assumption report says so for every recursive unit (KTD31):

```text
Corpus.Recursion.Sum(int)                             TRANSLATED   (kernel: Warrant 1.0, bundle: warrant-semantics sha256:cc74b3a23fc7)
  Assumed (global):
    - Each recursive call returns without exhausting the stack
    - Arithmetic wraps on overflow (overflow checking is off)
    - The semantics bundle models C# 14 int, long and bool
```

This is the `report.md` that `warrant verify tests/corpus/m5a/accepted --report <dir>` writes.
The stack line is in the unit's own `global` list, which the JSON report keeps apart from the report-wide list; a theorem that depends on a recursive method, directly or through other units, gets the same line.

Making recursion depth part of the model would make every recursive definition partial, so M5a does not.

## What is not built

- **Structural recursion.**
  Design §4.2 says recursion is "structural recursion when detectable".
  For M5a's types it never is: `Int32` has no `brecOn` (*ran*: `termination_by structural n` fails), and records and closed types cannot be recursive.
  Lean tries structural recursion first and falls back to well-founded recursion for these types too.
  It returns with recursive types.
- **Mutual recursion** (R7), which needs `PSum` packing.
- **Measure inference** (Lean's `GuessLex`): `Spec.Decreases` is required.
- **Theorems about recursive methods by induction on the measure.**
  M5a can unfold `Sum` and prove facts that follow from one unfolding, but a claim such as `Sum(n) >= 0` for every `n` needs strong induction or Lean's functional induction, which is follow-up work.
