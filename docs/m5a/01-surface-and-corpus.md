# 1. The surface and the corpus

> Part of the [M5a design](README.md). Decisions: KTD17, KTD18, KTD24 in the [plan](../plans/2026-11-03-0838-feat-m5a-meta-tactics-plan.md).

M4's theorems have no parameters, and their claims are checked by computation.
M5a lets a theorem take parameters, which makes it a claim about all of their values, and lets the developer say how to prove it.
This chapter covers what is added to the `Warrant` package, how extraction reads it into VIR, and the corpus that decides whether M5a is done.

## What the developer writes

A theorem's parameters are universally quantified.
`Spec.ForAll` and `Spec.Exists` quantify inside a claim, and `Spec.Implies` (from M4) states a condition:

```csharp
[Theorem]
static Proof AlwaysLarger(int x) =>                      // ∀ x : Int32, …
    Prove.That(Increment(x) > x)
         .By(Tactic.Unfold(nameof(Increment)), Tactic.Omega());

[Theorem]
static Proof ZeroIsNeutral() =>
    Prove.That(Spec.ForAll<int>(y => y + 0 == y))           // ∀ y : Int32, y + 0 = y
         .By(Tactic.Intro("y"), Tactic.Omega());

[Theorem(TimeoutSeconds = 60)]
static Proof PayoutIsNeverNegative(int loss, int deductible, int limit) =>
    Prove.That(Spec.Implies(deductible >= 0 && limit >= 0,
                            PayoutRules.Payout(loss, deductible, limit) >= 0))
         .By(Tactic.Unfold(nameof(PayoutRules.Payout)), Tactic.Simp(), Tactic.Omega());
```

`.By(...)` is the proof script, run left to right on the goal (chapter 4).
The engine introduces a theorem's own parameters before the script runs, so the script starts from `x : Int32 ⊢ Increment x > x`; binders from `Spec.ForAll` are introduced by `Tactic.Intro`.
Without `.By`, the engine tries M4's `rfl` and `decide`, which can only prove claims without free variables; a quantified claim without a script fails with its goal shown, and with a counterexample when one exists (chapter 4).

A recursive method states its measure as the first statement of a block body (chapter 3):

```csharp
[Verified]
public static int Sum(int n)
{
    Spec.Decreases(n);
    if (n <= 0) return 0;
    return n + Sum(n - 1);
}
```

## The package additions

The new members, with XML comments omitted:

```csharp
namespace Warrant;

public sealed class Proof
{
    private Proof() { }
    public Proof By(params Tactic[] steps) => this;                 // never runs: Prove.That throws first
}

public static partial class Spec
{
    public static bool ForAll<T>(Func<T, bool> claim) => throw NotExecuted();
    public static bool Exists<T>(Func<T, bool> claim) => throw NotExecuted();

    [Conditional("WARRANT_CONTRACTS")]
    public static void Decreases(long measure) { }                 // int widens implicitly
}

public sealed class Tactic
{
    private Tactic() { }
    public static Tactic Intro(params string[] names) => …;
    public static Tactic Exact(object term) => …;                    // a hypothesis name, nameof(...) or Lean.Const(...)
    public static Tactic Apply(object term) => …;
    public static Tactic Cases(object target) => …;
    public static Tactic Induction(object target) => …;
    public static Tactic Unfold(params string[] names) => …;         // nameof(...)
    public static Tactic Simp(params object[] lemmas) => …;
    public static Tactic Omega() => …;
    public static Tactic AllGoals(Tactic tactic) => …;
    public static Tactic Try(Tactic tactic) => …;

    public Tactic With(bool? decide = null, bool? contextual = null) => …;  // simp options: Tactic.Simp().With(decide: false)
}

public static class Lean
{
    public static LeanConstant Const(string name) => new(name);       // a declaration in the bundle
}

public sealed class TheoremAttribute : Attribute
{
    public int TimeoutSeconds { get; set; }                         // 0 means the project default
    public long TacticFuel { get; set; }
    public long KernelFuel { get; set; }
}
```

`Spec.ForAll` and `Spec.Exists` return `bool` so that they compose with `&&` and `Spec.Implies`, and they throw if called, because a quantifier over `int` cannot be computed.
Like `Prove.That`, they are valid only in theorem statements (WRT0004 elsewhere).
`Spec.Decreases` returns `void`, so it can be `[Conditional]` and disappears from the compiled code (M4 KTD20); extraction reads it from the operation tree, which still contains the call, and a U9 test checks that it does.
Its parameter is `long`, so an `int` measure is widened implicitly at the call; extraction drops that implicit conversion and stores the measure in its own type, `int32`.

Names in a script follow fixed rules, so extraction never guesses:

- `nameof(M)` names a C# member: a `[Verified]` method to unfold, or a `[Theorem]` to use as a lemma.
  Extraction resolves it through the semantic model and adds a dependency edge (KTD18).
  It must resolve to exactly one `[Verified]` member or `[Theorem]` declared in the compilation: an overload set is WRT0004 `nameof of an overloaded method`, and anything else is WRT0004 `nameof that names no verified member or theorem`.
- `Lean.Const("Int32.lt_iff_toInt_lt")` names a Lean declaration, which must be in the bundle. It takes a string literal, and it is not accepted where a variable or a member to unfold is expected.
- A string literal names a hypothesis or variable in the goal, as in `Tactic.Exact("h")` or `Tactic.Cases("b")`.
  That holds for `Intro`, `Exact`, `Apply`, `Cases` and `Induction`.
  `Simp` takes lemmas only, so a string literal there is WRT0004 `string literal where a lemma is expected`; `Unfold` takes members only, so a string literal there is WRT0004 `string literal where a member name is expected`.

A step that is not a `Tactic.X(...)` call, an option value that is not a constant, or a script built as an array is WRT0004 `unsupported script argument`.
A `Tactic` or `Lean` call outside a theorem's `.By(...)` is WRT0004 `proof script outside a theorem`, and a theorem whose script names the theorem itself is WRT0004 `theorem used in its own proof`.

The budget properties on `[Theorem]` are compile-time constants, so extraction can read them (KTD24); zero means the project's setting (chapter 7).

## What extraction produces

VIR grows by new kinds and fields only (M4 KTD5), and the schema version becomes 2 (KTD18):

| VIR addition | From | Holds |
|---|---|---|
| `forall`, `exists` | `Spec.ForAll<T>(x => p)`, `Spec.Exists<T>(x => p)` | `local` (the bound variable's ID), `name`, `domain` (its type) and `body` |
| `decreases` statement | `Spec.Decreases(e)` as the first statement | the measure expression |
| a theorem unit's `params` | the method's parameters | as for `[Verified]` units |
| `script` on a theorem unit, after `statement` | `.By(...)` | a list of `{"tactic": {"name", "args"}}` nodes |
| tactic node | each `Tactic.X(...)` | the tactic's name as Lean spells it (`intro`, `exact`, `apply`, `cases`, `induction`, `unfold`, `simp`, `omega`, `all_goals`, `try`), then arguments: `unit` (a unit key, from `nameof`), `lean` (a Lean name), `string`, `number`, `bool`, a nested tactic, and `option` (a name and a value) |
| `budget` on a theorem unit | `[Theorem(...)]` | `timeoutSeconds`, `tacticFuel` and `kernelFuel` as decimal strings; omitted when all three are zero |

A tactic node is generic: `Tactic.Simp().With(decide: false)` becomes `simp` with the argument `option{decide, bool false}`, and a later tactic needs no new VIR kind.
The tactic's source span goes into the span side table, so a failure points at the `Tactic.X` call that failed.
A unit that uses none of these encodes as in version 1, apart from the version field.

The rules that M4 used to reject now accept:

- theorems with parameters;
- the lambda inside `Spec.ForAll` and `Spec.Exists`, with one parameter of a supported type and an expression body in the M4 subset (a lambda anywhere else stays WRT0002 `lambda`, a lambda with a statement body is WRT0002 `lambda with statements`, and a claim that is not a lambda is WRT0004 `quantifier whose claim is not a lambda`);
- `.By(...)` on `Prove.That`;
- a method that calls itself, when its block body starts with `Spec.Decreases`.

Still rejected with WRT0002:

| Construct | Why |
|---|---|
| `recursion without Spec.Decreases` | M5a does not infer measures (KTD14); this includes expression-bodied recursive methods, which have no statement to hold the measure. |
| `mutual recursion` | M5a supports direct self-recursion only (R7). |
| `nested recursion` | a recursive call in another recursive call's argument, such as `F(F(n - 1))`, has a decrease obligation that cannot name the inner result (chapter 3). |
| `Spec.Decreases not first` | the measure is read at entry, over the parameters. |

`IsEven` and `IsOdd` in the M4 corpus stay rejected; `Factorial` stays rejected until it gains a block body with `Spec.Decreases`.

## The M5a corpus

`tests/corpus/m5a/` follows the M4 layout (M4's chapter 2): files compiled in memory, `expected.json` naming each member's outcome, and `accepted/`, `refuted/` and `rejected/` directories.
The exit criterion's members are:

| File | Members | Expected |
|---|---|---|
| `accepted/Payments.cs` | `Validate`, `ValidImpliesPositive` | proved by `Unfold`, `Simp` |
| `accepted/Increment.cs` | `Increment`, `LargerBelowMax` (`x < int.MaxValue` implies `Increment(x) > x`) | proved by `Unfold`, `Simp`, `Omega` |
| `accepted/Clamp.cs` | `Clamp`, `AtMostOneHundred` (`Clamp(x) <= 100`) | proved by `Unfold`, `Omega`, through the literal lemmas (chapter 6) |
| `accepted/Recursion.cs` | `Sum`, `Add` (two parameters, the measure is the second), `SumLong` (a `long` measure) | translated; each decrease proved by `omega` |
| `accepted/Quantifiers.cs` | `ZeroIsNeutral` (`Spec.ForAll` with `Intro`), `FlipTwice` (`Cases` over `bool`), `RankIsSmall` (`Cases` over a `[Closed]` enum, with `.With(decide: true)`), `AndTrueIsIdentity` (`Induction` over `bool`, with `AllGoals` and `Try`) | proved |
| `refuted/Increment.cs` | `AlwaysLarger` | WRT0001 at `Tactic.Omega()`, goal `x : Int32 ⊢ x + 1 > x` (after `Unfold`), counterexample `x = 2147483647` |
| `refuted/Recursion.cs` | `Bad(n) => Bad(n - 1)` without a guard | WRT0001 on the decrease obligation |
| `rejected/Recursion.cs` | mutual recursion (`IsEven`, `IsOdd`), recursion without `Spec.Decreases` (`Factorial`), `Spec.Decreases` not first (`Countdown`), nested recursion (`Nested`) | WRT0002 |
| `rejected/Scripts.cs` | a `nameof` of an overloaded method, a string literal where a lemma is expected, `Spec.ForAll` outside a theorem | WRT0004 |

C# cannot declare a variable of Lean's `Nat`, so the corpus has no induction over `Nat`; `AndTrueIsIdentity` runs `Induction` over a `bool`, and induction over `Nat` is tested at the Meta level (chapter 4).

`expected.json` gains, per theorem, the expected goal text for refuted members and the counterexample.
The corpus tests check which members extraction accepts and rejects; the goals, counterexamples and proofs are checked by the engine's tests, which assert the printed goal of each refuted member.
As in M4, the corpus was written before the extractor changed (U9), so every rule had a failing test first.
