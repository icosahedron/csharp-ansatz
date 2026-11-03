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
`Spec.Decreases` returns `void`, so it can be `[Conditional]` and disappears from the compiled code (M4 KTD20); extraction reads it from the operation tree, which still contains the call, and U9 checks that it does.

Names in a script follow one rule, so extraction never guesses:

- `nameof(M)` names a C# member: a `[Verified]` method to unfold, or a `[Theorem]` to use as a lemma.
  Extraction resolves it through the semantic model, so an overloaded or unknown name is WRT0004 and a resolved one adds a dependency edge (KTD18).
- `Lean.Const("Int32.lt_iff_toInt_lt")` names a Lean declaration, which must be in the bundle.
- A string literal names a hypothesis in the goal, as in `Tactic.Exact("h")`.

The budget properties on `[Theorem]` are compile-time constants, so extraction can read them (KTD24); zero means the project's setting (chapter 7).

## What extraction produces

VIR grows by new kinds and fields only (M4 KTD5), and the schema version becomes 2 (KTD18):

| VIR addition | From | Holds |
|---|---|---|
| `ForAll`, `Exists` | `Spec.ForAll<T>(x => p)`, `Spec.Exists<T>(x => p)` | the bound variable's name and type, and the body |
| `Decreases` | `Spec.Decreases(e)` as the first statement | the measure expression |
| a theorem unit's parameters | the method's parameters | as for `[Verified]` units |
| `ProofScript` on a theorem unit | `.By(...)` | a list of tactic nodes |
| tactic node | each `Tactic.X(...)` | the tactic's name, then arguments: lemma references (unit key or Lean name), strings, numbers, nested tactics, named options |
| budget overrides on a theorem unit | `[Theorem(...)]` | the three numbers |

A tactic node is generic: `Tactic.Simp().With(decide: false)` becomes `tactic "simp" [option decide false]`, and a later tactic needs no new VIR kind.
The tactic's source span goes into the span side table, so a failure points at the `Tactic.X` call that failed.

The rules that M4 used to reject now accept:

- theorems with parameters;
- the lambda inside `Spec.ForAll` and `Spec.Exists`, with one parameter of a supported type and a body in the M4 subset (a lambda anywhere else stays WRT0002);
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
| `accepted/Recursion.cs` | `Sum`, a two-parameter recursion, `long` recursion | translated; decrease proved by `omega` |
| `accepted/Quantifiers.cs` | `ZeroIsNeutral`, `Cases` over `bool` and a closed enum, `Induction` over `Nat` | proved |
| `refuted/Increment.cs` | `AlwaysLarger` | WRT0001, goal `x : Int32 ⊢ Increment x > x`, counterexample `x = 2147483647` |
| `refuted/Recursion.cs` | `Bad(n) => Bad(n - 1)` without a guard | WRT0001 on the decrease obligation |
| `rejected/Recursion.cs` | mutual recursion, recursion without `Spec.Decreases`, `Spec.Decreases` not first | WRT0002 |
| `rejected/Scripts.cs` | a `nameof` of an overloaded method, a string literal where a lemma is expected | WRT0004 |

`expected.json` gains, per theorem, the expected goal text for refuted members and the counterexample, so the goal printer's output is part of the exit criterion.
As in M4, the corpus is written before the extractor changes (U9), so every rule has a failing test first.
