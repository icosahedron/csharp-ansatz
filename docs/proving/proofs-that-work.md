# Proofs that work today

Every proof on this page runs in this repository today, and the last command that ran it is given. The examples are
invented for the corpus in `tests/corpus/`: none of them is production code.

Two commands reproduce the results:

```sh
dotnet build -c Release src/Warrant.Cli
dotnet src/Warrant.Cli/bin/Release/net10.0/warrant.dll verify tests/corpus/m5a/accepted   # 20 verified units, 7 theorems proved, 0 not proved
dotnet src/Warrant.Cli/bin/Release/net10.0/warrant.dll verify tests/corpus/m4/accepted    # 79 verified units, 33 theorems proved, 0 not proved
```

## How a proof is checked

Warrant translates each `[Verified]` member to a Lean definition, and each `[Theorem]` to a Lean statement about
those definitions. A theorem without parameters is proved by computation (`rfl` or `decide`). A theorem with
parameters holds for every value of them, and its `.By(...)` script is run by Warrant's port of Lean's tactics.
The tactics are untrusted: they only search for a proof term. A theorem counts as proved only when Warrant's kernel
admits that term as a proof of the statement the trusted translator built.

Three independent kernels then check the same certificate (`warrant verify --out`; `scripts/cross-kernel.sh`,
[docs/kernel.md](../kernel.md#cross-kernel-checks-ansatz-and-the-arena-milestone-5a)):

| Certificate | Lean 4.35.0 | Warrant | Ansatz (patched) |
|---|---|---|---|
| M4 corpus, translated (2,956 declarations) | accept | accept | accept |
| M5a corpus, proved (2,879 declarations) | accept | accept | accept |
| M5a corpus with one proof replaced by another theorem's | reject at the replaced proof | reject at the replaced proof | reject at the replaced proof |

Ansatz needs a 7-line local patch for Lean 4.35 certificates (`tools/ansatz/nat-deceq-shortcut.patch`).

What a proof assumes is printed by `warrant verify --report <dir>`. Every unit here assumes that arithmetic wraps on
overflow (as it does with overflow checking off) and that the semantics bundle models C# 14's `int`, `long` and
`bool`. A recursive unit also assumes that each recursive call returns without exhausting the stack.

## Theorems for every input (M5a)

Source: `tests/corpus/m5a/accepted/`.

### An upper bound through a conditional

```csharp
[Verified]
public static int Clamp(int x) => x > 100 ? 100 : x < -100 ? -100 : x;

[Theorem]
static Proof AtMostOneHundred(int x) =>
    Prove.That(Clamp(x) <= 100)
         .By(Tactic.Unfold(nameof(Clamp)), Tactic.Omega());
```

`Unfold` replaces `Clamp(x)` by its body, and `omega` decides the linear arithmetic on both branches, for all
2³² values of `x`.

### Overflow, stated honestly

```csharp
[Verified]
public static int Increment(int x) => x + 1;

[Theorem]
static Proof LargerBelowMax(int x) =>
    Prove.That(Spec.Implies(x < int.MaxValue, Increment(x) > x))
         .By(Tactic.Unfold(nameof(Increment)), Tactic.Simp(), Tactic.Omega());
```

`x + 1` wraps like the CLR's `int`, so the guard is needed. Without it (`tests/corpus/m5a/refuted/Increment.cs`),
the proof fails with the counterexample:

```text
error WRT0001: Theorem 'Increments.AlwaysLarger(int)' could not be proved: omega could not prove the goal. Counterexample: x = 2147483647.
  x : Int32
  ⊢ x + 1 > x
```

### A fact about a record

```csharp
public enum PaymentStatus { Pending, Processed, Failed }
public sealed record Payment(int Id, int Amount, PaymentStatus Status);
public enum PaymentResult { Valid, InvalidAmount, InvalidStatus }

[Verified]
public static PaymentResult Validate(Payment p)
{
    if (p.Amount <= 0) return PaymentResult.InvalidAmount;
    if (p.Status != PaymentStatus.Pending) return PaymentResult.InvalidStatus;
    return PaymentResult.Valid;
}

[Theorem]
static Proof ValidImpliesPositive(Payment p) =>
    Prove.That(Spec.Implies(Validate(p) == PaymentResult.Valid, p.Amount > 0))
         .By(Tactic.Unfold(nameof(Validate)), Tactic.Simp());
```

This is design §5.1's example. It holds for every payment, because a valid result means the first `return` was not
taken. `simp` closes it with Warrant's default simp set; its proof also depends on the axiom `propext`.

### Case analysis over `bool` and a closed enum

```csharp
[Verified] public static bool Flip(bool b) => !b;

[Theorem]
static Proof FlipTwice(bool b) =>
    Prove.That(Flip(Flip(b)) == b)
         .By(Tactic.Unfold(nameof(Flip)), Tactic.Cases("b"), Tactic.AllGoals(Tactic.Simp()));

[Closed] public enum Light { Red, Amber, Green }

[Verified]
public static int Rank(Light l) => l switch { Light.Red => 0, Light.Amber => 1, _ => 2 };

[Theorem]
static Proof RankIsSmall(Light l) =>
    Prove.That(Rank(l) <= 2)
         .By(Tactic.Unfold(nameof(Rank)), Tactic.Cases("l"), Tactic.AllGoals(Tactic.Simp().With(decide: true)));
```

`Cases` splits the goal into one goal per value; `[Closed]` is what makes an enum's named values the only ones.
The same file proves `AndTrue(b) == b` by `Induction("b")`, and `ForAll<int>(y => y + 0 == y)` by `Intro` and
`Omega`.

### Recursion that terminates

```csharp
[Verified]
public static int Sum(int n)
{
    Spec.Decreases(n);
    if (n <= 0) return 0;
    return n + Sum(n - 1);
}
```

`Sum` becomes a well-founded definition over `Int.toNat n`. Warrant proves the decrease obligation
`Sum.$dec_1` with `omega`, and derives the equation lemma `Sum.$eq_def` that `Unfold` uses. `Add(a, b)` (measure:
the second parameter) and `SumLong(long n)` are proved terminating the same way. A call that does not decrease
is reported at the call (`tests/corpus/m5a/refuted/Recursion.cs`):

```text
error WRT0001: The recursive call 'Bad(n - 1)' could not be shown to decrease 'n': omega could not prove the goal.
  n : Int32
  ⊢ (n - 1).toInt.toNat < n.toInt.toNat
```

`Bad` steps from `int.MinValue` to `int.MaxValue`, so it need not terminate.

## Facts about particular inputs (M4)

Source: `tests/corpus/m4/accepted/`. These 33 theorems have no parameters, and are proved by computation in the
kernel: 26 by `rfl` and 7 by `decide`.

| File | Theorems | What they show |
|---|---|---|
| `Increment.cs` | `IncrementIsLarger`, `WrapsAtMax`, `LongWrapsAtMax` | `int` and `long` addition wraps at the maximum, as in the CLR |
| `Conversions.cs` | `NarrowingKeepsLowBits`, `WideningKeepsSign`, `SevenIsUnnamed`, `ProcessedIsOne` | Narrowing and widening casts; an enum cast to an unnamed value |
| `Locals.cs` | `BucketBreaks`, `BucketFallsThrough`, `BucketReturns`, `NestedReturnTaken`, `NestedReturnNotTaken`, `RushDoublesTheFee`, `ExpressMember`, `StepsAddThree` | Locals, reassignment, `switch` with `break` and fall-through, early `return` |
| `PayoutRules.cs` | `CappedAtTheLimit`, `NothingBelowTheDeductible` | A deductible and a limit |
| `Discounts.cs` | `NeverNegativeHere`, `TakesTheDiscount` | A discount that stays non-negative |
| `ClaimStatus.cs` | `DeniedIsFinal`, `OpenIsNotFinal`, `DeniedTakesTheDefault`, `OpenIsUrgent` | `switch` over a `[Closed]` enum, including its default arm |
| `Outcome.cs` | `MatchedIsOne`, `NoMatchIsTwo`, `DifferentOutcomes` | A `[Closed]` closed-set class compared with `==` |
| `Payments.cs` | `AcceptsPending`, `RejectsProcessed`, `RejectsZero` | `Validate` on particular payments |
| `Records.cs` | `MoveChangesX`, `MoveKeepsY`, `DifferentPoints`, `UnassignedEscalationAlerts` | `with` expressions, record equality and instance members of a sealed record |

The remaining files hold no theorems: `Operators.cs` is checked against the compiled .NET code by the differential
tests. `tests/corpus/m4/refuted/` holds a false theorem, and `rejected/` holds code outside the subset, each with the
diagnostic it must produce (`tests/corpus/m4/expected.json`).

## What cannot be proved yet

Division and remainder, checked arithmetic, `null`, `string`, `decimal`, loops, exceptions, and calls to anything
that is not `[Verified]` are rejected with WRT0002; [the reference](reference.md#supported-c) lists the subset and
the milestone that lifts each limit. The two known gaps in what a build verifies are in
[docs/m5a/07](../m5a/07-verify-and-build.md): `dotnet build -f` for a framework other than the first does not
verify, and code a source generator adds is not modelled.
