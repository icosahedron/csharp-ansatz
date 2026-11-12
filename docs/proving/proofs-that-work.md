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
overflow outside a `checked` region (as it does with overflow checking off), that the semantics bundle models the
C# 14 types and operations it lists (`int`, `long`, `bool` and, from M6, `decimal`, nullable values and exceptions), and that the only axioms are Lean's standard three: `propext`, `Classical.choice` and `Quot.sound`. A recursive unit also assumes that each recursive call returns without exhausting the stack.

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

### A guard against `int.MinValue`

```csharp
[Verified]
public static int Abs(int x) => x < 0 ? -x : x;

[Theorem]
static Proof AbsIsNonNegativeAboveMin(int x) =>
    Prove.That(Spec.Implies(x > int.MinValue, Abs(x) >= 0))
         .By(Tactic.Unfold(nameof(Abs)), Tactic.Simp(), Tactic.Omega());
```

`-int.MinValue` wraps to `int.MinValue`, so the guard is needed. The compiler folds `int.MinValue` to the literal
`-2147483648`, and `omega` reads it as that number; the same proof works for `long` and `long.MinValue`. This example
is not in the corpus: `AGuardAgainstMinValueIsReadByOmega` in `tests/Warrant.Engine.Tests/TheoremTests.cs` proves
both (`dotnet test tests/Warrant.Engine.Tests --filter AGuardAgainstMinValueIsReadByOmega`).

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

## Division by a constant and `Math.Max` (M6)

```csharp
[Verified] public static int Half(int x) => x / 2;
[Verified] public static int AtLeastZero(int x) => Math.Max(x, 0);

[Theorem]
static Proof HalfIsAtMost(int x) =>
    Prove.That(Spec.Implies(x >= 0, Half(x) <= x))
         .By(Tactic.Unfold(nameof(Half)), Tactic.Simp(), Tactic.Omega());

[Theorem]
static Proof HalfOfALong(long a) =>
    Prove.That(Spec.Implies(a >= 0, a / 2 <= a && a % 2 < 2)).By(Tactic.Simp(), Tactic.Omega());

[Theorem]
static Proof NeverNegative(int x) =>
    Prove.That(AtLeastZero(x) >= 0)
         .By(Tactic.Unfold(nameof(AtLeastZero)), Tactic.Simp(Lean.Const("Warrant.Int32.max_def")), Tactic.Omega());
```

`/` and `%` by a constant other than 0 and -1 cannot throw, so they translate as Lean's truncating `/` and `%`, which
agree with C#'s there, and may appear in a theorem statement; `omega` reads them through Warrant's division lemmas.
`Math.Min` and `Math.Max` cannot throw either, and `Warrant.Int32.max_def` unfolds `Math.Max` to its `if`. A method that
divides by a variable, or uses checked arithmetic, `Math.Abs` or a nullable read, can throw: it becomes a program in
M6's effect monad, and what it may throw is for its contract obligation to prove (M6 U10 states it, U11's default
procedure proves it), not for a theorem, which cannot call it. These examples are
not in the corpus: `PureDivisionAndMathMaxAreProvable` in `tests/Warrant.Engine.Tests/TheoremTests.cs` proves all
three (`dotnet test tests/Warrant.Engine.Tests --filter PureDivisionAndMathMaxAreProvable`).

## `decimal` equality and order (M6)

```csharp
public sealed record Price(decimal Amount);

[Verified] public static decimal Larger(decimal a, decimal b) => Math.Max(a, b);

[Theorem] static Proof ScaleIsIgnored() => Prove.That(new Price(1.0m) == new Price(1.00m));

[Theorem] static Proof LargerKeepsTheFirstOfEqualValues() => Prove.That(Larger(1.0m, 1.00m) == 1m && 0.1m < 0.11m);

[Theorem]
static Proof OrderIsTransitive(decimal a, decimal b, decimal c) =>
    Prove.That(Spec.Implies(a < b && b <= c, a < c))
         .By(Tactic.Simp(Lean.Const("Warrant.Decimal.lt_iff"), Lean.Const("Warrant.Decimal.le_iff")), Tactic.Omega());

[Theorem]
static Proof EqualityIsReflexive(decimal a) => Prove.That(a == a).By(Tactic.Apply(Lean.Const("Warrant.Decimal.eq_refl")));
```

A `decimal` keeps its scale, as the CLR's does, but `==`, `<` and `<=` compare values, so `1.0m == 1.00m`, and a
record's `==` compares a `decimal` field the same way. Comparisons, unary `-` and `Math.Min`, `Max` and `Abs` cannot
throw, so theorems may use them; the first two theorems are proved by computation. Over every `decimal`,
`Warrant.Decimal.lt_iff` and `le_iff` turn the order into one on `units`, the value as an integer count of 10^-28, which
`omega` reads. Two things do not work yet: `simp` does not compute `units` of a literal, so a claim over every `decimal`
that mentions one (`a > 0m`) is not proved, and nothing splits the `if` that `Math.Max` unfolds to, so
`Larger(a, b) >= a` is not proved either. `+` and `-` on `decimal` can throw, so a method that uses them is a program in
the effect monad, for its contract obligation (from M6 U10 and U11). These examples are not in the corpus:
`DecimalEqualityAndOrderAreProvable` in `tests/Warrant.Engine.Tests/TheoremTests.cs` proves all four
(`dotnet test tests/Warrant.Engine.Tests --filter DecimalEqualityAndOrderAreProvable`).

## Contracts proved with no script (M6)

A method that can throw, divides, uses checked arithmetic or reads a nullable value, or that states `Spec.Requires` or
`Spec.Ensures`, has a contract obligation, and the build proves it with no script: the VC walker follows the method's
program, the VC simp set and `omega` close what it leaves, and each condition that does not close is WRT0001 at the
operation that produced it, starting with its kind. The examples below are run by
`tests/Warrant.Engine.Tests/DefaultProcedureTests.cs` (each in a class `S`) and the M6 corpus
(`tests/corpus/m6/`, `EveryM6MemberGetsItsExpectedOutcome`).

### A division under its precondition

```csharp
[Verified]
public static int Ratio(int a, int b)
{
    Spec.Requires(b != 0 && b != -1);
    return a / b;
}
```

Proved. `Spec.Requires` rules out both ways C#'s `/` throws: a zero divisor, and `int.MinValue / -1`, which overflows.
With only `Spec.Requires(b != 0)` the build fails at `a / b` with `overflow in a checked operation`, because
`int.MinValue / -1` is still possible (`RatioWithoutTheMinusOneGuardFailsAtTheDivisionAsOverflow`).

### A division with nothing to rule out its exceptions

```csharp
[Verified]
public static int Ratio(int a, int b) => a / b;
```

Not proved, with two errors at the division's line (`tests/corpus/m6/refuted/Effects.cs`):

```text
Effects.cs(10,46): error WRT0001: The contract of 'Effects.Ratio(int, int)' could not be proved: division by zero: omega could not prove the goal:
  a b : Int32
  h : b = 0
  ⊢ False
Effects.cs(10,46): error WRT0001: The contract of 'Effects.Ratio(int, int)' could not be proved: overflow in a checked operation: omega could not prove the goal:
```

Each error names the kind of condition, then its path conditions as hypotheses (here, the divisor is zero), then the
goal left after the VC simp set. A method with no contract still has to prove that no implicit exception happens.

### Checked arithmetic with bounds

```csharp
[Verified]
public static int Bounded(int a, int b)
{
    Spec.Requires(a > -1000 && a < 1000 && b > -1000 && b < 1000);
    return checked(a + b);
}
```

Proved: the bounds keep the sum inside `int`. With only the upper bounds, `checked(a + b)` can still overflow below
`int.MinValue`, and the build fails at `a + b` (`CheckedAddProvesWithBothBoundsAndFailsAtThePlusWithOnlyTheUpperOnes`).

### Arithmetic in a contract

```csharp
[Verified]
public static int Sum(int a, int b)
{
    Spec.Requires(a > -1000 && a < 1000 && b > -1000 && b < 1000);
    Spec.Ensures<int>(r => r == a + b);
    return a + b;
}
```

Proved (`Sum` in `tests/corpus/m6/accepted/Contracts.cs`). `+`, `-`, `*` and unary `-` on `int` and `long` in a
`Spec.Requires` or `Spec.Ensures` must not overflow, even though the method's own `a + b` wraps (GitHub #183): an
overflowing spec almost always states something its author did not mean. Each one is a well-definedness condition, proved
under the `Spec.Requires` before it, and here the bounds keep `a + b` inside `int`. Without the `Spec.Requires` the build
fails at the `a + b` in `Spec.Ensures` with `well-definedness of a Spec expression` (`SumUnbounded` in
`tests/corpus/m6/refuted/Contracts.cs`, `ArithmeticInEnsuresThatCanOverflowFailsAtTheEnsuresLineAndProvesWhenBounded`).
Specs keep C#'s `int` and `long`: there is no unbounded integer, so bound the operands rather than widening them. An
explicit `(int)` cast still truncates as in C#, and a `Spec.Assert` condition still wraps.

### An implication in a contract

```csharp
[Verified]
public static int Successor(int x)
{
    Spec.Ensures<int>(r => Spec.Implies(x < 1000, r == x + 1));
    return x < 1000 ? x + 1 : x;
}
```

Proved (`Successor` in `tests/corpus/m6/accepted/Contracts.cs`). `Spec.Implies(p, q)` is accepted in `Spec.Requires` and
`Spec.Ensures` (GitHub #213) and means `p → q`. `q` is read only when `p` holds, so its well-definedness conditions
(here, that `x + 1` does not overflow) are proved under `p`: `x < 1000` is enough. With `Spec.Implies(x > 0, r == x + 1)`
the `x + 1` can overflow at `int.MaxValue`, and the build fails at it with `well-definedness of a Spec expression`
(`ArithmeticInTheConclusionOfImpliesIsWellDefinedUnderItsPremise`). A false implication fails at its `Spec.Ensures`
line with `postcondition of the method`: `Spec.Ensures<int>(r => Spec.Implies(x > 0, r > x)); return x;` leaves the
goal `0 < x ⊢ False` (`Grown` in `tests/corpus/m6/refuted/Contracts.cs`). In a `Spec.Requires`, each verified caller
proves the implication at its arguments, so `Spec.Requires(Spec.Implies(x > 0, x < 100))` accepts `Small(-500)` and
fails at `Small(500)` (`ARequiresWithImpliesIsACallersPreconditionAndHasAVacuityCheck`). `Spec.Assert` still rejects
`Spec.Implies` (WRT0004); write `!p || q` there.

### A null guard

```csharp
[Verified]
public static int Guarded(Payment? p)
{
    if (p is not null)
    {
        return p.Id;
    }
    return 0;
}
```

Proved: the guard is a path condition, so reading `p.Id` cannot meet a null. Without the guard the build fails at `p`
with `null read`, and passing an unchecked `Payment?` to a method that takes a `Payment` fails with `null passed where
a non-null value is required` (`ANullDereferenceGuardedByIsNotNullProvesAndAnUnguardedOneFailsAtItsLine`,
`ANullablePassedWhereANonNullValueIsRequiredProvesOnlyUnderItsGuard`).

### `Spec.Assert`

```csharp
[Verified]
public static int Average(int a, int b)
{
    Spec.Requires(a >= 0 && a <= 1000 && b >= 0 && b <= 1000);
    Spec.Assert(a + b >= 0, Tactic.Omega());
    return (a + b) / 2;
}
```

Proved (`tests/corpus/m6/accepted/Contracts.cs`): the asserted fact is a condition at the `Spec.Assert`, proved by its
script, and the code after it may use it. `Spec.Assert(b != 0); return a / b;` with no `Spec.Requires` fails at the
`Spec.Assert` line with `Spec.Assert` (`AFailingAssertFailsAtItsLineAndTheDivisionAfterItUsesTheAssertedFact`).

### No reachable throw: `Spec.NoThrow`

```csharp
[Verified]
public static int NonZero(int b)
{
    Spec.Requires(b != 0);
    Spec.NoThrow();
    if (b == 0)
    {
        throw new ArgumentException("b must not be zero");
    }
    return b;
}
```

Proved, and its report lists no "Assumed (exceptions)": `Spec.NoThrow` makes the proof show that the throw is
unreachable under the `Spec.Requires`, rather than allow it (#182). The guard still protects callers Warrant does not
verify, which can pass 0. The same method without the `Spec.Requires` fails at the `throw`
(`TheGuideExampleProvesAndItsTwinWithoutTheRequiresFailsAtTheThrow` in `tests/Warrant.Engine.Tests/NoThrowTests.cs`,
whose class is `S`; here it is in a class `Guards`):

```text
Guards.cs(24,13): error WRT0001: The contract of 'Guards.NonZeroOfAny(int)' could not be proved: an explicit throw is reachable under the Requires (Spec.NoThrow): omega could not prove the goal:
  case ht
  b : Int32
  h : b = 0
  ⊢ False
```

The path condition `b = 0` is the branch that throws; nothing contradicts it. In the M6 corpus, `Quotient` in
`accepted/Contracts.cs` proves and its twin `QuotientOfAny` in `refuted/Contracts.cs` fails at its `throw`.

## A contract proved by a script (M6)

```csharp
[Verified]
public static int NonNegative(int x)
{
    Spec.Ensures<int>(r => r >= 0);
    return x < 0 ? 0 : x;
}

[ProofFor(nameof(NonNegative))]
static Proof NonNegativeProof() =>
    Prove.Contract().By(
        Tactic.Apply(Lean.Const("Std.Do.Triple.pure")),
        Tactic.Unfold(nameof(NonNegative)),
        Tactic.Simp(Lean.Const("Std.Do.SPred.entails_1"), Lean.Const("Std.Do.SPred.apply_pure_cons"), Lean.Const("Std.Do.SPred.down_pure_nil")),
        Tactic.Omega());

[Theorem]
static Proof NeverNegative(int x) =>
    Prove.That(NonNegative(x) >= 0).By(Tactic.Apply(Lean.Const("Cs.S.«NonNegative(System.Int32)».$contract_spec")));
```

A method's `Spec.Requires` and `Spec.Ensures` are one obligation, a `Std.Do` triple
`NonNegative.$contract : ∀ σ x, ⦃⌜True⌝⦄ pure (NonNegative x) ⦃⇓r => ⌜r ≥ 0⌝, allowed⦄`, which the `[ProofFor]` script
proves from the triple: `Triple.pure` leaves `⌜True⌝ ⊢ₛ ⌜NonNegative x ≥ 0⌝`, and the three `SPred` lemmas turn it into a
plain goal for `omega`. Once proved, a pure method's contract is also the lemma `NonNegative.$contract_spec : ∀ x,
NonNegative x ≥ 0`, which a theorem can apply without unfolding the method. This contract also proves with no script
(`APureMethodWithAnEnsuresProvesWithNoScript`); a script that starts with `Tactic.VcGen()` runs the walker first and
gets its conditions as goals, as `Contracts.Same` in the M6 corpus does with `Tactic.VcGen(), Tactic.Omega()`.
`AProofForScriptProvesAPureMethodsContractAndItsSpecLemmaIsAvailableToCallers` in
`tests/Warrant.Engine.Tests/ContractTests.cs` runs this example, in a class `S`.

## A dependency's contract used by a script (M6)

```csharp
public interface ICounter { int Count(); }

[ContractFor(typeof(ICounter))]
internal abstract class CounterContract : ICounter
{
    public int Count() { Spec.Ensures<int>(r => r >= 0); return default!; }
}

public sealed class S(ICounter counter)
{
    [Verified]
    public int Size()
    {
        Spec.Ensures<int>(r => r >= 0);
        return counter.Count();
    }

    [ProofFor(nameof(Size))]
    static Proof SizeProof() => Prove.Contract().By(Tactic.Unfold(nameof(Size)), Tactic.Exact("counter_Count_spec"));
}
```

A method that calls a dependency is proved for every implementation that keeps the dependency's contract: its obligation
binds one operation per member it calls and takes that member's contract as a hypothesis, `∀ σ (counter_Count : ClrM σ
Int32), ⦃⌜True⌝⦄ counter_Count ⦃⇓r => ⌜r ≥ 0⌝, allowed⦄ → ⦃⌜True⌝⦄ Size counter_Count ⦃⇓r => ⌜r ≥ 0⌝, allowed⦄`. Here
`Size` is the call itself, so once unfolded the goal is the hypothesis, named after the dependency and the member with
`_spec` appended. The script is not needed: the default procedure proves `Size` too, as the next section shows.
`AProofForScriptProvesADependencyObligationFromTheMembersContract` in `tests/Warrant.Engine.Tests/ContractTests.cs`
runs this example.

## Dependencies proved with no script (M6)

At each call to a dependency member, the VC walker uses the member's contract hypothesis at the call's arguments: the
member's `Spec.Requires` must hold there, its `Spec.Ensures` holds after it, and an exception from it is allowed and
listed in the report. The proof holds for every implementation of the interface that keeps its contract class.

### A result that holds only through the contract

```csharp
public interface IStore
{
    Task<Payment?> GetPayment(int id);
    Task SavePayment(Payment p);
}

[ContractFor(typeof(IStore))]
internal abstract class StoreContract : IStore
{
    public Task<Payment?> GetPayment(int id)
    {
        Spec.Ensures<Payment?>(r => r is null || r.Id == id);
        return default!;
    }

    public Task SavePayment(Payment p) => default!;
}

public sealed class S(IStore store)
{
    [Verified]
    public async Task<bool> Found(int id)
    {
        Spec.Ensures<bool>(r => r);
        var p = await store.GetPayment(id);
        return p is null || p.Id == id;
    }
}
```

Proved with no script. Nothing in `S` says what `GetPayment` returns, so the proof rests on its contract alone: called
with `id + 1`, the same method is WRT0001 at its `Spec.Ensures` (postcondition of the method). So is a method that
expects `GetPayment` to find what `SavePayment` stored, since `SavePayment`'s `=> default!` contract promises nothing,
and one that expects two calls to `GetPayment(id)` to agree: each call may see a different store. The tests are in
`tests/Warrant.Engine.Tests/ExternalCallTests.cs` (`AnEnsuresThatHoldsOnlyThroughTheMembersContractProves` and the
three after it).

### The payment example

Design §5.2's `ProcessPayment`, shortened here, is proved with its store as a hypothesis:

```csharp
[Verified]
public async Task<Result> ProcessPayment(int paymentId)
{
    Spec.Ensures<Result>(r => r != Result.Success || paymentId > 0);

    if (paymentId <= 0) return Result.InvalidId;
    var payment = await store.GetPayment(paymentId);
    if (payment is null) return Result.NotFound;
    if (Validate(payment) != PaymentResult.Valid) return Result.Invalid;
    await store.SavePayment(payment with { Status = PaymentStatus.Processed });
    return Result.Success;
}
```

Proved with no script, for every implementation of `IPaymentStore` that keeps its contract class. The walker also proves
that `payment` is not null where `Validate` and `with` use it. Its report lists both members' contracts under "Assumed
(contracts)", that `store` and the tasks the two calls return are not null, and that either call may throw. The full
example is `tests/corpus/m6/accepted/Payments.cs`, and its report block is `tests/corpus/m6/ProcessPayment.report.txt`
(`ProcessPaymentsObligationProvesUnderTheDefaultProcedure` in `ExternalCallTests.cs`,
`TheReportOfProcessPaymentIsTheCheckedInOne` in `ReportTests.cs`).

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

`string`, loops, `try`, and calls to anything that is not `[Verified]`, modelled or a contracted dependency are rejected
with WRT0002; [the reference](reference.md#supported-c) lists the subset and
the milestone that lifts each limit. A type defined in another assembly cannot appear in verified code, with one
exception: a `[Closed]` class from a referenced project that imports `Warrant.Build` (even with `WarrantEnabled` false)
is checked from the source that project recorded, and the assumption report says so. Source generators run as in the compiler, and a call that a generated
interceptor replaces is rejected ([docs/m5a/07](../m5a/07-verify-and-build.md)). The known gap in what a build
verifies is that `dotnet build -f` for a framework other than the first does not verify.

## Two calls of a method that can throw (M6)

```csharp
[Verified]
public static int Scale(int x)
{
    Spec.Requires(x >= -1000 && x <= 1000);
    Spec.Ensures<int>(r => r == x + x);
    if (x < 0)
    {
        throw new System.ArgumentException("x");
    }
    return checked(x + x);
}

[Verified]
public static bool Monotone(int x, int y)
{
    Spec.Requires(0 <= x && x <= y && y <= 1000);
    Spec.Ensures<bool>(r => r);
    return Scale(x) <= Scale(y);
}

[Theorem]
static Proof DoubleIsMonotone(int x, int y) =>
    Prove.That(Spec.Implies(0 <= x && x <= y && y <= 1000, x + x <= y + y)).By(Tactic.Simp(), Tactic.Omega());
```

All three are proved; `Scale` and `Monotone` with no script. `Scale` can throw, so a theorem that calls it, such as
`Prove.That(Spec.Implies(0 <= x && x <= y && y <= 1000, Scale(x) <= Scale(y)))`, is WRT0002
`theorem calling a raising method`. `Monotone` is the wrapper route: it makes both calls and states the relation as its
`Spec.Ensures`, and the VC walker uses `Scale`'s proved contract at each call, so with the two results
rewritten by those `Spec.Ensures` the goal it leaves is `x + x ≤ y + y` under the bounds, which `omega` closes. `DoubleIsMonotone` is the other route:
`Scale`'s `Spec.Ensures` pins its result, so the relation is a theorem about `x + x`. With `x * 3` in place of `x + x`,
neither is proved: `int` multiplication wraps, and `omega` (Lean's too, which has no dark shadow) cannot use the bounds
to rule the wrap out. `tests/Warrant.Engine.Tests/RelationalPropertyTests.cs` runs this example, in a class `S`, and
pins the `x * 3` limit (`dotnet test tests/Warrant.Engine.Tests --filter RelationalPropertyTests`).
