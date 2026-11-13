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
public static int Increment(int x)
{
    Spec.Requires(x < int.MaxValue);
    return x + 1;
}

[Theorem]
static Proof LargerBelowMax(int x) =>
    Prove.That(Spec.Implies(x < int.MaxValue, Increment(x) > x))
         .By(Tactic.Unfold(nameof(Increment)), Tactic.Simp(), Tactic.Omega());
```

`x + 1` would wrap like the CLR's `int` at `int.MaxValue`, which a verified method's own arithmetic may not do
(GitHub #244), so `Increment` states the bound as its precondition, and the theorem's guard is that precondition: a
theorem may only ask about a method within its `Spec.Requires`. To reason about the wrap itself, write it on purpose:
with `Increment(int x) => unchecked(x + 1)` and no guard (`tests/corpus/m5a/refuted/Increment.cs`), the proof fails
with the counterexample:

```text
error WRT0001: Theorem 'Increments.AlwaysLarger(int)' could not be proved: omega could not prove the goal. Counterexample: x = 2147483647.
  x : Int32
  ⊢ x + 1 > x
```

### A bounded theorem

```csharp
[Theorem]
static Proof Bounded(int a) =>
    Prove.That(Spec.Implies(a < 1000 && a > -1000, a + 1 > a))
         .By(Tactic.Intro("h"), Tactic.Omega());
```

Proved.A theorem's own `+`, `-`, `*` and unary `-` on `int` and `long` must not overflow (GitHub #236), under the
`Spec.Implies` that guards them: each is a well-definedness condition the default procedure proves before the script
runs. Without the bound (`Unbounded` there) the build fails at `a + 1` with `well-definedness of a Spec expression`, whatever the script
proves (`ArithmeticInATheoremThatCanOverflowFailsAtTheOperationAndProvesWhenBounded` in
`tests/Warrant.Engine.Tests/DefaultProcedureTests.cs`). `Spec.ForAll<int>(y => y + 0 == y)` needs no bound, since
`y + 0` cannot overflow.

### Wrapping on purpose

```csharp
[Verified]
public static int One() => 1;

[Theorem]
static Proof Wraps() => Prove.That(unchecked(int.MaxValue + One()) == int.MinValue);
```

Proved by `decide` (`Wraps` in `ArithmeticInATheoremThatCanOverflowFailsAtTheOperationAndProvesWhenBounded`).
`unchecked(...)` (or an `unchecked { }` block) says the wrap is intended, so the statement's arithmetic has no
obligation and wraps as the CLR does. Without `unchecked` the same statement fails at `int.MaxValue + One()`, which
overflows. (`One()` keeps the compiler from folding the sum, which it rejects as a constant overflow.) Arithmetic inside
a method's body is the method's own, which these obligations do not cover yet (#244).

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
    return unchecked(n + Sum(n - 1));
}
```

`Sum` becomes a well-founded definition over `Int.toNat n`. Its `n + Sum(n - 1)` is `unchecked`: nothing is known of
a recursive call's result where the no-overflow obligation is stated, since a recursive method has no `Spec.Ensures`
yet (a checker gap), and the sum does overflow for large `n`. Without `unchecked` the method fails at that `+` with `arithmetic overflow`
(`ARecursiveMethodsArithmeticHasObligationsAndItsRecursiveResultIsUnknown`); `n - 1` alone, under `n > 0`, is proved. Warrant proves the decrease obligation
`Sum.$dec_1` with `omega`, and derives the equation lemma `Sum.$eq_def` that `Unfold` uses. `SumLong(long n)` is
proved terminating the same way. A call that does not decrease is reported at the call
(`tests/corpus/m5a/refuted/Recursion.cs`):

```text
error WRT0001: The recursive call 'Bad(n - 1)' could not be shown to decrease 'n': omega could not prove the goal.
  n : Int32
  ⊢ (n - 1).toInt.toNat < n.toInt.toNat
```

`Bad` steps from `int.MinValue` to `int.MaxValue`, so it need not terminate.

### A recursive method with `Spec.Requires`

```csharp
[Verified]
public static int Add(int a, int b)
{
    Spec.Decreases(b);
    Spec.Requires(b >= 0 && a <= int.MaxValue - b);
    if (b <= 0) return a;
    return Add(a + 1, b - 1);
}
```

Proved (`tests/corpus/m5a/accepted/Recursion.cs`): `a + 1` is in range because the body assumes the `Spec.Requires`,
and the recursive call `Add(a + 1, b - 1)` is checked against it, as a call from any other method is (GitHub #256).
`Spec.Decreases` comes first, then `Spec.Requires`. With `Spec.Requires(a >= 0 && a <= 1000)` instead, `a + 1` is
still in range but the call fails, since the next `a` may be 1001
(`ARecursiveMethodsRequiresIsAssumedByItsBodyAndCheckedAtEachRecursiveCall`). A recursive method cannot state
`Spec.Ensures` yet, so a recursive call's result is still unknown.

### Locals merged after branches, and a closed-enum section

```csharp
[Closed] public enum Size { Small, Medium, Big }

[Verified]
public static int Shipping(int weight, bool express, bool member)
{
    Spec.Requires(weight >= 0 && weight <= 1000000);
    var cost = weight * 2;
    var bonus = 0;
    if (express)
    {
        cost = cost + 15;
        bonus = 1;
    }
    if (member) return cost - 5;
    return cost + bonus;
}

[Verified]
public static int Section(Size s, int x)
{
    Spec.Requires(s != Size.Small || (x >= 0 && x <= 1000));
    switch (s)
    {
        case Size.Small:
            return x * 2;
        default:
            return 0;
    }
}
```

Proved (`Shipping` in `tests/corpus/m4/accepted/Locals.cs`, `Section` in `OverflowGapTests`): after the `if`, `cost`
and `bonus` are known by their value on each path, `weight * 2` with `bonus = 0` or `weight * 2 + 15` with
`bonus = 1` (GitHub #255), and inside `case Size.Small` the obligation knows `s = Size.Small` (GitHub #258), so the
`Spec.Requires` bounds `x`. A section or `_` arm that takes several members knows the scrutinee is one of them.

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
`omega` reads. `+` and `-` on `decimal` can throw, so a method that uses them is a program in
the effect monad, for its contract obligation (from M6 U10 and U11). These examples are not in the corpus:
`DecimalEqualityAndOrderAreProvable` in `tests/Warrant.Engine.Tests/TheoremTests.cs` proves all four
(`dotnet test tests/Warrant.Engine.Tests --filter DecimalEqualityAndOrderAreProvable`).

`Math.Max` and `Math.Min` over parameters, and literals in a claim over every `decimal`, prove the same way:

```csharp
[Verified] public static decimal Smaller(decimal a, decimal b) => Math.Min(a, b);

[Theorem]
static Proof LargerIsAtLeastTheFirst(decimal a, decimal b) =>
    Prove.That(Larger(a, b) >= a)
         .By(Tactic.Unfold(nameof(Larger)), Tactic.Simp(Lean.Const("Warrant.Decimal.max_def"), Lean.Const("Warrant.Decimal.le_iff")), Tactic.Omega());

[Theorem]
static Proof SmallerOfOrderedIsTheFirst(decimal a, decimal b) =>
    Prove.That(Spec.Implies(a <= b, Smaller(a, b) <= a))
         .By(Tactic.Unfold(nameof(Smaller)),
             Tactic.Simp(Lean.Const("Warrant.Decimal.min_def"), Lean.Const("Warrant.Decimal.lt_iff"), Lean.Const("Warrant.Decimal.le_iff")),
             Tactic.Omega());

[Theorem]
static Proof NegatingAPositiveMakesItSmaller(decimal a) =>
    Prove.That(Spec.Implies(a > 0m, -a < a))
         .By(Tactic.Simp(Lean.Const("Warrant.Decimal.lt_iff"), Lean.Const("Warrant.Decimal.units_neg")), Tactic.Omega());
```

`max_def` unfolds `Math.Max` to an `if` on decimals, and the omega-prep step moves `units` inside it, which leaves an
`if` on integers that `omega` splits (GitHub #216). A literal such as `0m` is `units` of a literal to `omega`, whose
value `Tactic.Omega()` states when `omega` alone fails (GitHub #217). `DecimalMaxAndMinOverParametersAreProvable` and
`ADecimalLiteralIsReadByOmega` in `tests/Warrant.Engine.Tests/ProcedureStrengthTests.cs` prove these; a false claim
such as `Spec.Implies(a > 0m, a > 1m)` still fails (`AFalseClaimAboutADecimalLiteralStillFails`).

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
`Spec.Requires` or `Spec.Ensures` must not overflow (GitHub #183), as the method's own `a + b` must not (#244): an
overflowing spec almost always states something its author did not mean. Each one is a well-definedness condition, proved
under the `Spec.Requires` before it, and here the bounds keep `a + b` inside `int`. Without the `Spec.Requires` the build
fails at the `a + b` in `Spec.Ensures` with `well-definedness of a Spec expression` (`SumUnbounded` in
`tests/corpus/m6/refuted/Contracts.cs`, `ArithmeticInEnsuresThatCanOverflowFailsAtTheEnsuresLineAndProvesWhenBounded`).
Specs keep C#'s `int` and `long`: there is no unbounded integer, so bound the operands rather than widening them. An
explicit `(int)` cast still truncates as in C#. A `Spec.Assert` condition follows the same rule (#235).

### A bounded method

```csharp
[Verified]
public static int Steps(int a)
{
    Spec.Requires(a < 100 && a > -100);
    var x = a;
    x += 5;
    x++;
    x--;
    x *= 2;
    return -x;
}
```

Proved. A verified method's own `+`, `-`, `*`, unary `-`, `++`, `--` and compound assignment on `int` and `long` must
not overflow (GitHub #244): C# would wrap, which is almost always a bug. Each operation is a condition, proved under
what is known on the way to it: the `Spec.Requires`, the `if` branch and `switch` section taken, the guard of a `?:`,
`&&` or `||` around it, and the value of each local, here each step's exact value. Without the `Spec.Requires` the
build fails at `x += 5` with `arithmetic overflow`. A guard works as well as a precondition: `a < 1000 ? a + 1 : 0`
is proved with none. When wrapping is the point (a hash, a checksum), write `unchecked(...)` or `unchecked { }`,
which has no condition (`ArithmeticInAPureBodyThatCanOverflowFailsAtTheOperationAndProvesWhenBounded`).
A value merged from two branches that change two locals reaches the operation unknown.

### A product of two bounded variables

```csharp
[Verified]
public static int Total(int price, int quantity)
{
    Spec.Requires(0 <= price && price <= 10000 && 0 <= quantity && quantity <= 1000);
    Spec.Ensures<int>(r => r >= 0 && r <= 10000000);
    return price * quantity;
}
```

Proved. `omega` reads linear arithmetic only, so `price * quantity` is an atom to it, and alone it can neither rule
out the overflow nor prove the `Spec.Ensures`. When it fails, `Tactic.Omega()` looks for literal bounds on each factor,
proves them, and adds the bounds they put on the product (`Warrant.Int.mul_ge_of_ge_of_ge` and its three siblings, from
`0 ≤ (x - a) * (y - b)`), here `0 ≤ price * quantity ≤ 10000000` (GitHub #257). Signs do not matter:
`-1000 <= a && a <= 1000 && -50 <= b && b <= 2000` bounds the `long` `a * b + 1`, and `-5 <= a, b <= -1` proves
`1 <= a * b && a * b <= 25` (`TwoSidedProductBoundsProveAtTheDefaultBudget`). Each factor needs a literal bound, and a
product of three factors, `a * b * c`, gets none for its outer product:
with `-a <= b && b <= a` the product fails at `a * b` with `arithmetic overflow`, though it cannot overflow, and a
`[ProofFor]` script cannot rescue it, since a pure method's no-overflow conditions are the default procedure's alone.
`tests/Warrant.Engine.Tests/ProcedureStrengthTests.cs` runs these (`AProductOfTwoBoundedVariablesIsBounded`,
`AProductWhoseFactorHasNoLiteralBoundFailsEvenWithAProofForScript`, which checks that the script never runs).

### A `bool` result by cases

```csharp
[Verified]
public static bool NeedsReview(int amount, int threshold, bool flagged)
{
    Spec.Ensures<bool>(r => !flagged || r);
    return amount > threshold || flagged;
}

[Verified]
public static int DaysOrZero(int? x)
{
    Spec.Ensures<int>(r => x is null ? r == 0 : r == x.Value);
    return x is null ? 0 : x.Value;
}
```

Both proved. `omega` does not split a `bool`: `NeedsReview`'s goal is `flagged = false ∨ threshold < amount ∨ flagged =
true`, true by cases on `flagged` only. When `omega` fails, the default procedure splits a `bool` the goal compares
with `true` or `false`, here `flagged`, and in `DaysOrZero` the null test `x.isNone`, and proves each case with its value
substituted (GitHub #227, #245). A record's nullable field works the same way (`refund.Days is null ? … :
refund.Days.Value`), and so do up to three such terms on one path: `!(f && g) || r`, two nested null tests,
`!f || (x is null ? r == 0 : r == 1)`, and `(f == g) || r`, which splits `f` and then `g`
(`SeveralBoolAndNullTestsAreEachSplit`). With `return amount > threshold;` the case `flagged = true, amount <= threshold` fails, and so
does the method (`ABoolEnsuresThatNeedsACaseSplitOnABoolParameterIsProved`, `AConditionalEnsuresOverANullTestIsProved`,
`ABoolEnsuresThatIsFalseInOneCaseStillFails` in `ProcedureStrengthTests`).

### Arithmetic bounded by a callee's `Spec.Ensures`

```csharp
[Verified]
public static int Bound(int x)
{
    Spec.Requires(x >= 0);
    Spec.Ensures<int>(r => r >= 0 && r <= 100);
    return x > 100 ? 100 : x;
}

[Verified]
public static int ByCallee(int a)
{
    Spec.Requires(a >= 0);
    var n = Bound(a);
    return n + 1;
}
```

Proved: `Bound`'s `Spec.Ensures` says `n <= 100`, so `n + 1` cannot overflow. A call to a method with a
`Spec.Requires`, or to one that can throw, is a step the VC walk sees (chapter 7 of docs/m6), and each implicit
operation after it is checked there with everything the walk knows: the callee's `Spec.Ensures`, a dependency's
contract, the path. A pure callee with only a `Spec.Ensures` (`Cap(x)` with `r >= 0 && r <= 100`) bounds `Cap(a) * 2`
the same way (`ByCallee`, `ByRaisingCallee` and `ByCallee` in
`ArithmeticInABodyThatCanRaiseIsCheckedByTheWalkWithEverythingItKnows` and
`ArithmeticInAPureBodyThatCanOverflowFailsAtTheOperationAndProvesWhenBounded`).

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

### A record's nullable field

```csharp
public sealed record Refund(Payment? Original);

[Verified]
public static int OriginalIdOrZero(Refund refund)
{
    Spec.Requires(refund.Original is null || refund.Original.Id > 0);
    Spec.Ensures<int>(r => r >= 0);
    if (refund.Original is null) return 0;
    return refund.Original.Id;
}
```

Proved with no script. A null test of a field is a path condition about the field (`refund.Original = none`), so the
read after the test, and the read inside `Spec.Requires` after `is null ||`, cannot meet a null. Without the test,
`refund.Original.Id` fails with `null read`. Records with `int?`, `decimal?` and nullable record fields compare with `==`
as the CLR's generated `Equals` does (GitHub #218): two nulls are equal, a null and a value are not, and `1.0m` equals
`1.00m`. The examples are `Refunds` in `tests/corpus/m6/accepted/Nullables.cs` and `refuted/Nullables.cs`
(`ARecordsNullableFieldIsReadAfterANullTestInABodyAndInASpecExpression`; the differential tests compare `SameFee` and
`SameRefund` with the CLR).

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
script, and the code after it may use it. Its `a + b` must not overflow (GitHub #235), which the `Spec.Requires` rules
out; without it the build fails at that `a + b` with `well-definedness of a Spec expression`, and at the program's own
`a + b` with `arithmetic overflow` (#244) (`ArithmeticInASpecAssertThatCanOverflowFailsAtTheOperationAndProvesWhenKnownBounded`). What the
obligation knows is the `Spec.Requires`, the branch the `Spec.Assert` is in and the `Spec.Assert`s before it: to use a
callee's `Spec.Ensures`, assert it first. `Spec.Assert(b != 0); return a / b;` with no `Spec.Requires` fails at the
`Spec.Assert` line with `Spec.Assert` (`AFailingAssertFailsAtItsLineAndTheDivisionAfterItUsesTheAssertedFact`).

A local computed by the method's own arithmetic carries its value into a later `Spec.Assert` (GitHub #246):

```csharp
[Verified]
public static int Sum(int a, int b)
{
    Spec.Requires(a < 1000 && a > -1000 && b < 1000 && b > -1000);
    var sum = a + b;
    Spec.Assert(sum - b == a);
    return sum;
}
```

Proved: the program continues past `a + b` only where it does not overflow, so `sum - b` is `a` and stays in range
(`ArithmeticInASpecAssertThatCanOverflowFailsAtTheOperationAndProvesWhenKnownBounded`'s `ByImplicitLocal`).

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

### Several fields of the result after its null test

```csharp
[Verified]
public async Task<int> IdIfPending(int id)
{
    Spec.Ensures<int>(r => r == 0 || r == id);
    var p = await store.GetPayment(id);
    if (p is null || p.Status != PaymentStatus.Pending) return 0;
    return p.Id;
}
```

Proved with no script. Each read of `p` is checked not to be null on its own, so the walk names `p`'s value once for
`p.Status` and once for `p.Id`; the two names are of one value (`some v₁ = some v₂` gives `v₁ = v₂`), so what the contract
says about the first (`v₁.Id == id`) is what the `Spec.Ensures` needs of the second (GitHub #226). The same holds for a
fact from the null test's `||`: `if (p is null || p.Amount < 0) return 0; return p.Amount;` proves `r >= 0`. The example
is `PaymentLookup.IdIfPending` in `tests/corpus/m6/accepted/Payments.cs`
(`AFieldOfANullableResultReadAfterANullTestIsRelatedToWhatTheWalkLearned` in `ExternalCallTests.cs`).

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

### A cancellation token passed through, and an early `return;`

```csharp
public interface IShipments
{
    Task<Order?> Find(int id, CancellationToken ct);
    Task Ship(Order order, CancellationToken ct);
}

[ContractFor(typeof(IShipments))]
internal abstract class ShipmentsContract : IShipments
{
    public Task<Order?> Find(int id, CancellationToken ct)
    {
        Spec.Ensures<Order?>(r => r is null || r.Id == id);
        return default!;
    }

    public Task Ship(Order order, CancellationToken ct)
    {
        Spec.Requires(order.Id > 0);
        return default!;
    }
}

public sealed class ShipmentService(IShipments shipments)
{
    [Verified]
    public async Task ShipIfFound(int id, CancellationToken ct)
    {
        if (id <= 0) return;
        var order = await shipments.Find(id, ct);
        if (order is null) return;
        await shipments.Ship(order, ct);
    }
}
```

Proved with no script: `Ship`'s `Spec.Requires` holds because `Find`'s contract gives `order.Id == id` and the first
`return;` leaves only `id > 0`. The token is a value the proof cannot look at (a `Unit` in the model), passed on to both
calls; a cancelled call is one of the exceptions the report says `Find` and `Ship` may raise. Writing `default` or
`CancellationToken.None` for the token, or reading `ct.IsCancellationRequested`, is rejected. The example is
`ShipmentService` in `tests/corpus/m6/accepted/Dependencies.cs` (`CorpusTests.EveryM6MemberGetsItsExpectedOutcome`; the
differential tests run it with a cancelled and an uncancelled token).

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
both are proved too: `int` multiplication wraps, and `omega` alone (Lean's too, which has no dark shadow) cannot use the
bounds to rule the wrap out, so `Tactic.Omega()` proves `x.toInt * 3` in range under them and uses the exact product
(GitHub #237); without the bound `y <= 1000` the theorem fails. `tests/Warrant.Engine.Tests/RelationalPropertyTests.cs`
runs this example, in a class `S`, with both (`dotnet test tests/Warrant.Engine.Tests --filter RelationalPropertyTests`).
