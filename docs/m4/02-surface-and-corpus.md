# 2. The user package and the corpus

> Part of the [M4 design](README.md). Decisions: KTD3, KTD15, KTD18, KTD20 in the [plan](../plans/2026-11-02-1245-feat-m4-pure-subset-plan.md).

A developer marks code with a handful of attributes and calls from the `Warrant` package.
M4 publishes the part of that package M4 can use, and the corpus is the fixed set of C# files that decides whether M4 is done.

## The `Warrant` package in M4

`src/Warrant` targets netstandard2.0 (design D8), so any project, including .NET Framework ones, can reference it.
It has no dependencies and no run-time behaviour that matters.
In M4 it contains these types (XML documentation comments omitted):

```csharp
namespace Warrant;

[AttributeUsage(AttributeTargets.Method | AttributeTargets.Property, Inherited = false)]
public sealed class VerifiedAttribute : Attribute { }

[AttributeUsage(AttributeTargets.Method, Inherited = false)]
public sealed class TheoremAttribute : Attribute { }

[AttributeUsage(AttributeTargets.Enum | AttributeTargets.Class, Inherited = false)]
public sealed class ClosedAttribute : Attribute { }

public sealed class Proof
{
    private Proof() { }
}

public static class Prove
{
    public static Proof That(bool claim) =>
        throw new InvalidOperationException("[Theorem] methods are never executed.");
}

public static class Spec
{
    public static bool Implies(bool premise, bool conclusion) => !premise || conclusion;
}
```

Two details differ from what [reference.md](../proving/reference.md) said before M4, and the reference now says the same as this chapter (KTD20):

- **Not every `Spec` member can be `[Conditional]`.** C# allows `[Conditional]` only on methods that return `void` (error CS0578 otherwise).
  `Spec.Implies` returns `bool` and `Prove.That` returns `Proof`, so their calls stay in the compiled IL.
  `Prove.That` throws, because `[Theorem]` methods are never meant to run.
  `Spec.Implies` computes the implication, so a stray call is harmless.
  M6's `void` members (`Spec.Requires`, `Spec.Ensures`, `Spec.Assert`) will be `[Conditional("WARRANT_CONTRACTS")]` as designed.
- **Value-returning spec calls are allowed only inside theorem statements.** Extraction reports `Spec.Implies`, or `Prove.That`, anywhere else as WRT0004 (malformed spec).

`Prove.That(...).By(...)` and `Tactic` are M5a additions; adding them later does not change anything M4 publishes.

## The corpus

`tests/corpus/m4/` is the exit criterion made concrete (design §11, M4 row).
It holds C# source files that are **not** part of any project's build: the test suite compiles them in memory (chapter 3), so the repository's warnings-as-errors and analyzer settings never apply to them.
A `.gitattributes` entry forces LF line endings there, so source spans and hashes are the same on every machine.

```text
tests/corpus/m4/
├── README.md            what each file covers and why
├── expected.json        the expected outcome of every member
├── accepted/
│   ├── PayoutRules.cs   Payout and its theorems (tutorial)
│   ├── Discounts.cs     Discounted (how-to guide)
│   ├── Payments.cs      a Payment record, an open PaymentStatus enum, Validate
│   ├── Increment.cs     wrap-around at int.MaxValue, and a theorem about it
│   ├── ClaimStatus.cs   a [Closed] enum and a switch expression over it
│   ├── Outcome.cs       a [Closed] closed-set class, equality and ?: over its instances
│   ├── Records.cs       construction, with, equality, an instance property
│   ├── Locals.cs        reassignment, if without else, switch statements, a nested return
│   └── Conversions.cs   int to long and back, casts between open enums and integers
├── refuted/
│   └── Increment.cs     theorems that compile and translate but are false
└── rejected/
    └── one file per group of constructs M4 rejects, one method per construct
```

### The accepted side

Each accepted file is small and is there for a reason the README names.
`Payments.cs` is the `Validate`-shaped method the exit criterion asks for, with `int` in place of `decimal`:

```csharp
public enum PaymentStatus { Pending, Processed, Failed }

public sealed record Payment(int Id, int Amount, PaymentStatus Status);

public enum PaymentResult { Valid, InvalidAmount, InvalidStatus }

public static class Payments
{
    [Verified]
    public static PaymentResult Validate(Payment p)
    {
        if (p.Amount <= 0) return PaymentResult.InvalidAmount;
        if (p.Status != PaymentStatus.Pending) return PaymentResult.InvalidStatus;
        return PaymentResult.Valid;
    }

    [Theorem]
    static Proof RejectsZero() =>
        Prove.That(Validate(new Payment(1, 0, PaymentStatus.Pending)) == PaymentResult.InvalidAmount);
}
```

`Increment.cs` carries the classic false theorem in the form M4 can state, with no parameters.
The true theorem sits in `accepted/`; the false one sits in `refuted/`, because `accepted/` is what the cross-check step translates and it must come out clean (chapter 7):

```csharp
[Verified]
public static int Increment(int x) => x + 1;

[Theorem]
static Proof WrapsAtMax() => Prove.That(Increment(int.MaxValue) == int.MinValue);   // proved

[Theorem]
static Proof NeverWraps() => Prove.That(Increment(int.MaxValue) > int.MaxValue);    // reported false
```

`Outcome.cs` has a closed-set class with a `string` field.
One instance is a get-only auto-property and the other a `static readonly` field, because both are common in real code and both have the closed shape (chapter 3).
M4 has no strings, but the field does not stop translation: a closed type is modelled by *which* instance a value is, so instance fields are ignored, and only *reading* `Name` is rejected (chapter 3).
C# cannot `switch` over `Outcome`'s instances, because a pattern must be a constant and `Outcome.Matched` is a property, so verified code compares them with `==`.
One accepted method has the shape `o == Outcome.Matched ? 1 : o == Outcome.NoMatch ? 2 : 3`: the CLR returns `3` for `null`, a value the model cannot produce, which is what the non-null assumption excludes (chapter 7).

```csharp
[Closed]
public sealed class Outcome
{
    public static Outcome Matched { get; } = new("Matched");

    public static readonly Outcome NoMatch = new("NoMatch");

    private Outcome(string name) => Name = name;

    public string Name { get; }
}
```

### The rejected side

Every construct M4 rejects has a member that uses it and nothing else unsupported, so each rejection is tested in isolation.
There is one rejected member for each construct in KTD15 (all WRT0002) and for each diagnostic in KTD18:

- **WRT0002:** every construct listed in KTD15, from recursion and `/` to records with extra instance state and reserved member names.
  A unit that uses a rejected type is rejected too, with the construct `depends on a rejected unit`.
- **WRT0003:** a call to a `[Theorem]` method.
- **WRT0004:** `Spec.Implies` outside a theorem statement.
- **WRT0005:** a call to a member that is neither verified nor modelled, such as `Math.Sign` (`Math.Abs` until M6 modelled it).
- **WRT0008:** an integer cast and an unboxing conversion to a `[Closed]` enum in unverified methods, and a `[Closed]` enum with no member valued 0 (warnings; a cast inside a verified method is also WRT0002).
- **WRT0009:** a `[Closed]` class that fails each step of the closed shape, one member per step.

`Locals.cs` on the accepted side also carries the shape that a careless translation rule gets wrong: an `if` whose branches both fall through, one of which contains a nested `return` (chapter 5).

A few rejections are tested by the extraction tests rather than by corpus members, because they need a compilation of their own or are details of one rule.
One of them is a `switch` section that mixes `default` with `case` labels (`case 1: default:`), which extraction rejects with WRT0002 because translation places the default branch last and a shared section cannot be split (chapter 5).

### `expected.json`

The expected outcome of every member is data, not prose, so the tests can enforce it.
The file lists the compilations first, then the members of each compilation, keyed by documentation-comment ID, which Roslyn computes the same way on every machine.
An excerpt:

```json
{
  "compilations": [
    { "name": "accepted", "files": ["accepted/*.cs"], "checkOverflow": false },
    { "name": "refuted", "files": ["refuted/*.cs"], "checkOverflow": false },
    { "name": "rejected", "files": ["rejected/*.cs"], "exclude": ["rejected/CheckedProject.cs"], "checkOverflow": false },
    { "name": "checked-project", "files": ["rejected/CheckedProject.cs"], "checkOverflow": true }
  ],
  "members": {
    "accepted": {
      "M:Payouts.PayoutRules.Payout(System.Int32,System.Int32,System.Int32)": { "outcome": "translated" },
      "M:Payouts.PayoutTheorems.CappedAtTheLimit": { "outcome": "proved", "by": "rfl" },
      "M:Claims.Payments.Validate(Claims.Payment)": { "outcome": "translated", "assumeNonNull": ["p"] }
    },
    "refuted": {
      "M:Corpus.Refuted.Increments.NeverWraps": { "outcome": "false" }
    },
    "rejected": {
      "M:Corpus.Rejected.Arithmetic.Halve(System.Int32)": { "outcome": "rejected", "diagnostics": [{ "id": "WRT0002", "construct": "division" }] }
    }
  }
}
```

The construct names are the ones extraction puts in its messages, so `expected.json` is also the list of names a developer sees.
The `checked-project` compilation is the one case that needs its own options: `rejected/CheckedProject.cs` is compiled with overflow checking on, its `+`, unary `-` and narrowing cast are rejected as `checked arithmetic`, and its widening cast, which cannot overflow, translates.

M6 supports `/`, `%`, `throw`, checked arithmetic and `Math.Abs` (plan M6 U7), so the members that used them, `Halve` in the excerpt above among them, moved to `tests/corpus/m6`; the M4 corpus README's flip list records each move, and `checked-project` keeps only the widening cast.
