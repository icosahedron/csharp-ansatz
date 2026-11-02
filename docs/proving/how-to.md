# How-to guides

> Target syntax; see the [status note](README.md). Each guide names the milestone
> it needs. *Proposed* means the feature is not in the design yet (§12).

These guides assume you have done the [tutorial](tutorial.md). Each one solves a
single problem and stops there. For the full list of attributes, `Spec`
methods and tactics, see the [reference](reference.md).

- [Prove a property of a pure method](#prove-a-property-of-a-pure-method)
- [Read a failed proof](#read-a-failed-proof)
- [Get a proof through when the tactics give up](#get-a-proof-through-when-the-tactics-give-up)
- [Add preconditions and postconditions](#add-preconditions-and-postconditions)
- [Verify a method that calls a database or service](#verify-a-method-that-calls-a-database-or-service)
- [Work with enums and closed sets](#work-with-enums-and-closed-sets)
- [Deal with overflow](#deal-with-overflow)
- [Specify a method that throws](#specify-a-method-that-throws)
- [Prove things about private methods](#prove-things-about-private-methods)
- [Specify an expression-bodied member](#specify-an-expression-bodied-member)
- [Keep logging out of the proof](#keep-logging-out-of-the-proof)
- [Write a loop invariant](#write-a-loop-invariant)
- [Specify a method that mutates objects](#specify-a-method-that-mutates-objects)
- [Verify a block inside an unverified method](#verify-a-block-inside-an-unverified-method)
- [Run verification in CI](#run-verification-in-ci)
- [Have another kernel check your proofs](#have-another-kernel-check-your-proofs)

---

## Prove a property of a pure method

*M4 for concrete inputs, M5a for all inputs.*

1. Mark the method `[Verified]`. It must be inside the supported subset
   ([reference](reference.md#supported-c)); the build tells you if it isn't.
2. Write a `[Theorem]` method that returns `Prove.That(condition)`. Parameters
   of the theorem are universally quantified.
3. If the theorem has parameters, add `.By(...)`. Start with
   `Tactic.Unfold(nameof(M)), Tactic.Simp(), Tactic.Omega()`; that closes most
   claims about integer arithmetic and `if`.

```csharp
[Theorem]
static Proof DiscountNeverIncreasesPrice(int price, int discount) =>
    Prove.That(Spec.Implies(price >= 0 && discount >= 0,
                            Pricing.Discounted(price, discount) <= price))
         .By(Tactic.Unfold(nameof(Pricing.Discounted)), Tactic.Simp(), Tactic.Omega());
```

Write the claim as an implication when it only holds for some inputs. A
theorem with no `Spec.Implies` claims something for *every* `int`, including
negative ones and `int.MaxValue`.

## Read a failed proof

*M5a.*

A failed proof is a build error with up to three parts:

```text
Pricing.cs(40,5): error WRT0001: Theorem 'DiscountNeverIncreasesPrice' could not be proved.
  omega found a counterexample:
    price = 0, discount = -1
  Unsolved goal:
    price discount : Int32
    h₁ : 0 ≤ price
    h₂ : ¬(price ≤ discount)
    ⊢ price - discount ≤ price
```

(Here the theorem said only `price >= 0`, and `Discounted` returns
`discount >= price ? 0 : price - discount`.)

- **Counterexample.** If there is one, believe it first. Run the method with
  those values in a unit test. Usually the claim is missing a condition
  (here, `discount >= 0`).
- **Unsolved goal.** Above the line `⊢` are the facts the prover had: the
  theorem's parameters and the hypotheses it could use (`h₁`, `h₂`, …). Below it
  is what it still had to show. If a fact you expected is missing from above
  the line, the proof never learned it: add it to the `Spec.Implies`, to a
  `Spec.Requires`, or to a contract.
- **No counterexample, goal looks true.** The tactics weren't strong enough.
  See the next guide.

`warrant explain <unit>` prints the same goal with every intermediate step of
the tactic script.

## Get a proof through when the tactics give up

*M5a.*

Try these in order:

1. **Unfold the callees.** `Tactic.Unfold` only unfolds what you name. If the
   goal still mentions a method call, unfold that one too:
   `Tactic.Unfold(nameof(A), nameof(B))`.
2. **Split on cases.** For a `bool`, enum or closed-set parameter, or a nullable
   value, `Tactic.Cases(x)` produces one goal per value. Follow it with
   `Tactic.AllGoals(Tactic.Simp())`.
3. **Prove a helper theorem first.** Split a long claim into two `[Theorem]`
   methods and use the first with `Tactic.Apply(nameof(First))` or pass it to
   simp: `Tactic.Simp(nameof(First))`.
4. **Use a Lean library lemma.** Anything in Init (and later Mathlib) is
   available by name: `Tactic.Simp(Lean.Const("Int.add_comm"))`.
5. **Check the claim is true.** If none of this works, write a few unit tests
   with edge values. Most stuck proofs are of false claims with no small
   counterexample.

For a theorem over several `bool` parameters, a nested `Tactic.Cases` for each
is verbose. A finite-domain `decide` tactic is *proposed* (§12 Q20).

## Add preconditions and postconditions

*M6.*

Put `Spec` calls at the top of the method body:

```csharp
[Verified]
public static int Installment(int total, int count)
{
    Spec.Requires(total >= 0 && count > 0);
    Spec.Ensures<int>(r => r >= 0 && r * count <= total);
    return total / count;
}
```

- `Spec.Requires` is assumed inside the method and **checked at every verified
  call site**. A caller that can't show `count > 0` gets a build error at the
  call.
- `Spec.Ensures<T>(r => ...)` must hold on every normal return; `r` is the
  return value. For `void` methods use `Spec.Ensures(() => ...)`. For `async`
  methods, `T` is the awaited type.
- The calls are `[Conditional("WARRANT_CONTRACTS")]`: they don't exist in the
  compiled IL and cost nothing at run time.

## Verify a method that calls a database or service

*M6.*

1. Find the interface the method calls through (a repository, a client, a port).
2. Write a contract class for it: an abstract class that implements the
   interface, marked `[ContractFor(typeof(I))]`, with a `Spec.Ensures` in each
   method you need to assume something about. Return `default!`.
3. Methods you assume nothing about can just `=> default!`. The verifier then
   allows them to return anything and throw anything.

```csharp
[ContractFor(typeof(IClaimStore))]
file abstract class ClaimStoreContract : IClaimStore
{
    public Task<Claim?> Find(int claimId)
    {
        Spec.Ensures<Claim?>(c => c is null || c.Id == claimId);
        return default!;
    }

    public Task Save(Claim claim) => default!;   // no guarantees assumed
}
```

4. Inject the dependency through a constructor. A dependency stored in a
   `readonly` field becomes a parameter of the theorem Warrant generates.
   Primary-constructor parameters that are never assigned are *proposed* to
   count too (§12 Q20).
5. Build, then read the "Assumed (contracts)" section of the report. Every line
   is something you're asking reviewers to take on trust. Keep contracts as weak
   as the proof allows.

Contracts are **never** global axioms. A wrong contract can't be used to prove
something unrelated; it only weakens the proofs that use it.

## Work with enums and closed sets

*M4.*

C# enums are open: `(Status)42` is a valid value. Warrant models them that
way, so a `switch` without a default case is not exhaustive. If your code never
casts integers to the enum, mark it `[Closed]`:

```csharp
[Closed]
public enum ClaimStatus { Open, Paid, Denied }
```

Now `Tactic.Cases(status)` gives exactly three goals, and the analyzer reports
any cast to `ClaimStatus` from an integer.

`[Closed]` works the same way on the "smart enum" pattern: a sealed class with
only private constructors, whose static get-only instances are its only values.

```csharp
[Closed]
public sealed class Outcome
{
    public static Outcome Matched { get; } = new("Matched");
    public static Outcome NoMatch { get; } = new("NoMatch");

    private Outcome(string name) => Name = name;
    public string Name { get; }
}
```

Warrant recognises the class by that shape, not by its base class. If a
`[Closed]` class doesn't have the shape (a public constructor, say), the
analyzer reports an error instead of guessing. Classes like this are more
reliably closed than enums: without reflection, no code can create another
instance.

## Deal with overflow

*M5a for unchecked, M6 for checked.*

`int` arithmetic wraps around, as the CLR does. When a proof fails with a
counterexample near `int.MaxValue` or `int.MinValue`, choose one:

- **Rule it out.** Add the bound the business logic already guarantees:
  `Spec.Requires(amount <= 1_000_000_000)`. Each caller now has to show it.
- **Use a wider type** for the intermediate value (`long`), if that's what the
  code should have done anyway.
- **Use `checked`.** Then overflow throws `OverflowException` instead of
  wrapping, and the proof has to show the exception can't happen, or the spec
  has to allow it.

In a project with `<CheckForOverflowUnderflow>true</CheckForOverflowUnderflow>`,
all arithmetic is checked, and Warrant follows the project setting.

`decimal` (M6) doesn't wrap: `a - b` throws when the result is out of range.
Proofs about `decimal` subtraction therefore usually need a bound on the inputs.

## Specify a method that throws

*M6.*

Exceptions are part of the model. A `throw`, a null dereference, a division by
zero and checked overflow are all exits that the verifier tracks.

- To prove a method never throws, show that every throwing path is unreachable
  from its `Spec.Requires`.
- `Spec.Ensures` constrains **normal** returns only.
- To say which calls an exception can come from, `Spec.ThrowsOnlyFrom(...)` is
  *proposed* (§12 Q20). Until then, put the code that may throw behind a
  contract, and keep the rest of the method throw-free.

## Prove things about private methods

*M5a.*

C# access rules still apply: a theorem can only call what it can see. Put the
theorem in the same class. If the class is not `partial`, nest a static class:

```csharp
internal partial class ReassignmentAlerts
{
    private static bool IsRepeat(Guid? current, Guid? previous, int count) =>
        count > 0 && current == previous;

    static class Theorems
    {
        [Theorem]
        static Proof FirstIsNeverARepeat(Guid? current, Guid? previous) =>
            Prove.That(!IsRepeat(current, previous, 0))
                 .By(Tactic.Unfold(nameof(IsRepeat)), Tactic.Simp());
    }
}
```

`[Theorem]` methods are never emitted into your call graph. You can leave them
in production code.

## Specify an expression-bodied member

*M6.*

`Spec.Ensures` is a statement, so it needs a block body. Rewrite

```csharp
public bool NeedsReview => Amount > Threshold || IsFlagged;
```

as

```csharp
public bool NeedsReview
{
    get
    {
        Spec.Ensures<bool>(r => Spec.Implies(IsFlagged, r));
        return Amount > Threshold || IsFlagged;
    }
}
```

Or leave the member alone and state the property as a `[Theorem]` about it,
which needs no change to the member. Other options are under discussion
(§12 Q17).

## Keep logging out of the proof

*M6, proposed (§12 Q20).*

Logging calls in a verified method are calls to code without a contract, and
interpolated messages pull strings into the proof. The proposed fix is a
standard contract that says logging has no effect on verified state. It is
listed in the assumption report like any other contract. Until it exists, write
a contract class for your logging interface whose methods are all `=> default!`.

## Write a loop invariant

*M7.*

At the top of the loop body, state what is true before every iteration, and for
`while` and `for` loops, what decreases:

```csharp
var total = 0m;
for (var i = 0; i < payments.Count; i++)
{
    Spec.Invariant(0 <= i && i <= payments.Count);
    Spec.Invariant(total >= 0);
    Spec.Decreases(payments.Count - i);
    if (payments[i].Amount > 0) total += payments[i].Amount;
}
```

A good invariant is true on entry, preserved by the body, and strong enough to
give you the postcondition when the loop ends. If the verifier says the
invariant is not preserved, the goal shows the state after one iteration;
usually the invariant is missing a fact about a variable the body changes.

`foreach` loops need no `Spec.Decreases`. To relate a counter to the number of
iterations so far (for example, to rule out overflow of `count++`), a
`Spec.Iteration()` ghost value is *proposed* (§12 Q20).

## Specify a method that mutates objects

*M7.*

Methods that set properties on mutable classes are verified against a heap
model. Say what changes:

```csharp
Spec.Modifies(payments);   // proposed: only these objects (and their fields) change
Spec.Ensures(() => payments.TrueForAll(p => p.IsFinal));
```

Watch for methods that modify objects the caller passed in. The frame clause
makes that visible to callers, and their proofs must account for it. The exact
vocabulary depends on the heap model (§12 Q6).

## Verify a block inside an unverified method

*M7. Syntax is a placeholder (§12 Q4).*

When a method uses things Warrant can't model (reflection, networking types,
caches), you can still verify the part that matters:

```csharp
public bool IsAllowed(IPAddress? ip)                 // not verified
{
    var ranges = LoadRanges();
    using (Verify.Region(
        returns:      (bool allowed) => ranges.Count == 0 ? allowed : !allowed,
        fallsThrough: () => ranges.Count > 0 && ip is not null))
    {
        if (ranges.Count == 0) return true;
        if (ip is null) return false;
    }
    return ranges.Any(r => r.Contains(ip));         // outside the region
}
```

Give a clause for **every** way out of the region: falling through the end,
each `return`, each `throw`. The verifier rejects a region contract that only
describes the fall-through path, because early exits are where these bugs live.

## Run verification in CI

*M5a for the task, M5b for the cache.*

`Warrant.Build` fails the build when a required proof fails, so a normal
`dotnet build` in CI is enough. Two settings matter:

```xml
<PropertyGroup>
  <!-- Re-check cached certificates with the kernel instead of trusting the cache. -->
  <WarrantRecheck>true</WarrantRecheck>
</PropertyGroup>
```

Recheck runs only the kernel, not the tactics, so it costs little compared with
proving from scratch. Turn it on in CI. Publish `obj/warrant/report.md` as a
build artifact so reviewers can read the assumptions.

## Have another kernel check your proofs

*M5a.*

```sh
warrant export --unit Approvals.Approve --out approve.ndjson
```

The file holds the translated method, the theorem and its proof, with every
declaration they depend on, in lean4export format. Lean's own kernel (or any
kernel in the Lean kernel arena) can check it without trusting Warrant.
