# How-to guides

> Target syntax for M6 and later; see the [status note](README.md). Each guide
> names the milestone it needs, and the M4 and M5a guides run today; their
> outputs are copied from `warrant verify`. *Proposed* means the feature is not
> in the design yet (§12).

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
public static class Prices
{
    [Verified]
    public static int Discounted(int price, int discount) =>
        discount >= price ? 0 : price - discount;
}

static class PriceTheorems
{
    [Theorem]
    static Proof DiscountNeverIncreasesPrice(int price, int discount) =>
        Prove.That(Spec.Implies(price >= 0 && discount >= 0,
                                Prices.Discounted(price, discount) <= price))
             .By(Tactic.Unfold(nameof(Prices.Discounted)), Tactic.Simp(), Tactic.Omega());
}
```

This one is proved (`proved (script)`).

Write the claim as an implication when it only holds for some inputs. A
theorem with no `Spec.Implies` claims something for *every* `int`, including
negative ones and `int.MaxValue`.

## Read a failed proof

*M5a.*

A failed proof is a build error (WRT0001) in up to three parts. This is the
previous guide's theorem with only `price >= 0` as its condition, in a file
`Pricing.cs` that starts with `using Warrant;` and `namespace Pricing;`:

```text
Pricing.cs(18,75): error WRT0001: Theorem 'PriceTheorems.DiscountNeverIncreasesPrice(int, int)' could not be proved: omega could not prove the goal. Counterexample: price = 0, discount = -1.
  a possible counterexample may satisfy the constraints
    0 ≤ b ≤ 2147483647
    b + 4294967296*c ≥ 1
    -2147483648 ≤ a ≤ 2147483647
    a + 4294967296*c ≤ -1
    0 ≤ a + b + 4294967296*c ≤ 2147483647
  where
   a := discount.toInt
   b := if (price.toInt - discount.toInt) % ↑(2 ^ 32) < (↑(2 ^ 32) + 1) / 2 then (price.toInt - discount.toInt) % ↑(2 ^ 32) else (price.toInt - discount.toInt) % ↑(2 ^ 32) - ↑(2 ^ 32)
   c := (price.toInt - discount.toInt) / 4294967296

  price discount : Int32
  ⊢ 0 ≤ price → (if price ≤ discount then 0 else price - discount) ≤ price
```

The location is the tactic that failed, here `Tactic.Omega()`.

- **Counterexample.** On the first line, if the engine found one. Believe it
  first: run the method with those values in a unit test. Usually the claim is
  missing a condition (here, `discount >= 0`: `Discounted(0, -1)` is 1).
- **The tactic's explanation.** The indented lines after the first are the
  failing tactic's own message. For `omega` they are constraints over atoms
  (`a`, `b`, …) that describe where it could not rule out a failure; an `if`
  of `%` terms like `b` is how `int` wrap-around looks over `Int`.
- **Unsolved goal.** The last block. Above the line `⊢` are the facts the
  prover had: the theorem's parameters and any hypotheses. Below it is what it
  still had to show; a `Spec.Implies` condition that no `Tactic.Intro` moved
  above the line appears as `… →`. If a fact you expected is missing, the proof
  never learned it: add it to the `Spec.Implies` (or, from M6, to a
  `Spec.Requires` or a contract).
- **No counterexample, goal looks true.** The tactics weren't strong enough.
  See the next guide.

To see every step, run `warrant explain` with the name the diagnostic gives
(M5b). It prints each tactic as you wrote it, with the goals before and after
it, so a `simp` that turned the goal into something `omega` cannot use shows
up as the step where the goal went wrong:

```text
$ warrant explain "Increments.AlwaysLarger(int)" --project-dir src/Payouts
explaining Increments.AlwaysLarger(int)  …/Increments.cs(11,18)

[1] Tactic.Unfold(nameof(Increment))   …/Increments.cs(13,18)
  before:
    x : Int32
    ⊢ Increment x > x
  after:
    x : Int32
    ⊢ x + 1 > x
[2] Tactic.Omega()   …/Increments.cs(13,52)
  before:
    x : Int32
    ⊢ x + 1 > x
  failed:
    omega could not prove the goal:
    …
```

It uses the project's last build (`obj/**/warrant.csc.args`), `--csc-args
<file>`, or `--sources <dir>` for a directory of files, and it never uses the
result cache, because an explanation must come from running the tactics. It
verifies in-process unless you add `--server auto`. Steps inside
`Tactic.AllGoals` or `Tactic.Try` are numbered under them (`[3.1]`, `[3.2]`).

## Get a proof through when the tactics give up

*M5a.*

Try these in order:

1. **Unfold the callees.** `Tactic.Unfold` only unfolds what you name. If the
   goal still mentions a method call, unfold that one too:
   `Tactic.Unfold(nameof(A), nameof(B))`.
2. **Split on cases.** For a `bool`, `[Closed]` enum or closed-set parameter,
   `Tactic.Cases("x")` produces one goal per value; name the variable with a
   string. Follow it with `Tactic.AllGoals(Tactic.Simp())`.
3. **Prove a helper theorem first.** Split a long claim into two `[Theorem]`
   methods and use the first with `Tactic.Apply(nameof(First))` or pass it to
   simp: `Tactic.Simp(nameof(First))`. A theorem cannot name itself.
4. **Use a Lean library lemma.** A declaration in the semantics bundle is
   available by name, for example
   `Tactic.Simp(Lean.Const("Int32.lt_iff_toInt_lt"))`. That is the semantics
   library and the part of Init it depends on, not all of Init; M5b's store
   can hold the rest, but proofs see it only from M6, when Std comes in.
5. **Raise a budget.** If the theorem fails with WRT0006, it ran out of fuel
   or time. Give it more with `[Theorem(TacticFuel = …, TimeoutSeconds = …)]`
   or the project's `WarrantTacticFuel`, `WarrantKernelFuel` and
   `WarrantTimeoutSeconds`.
6. **Check the claim is true.** If none of this works, write a few unit tests
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

Now `Tactic.Cases("status")` gives exactly three goals (M5a), and Warrant warns
(WRT0008) about any integer cast or unboxing conversion to `ClaimStatus`
anywhere in the project.

Two rules keep a closed enum honest:

- **Every member needs its own value.** `Default = Open` would make two names
  for one value, which the model would treat as two different values. Warrant
  rejects such an enum (WRT0002).
- **Give it a member valued 0.** `default(ClaimStatus)`, an uninitialised field
  and a new array all hold 0. If no member is 0, that value has no name, and
  Warrant warns (WRT0008). The first member of an enum without explicit values
  is 0, as `Open` is above.

`[Closed]` works the same way on the "smart enum" pattern: a sealed class with
only private constructors, whose static instances are its only values. Each
instance is a get-only auto-property or a `static readonly` field, initialised
with a `new` of the class:

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

Warrant recognises the class by that shape, not by its base class. If a
`[Closed]` class doesn't have the shape (a public constructor, say), Warrant
reports error WRT0009 naming what is wrong instead of guessing. Classes like
this are more reliably closed than enums: without reflection, no code can
create another instance.

A closed class may have instance fields and properties, like `Name` above, but
verified code can't read them: Warrant models only *which* instance a value
is, so `o.Name` is rejected (WRT0002). Compare instances with `==` instead.
C# can't `switch` over them either, because the instances aren't constants:

```csharp
[Verified]
public static int Code(Outcome o) => o == Outcome.Matched ? 1 : o == Outcome.NoMatch ? 2 : 3;
```

`==` means "the same instance", even if the class overrides `Equals`. When it
does, the assumption report lists that its equality agrees with identity on the
instances. That includes an `==` the class inherits from a base class, as smart
enums usually do.

The class can live in another project, such as a shared library. That project
must import `Warrant.Build` too; set `<WarrantEnabled>false</WarrantEnabled>`
there if it has nothing to verify. Its build then records its source, and the
project you verify checks the class from that source exactly as it checks its
own. The assumption report adds that the referenced assembly is the one built
from the source Warrant checked. If the library changed since it was last
built, the verify fails with WRT0012 and asks you to build it again. A
multi-targeted project can't use a closed class from another project yet,
because each framework ships with its own build of that project.

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
theorem in the same class, or nest a static class for the theorems. The private
method still needs `[Verified]`:

```csharp
internal static class ReassignmentAlerts
{
    [Verified]
    private static bool IsRepeat(int current, int previous, int count) =>
        count > 0 && current == previous;

    static class Theorems
    {
        [Theorem]
        static Proof FirstIsNeverARepeat(int current, int previous) =>
            Prove.That(!IsRepeat(current, previous, 0))
                 .By(Tactic.Unfold(nameof(IsRepeat)), Tactic.Simp());
    }
}
```

This is proved. (The real code this comes from compares `Guid?` values; `Guid`
and nullable types wait for §12 Q20 and M6.)

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

*M5a for the task, M5b for the cache and the server.*

`Warrant.Build` fails the build when a required proof fails, so a normal
`dotnet build` in CI is enough. Check the build log for the summary line,
`Warrant: n verified units, n theorems proved, n not proved.`; a project that
references `Warrant` without `Warrant.Build`, or turns `WarrantEnabled` off,
gets warning WRT0011 instead.

To publish the assumptions for reviewers, run
`warrant verify --csc-args obj/<configuration>/<framework>/warrant.csc.args --report <dir>`
after the build and keep `report.md` as a build artifact; the build itself does
not write a report.

From M5b a result cache under `obj/warrant/cache/` serves unchanged proofs, and
a cache hit is trusted: nothing re-checks it. The cache entry was written only
after the kernel accepted the proof, and a damaged entry is a miss, but someone
who can edit `obj/` could plant one. Where others rely on the build's verdict,
have the kernel re-check every cached proof:

```xml
<PropertyGroup>
  <!-- Re-check cached proofs with the kernel instead of trusting the cache. -->
  <WarrantRecheck>true</WarrantRecheck>
</PropertyGroup>
```

Recheck runs only the kernel, not the tactics, against each theorem as it is
built from the current code, so it costs little compared with proving from
scratch, and the summary says how many it re-checked:
`7 theorems proved (10 from cache, 10 rechecked)`. A fresh CI checkout has an
empty cache, so recheck matters when the job restores `obj/` from an earlier
one. Turn it on in CI.

CI builds (`ContinuousIntegrationBuild=true`) do not start the verification
server: an agent is thrown away after the job, and the server would only
outlive it. Set `WarrantUseServer` yourself to change that. The same setting
matters on a shared machine: the server keeps users apart, but not one user's
elevated and non-elevated processes (GitHub issue #43), so where non-elevated
code is not trusted, build elevated with `WarrantUseServer=false` and
`WarrantRecheck=true` (or `WarrantUseCache=false`), since the result cache in
`obj/` is just as writable. Warrant itself loads from your NuGet package
folder, so full separation also needs a package folder that non-elevated code
cannot write, such as a machine-wide `NUGET_PACKAGES`.

## Have another kernel check your proofs

*M5a.*

```sh
warrant verify src/Payouts --out payouts.ndjson
```

The file holds the semantics bundle and every declaration Warrant admitted
(translated methods, their decrease theorems and equation lemmas, and proved
theorems with their proofs) in lean4export format. Lean's own kernel (or any
kernel in the Lean kernel arena) can check it without trusting Warrant;
`tools/lean-replay` runs Lean's kernel on it, as `scripts/cross-check.sh`
does. A `warrant export --unit` that writes one unit's certificate is not
built yet.
