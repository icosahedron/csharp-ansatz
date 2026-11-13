# How-to guides

> Target syntax for M7 and later; see the [status note](README.md). Each guide
> names the milestone it needs, and the M4 to M6 guides run today; their
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
- [Relate two calls of a method that can throw](#relate-two-calls-of-a-method-that-can-throw)
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
    public static int Discounted(int price, int discount)
    {
        Spec.Requires(discount >= 0);
        return discount >= price ? 0 : price - discount;
    }
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

This one is proved (`proved (script)`). The `Spec.Requires` is there because a
verified method's own arithmetic must not overflow (M6, GitHub #244): with a
negative `discount`, `price - discount` could pass `int.MaxValue`. See
[Deal with overflow](#deal-with-overflow).

Write the claim as an implication when it only holds for some inputs. A
theorem with no `Spec.Implies` claims something for *every* `int`, including
negative ones and `int.MaxValue`.

## Read a failed proof

*M5a.*

A failed proof is a build error (WRT0001) in up to three parts. This is the
previous guide's theorem with only `discount >= 0` as its condition, in a file
`Pricing.cs` that starts with `using Warrant;` and `namespace Pricing;`:

```text
Pricing.cs(21,75): error WRT0001: Theorem 'PriceTheorems.DiscountNeverIncreasesPrice(int, int)' could not be proved: omega could not prove the goal. Counterexample: price = -1, discount = 0.
  a possible counterexample may satisfy the constraints
    -2147483648 ≤ b ≤ -1
    0 ≤ a ≤ 2147483647
    a - b ≥ 0
  where
   a := discount.toInt
   b := price.toInt

  price discount : Int32
  ⊢ 0 ≤ discount → (if price ≤ discount then 0 else price - discount) ≤ price
```

The location is the tactic that failed, here `Tactic.Omega()`.

- **Counterexample.** On the first line, if the engine found one. Believe it
  first: run the method with those values in a unit test. Usually the claim is
  missing a condition (here, `price >= 0`: `Discounted(-1, 0)` is 0, more than
  the price).
- **The tactic's explanation.** The indented lines after the first are the
  failing tactic's own message. For `omega` they are constraints over atoms
  (`a`, `b`, …) that describe where it could not rule out a failure.
- **Unsolved goal.** The last block. Above the line `⊢` are the facts the
  prover had: the theorem's parameters and any hypotheses. Below it is what it
  still had to show; a `Spec.Implies` condition that no `Tactic.Intro` moved
  above the line appears as `… →`. If a fact you expected is missing, the proof
  never learned it: add it to the `Spec.Implies` (or, for a contract (M6), to
  the method's `Spec.Requires` or a dependency's contract class).
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

It explains the project's last verifying build as that build verified it
(`obj/**/warrant.explain`: its argument file, the source records of the projects it
references, and its options), or takes `--csc-args <file>`, or `--sources <dir>` for
a directory of files, and it never uses the
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
   library and the part of Init it depends on (and, from M6, the part of
   `Std.Do` contracts use), not all of Init. M5b's store can hold the rest,
   but proofs do not see the store, and no milestone schedules that yet.
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

Put `Spec` calls at the top of a block body: any `Spec.Decreases` first, then
`Spec.Requires`, then `Spec.Ensures`. In a file `Pricing.cs` that starts with
`using System;`, `using Warrant;` and `namespace Pricing;`:

```csharp
public static class Prices
{
    [Verified]
    public static int Discounted(int price, int discount)
    {
        Spec.Requires(price >= 0 && discount >= 0);
        Spec.Ensures<int>(r => r >= 0 && r <= price);
        return discount >= price ? 0 : price - discount;
    }

    [Verified]
    public static int Sale(int price)
    {
        Spec.Requires(price >= 0);
        return Discounted(price, 10);
    }

    [Verified]
    public static int Refund(int price) => Discounted(price, 10);
}
```

`Discounted` and `Sale` are proved with no script. `Refund` is not, because
nothing tells it that `price` is not negative:

```text
Pricing.cs(24,44): error WRT0001: The contract of 'Prices.Refund(int)' could not be proved: precondition of a callee at this call: omega could not prove the goal:
  case hp
  price : Int32
  ⊢ 0 ≤ price
```

- `Spec.Requires` is assumed inside the method and **proved at every verified
  call site**. A caller that can't show `price >= 0` gets a build error at the
  call, as above.
- `Spec.Ensures<T>(r => ...)` must hold on every normal return; `r` is the
  return value. For `void`, `Task` and `ValueTask` methods use
  `Spec.Ensures(() => ...)`. For `async` methods, `T` is the awaited type.
- A caller learns about a callee only through its `Spec.Ensures`: `Sale` knows
  its result is between 0 and `price` without looking at `Discounted`'s body.
- The default procedure proves the contract with no script: it follows the
  method's code, then runs simp and `omega` on what is left. Each condition it
  cannot prove is a separate WRT0001 at the line that produced it, starting
  with its kind (`division by zero`, `postcondition of the method`, …). When
  it gives up on a true contract, add a `Spec.Assert(fact, tactics)` before
  the step that needs the fact, or write a `[ProofFor(nameof(M))]` method
  whose body is `Prove.Contract().By(...)`
  ([proofs that work](proofs-that-work.md#a-contract-proved-by-a-script-m6)).
- A method needs no contract to have an obligation: one that divides, uses
  `checked` arithmetic, `Math.Abs` or reads a nullable value must prove that
  no implicit exception (a zero divisor, overflow, a null read) can happen.
- Arithmetic in a contract must not overflow (GitHub #183): `+`, `-`, `*` and
  unary `-` on `int` and `long` in `Spec.Requires` or `Spec.Ensures` fail the
  proof at that operation unless they provably stay in range, as they do in a
  verified method's body (GitHub #244). `Spec.Ensures<int>(r => r == a + b)` alone fails at
  `a + b`; bound each operand in `Spec.Requires` and it proves
  ([proofs that work](proofs-that-work.md#arithmetic-in-a-contract)). An
  explicit `(int)` cast still truncates. The same holds in a `Spec.Assert`
  condition (GitHub #235), bounded by the `Spec.Requires`, the branch it is
  in, earlier `Spec.Assert`s and the value of a local such as `var s = a + b;`
  (GitHub #246).
- `Spec.Implies(a, b)` is accepted inside `Spec.Requires` and `Spec.Ensures`
  (GitHub #213). `b` is read only when `a` holds, so a division or an
  addition in `b` has to be safe only under `a`
  ([proofs that work](proofs-that-work.md#an-implication-in-a-contract)).
  `Spec.Assert` still rejects it; write `!a || b` there.
- The calls are `[Conditional("WARRANT_CONTRACTS")]`: they don't exist in the
  compiled IL and cost nothing at run time. So **nothing checks
  `Spec.Requires` at run time**, and code Warrant doesn't verify can call the
  method with anything. The report lists each `Spec.Requires` for that reason.
  To protect a method that unverified code can call, check the input with a
  guard that throws (next guides).

## Verify a method that calls a database or service

*M6.*

1. Find the interface the method calls through (a repository, a client, a port).
2. Write a contract class for it in the same project: a `file` or `internal`
   abstract class that implements exactly that interface, marked
   `[ContractFor(typeof(I))]`, with `Spec.Requires` and `Spec.Ensures` in each
   method you need to assume something about, then `return default!;`. The
   interface itself may come from any assembly.
3. Methods you assume nothing about can just `=> default!`. The verifier then
   allows them to return anything and throw anything.

```csharp
public sealed record Claim(int Id, int Amount);

public interface IClaimStore
{
    Task<Claim?> Find(int claimId);
    Task Save(Claim claim);
}

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

4. Inject the dependency through a constructor: a `readonly` field of the
   method's own class, or a primary-constructor parameter that nothing
   assigns. Call its members directly; `await` a call that returns a `Task`
   or `ValueTask` where you make it.

```csharp
public sealed class Claims(IClaimStore store)
{
    [Verified]
    public async Task<int> IdOf(int claimId)
    {
        Spec.Ensures<int>(r => r == 0 || r == claimId);
        var claim = await store.Find(claimId);
        if (claim is null) return 0;
        return claim.Id;
    }
}
```

   This is proved with no script, for every implementation of `IClaimStore`
   that keeps the contract. Each call may see a different store: two calls to
   `Find(claimId)` are not known to agree unless the contract says so.
5. Run `warrant verify --report <dir>` and read the "Assumed (contracts)",
   "Assumed (parameters)" and "Assumed (exceptions)" sections of `report.md`.
   Every line is something you're asking reviewers to take on trust: the
   contract, that `store` and the task `Find` returns are not null, and that
   `Find` may throw, in which case the proof says nothing about the call. Keep
   contracts as weak as the proof allows.

Contracts are **never** global axioms. A wrong contract can't be used to prove
something unrelated; it only weakens the proofs that use it.

A `CancellationToken` parameter may be passed on to a dependency call
(`store.Find(claimId, ct)`) or a verified method: the proof treats it as a
value it cannot look at, and cancellation as one more exception a call may
raise. Reading a token (`ct.IsCancellationRequested`) or making one
(`default`, `CancellationToken.None`) is rejected. A bare `return;` in a
`void` or `Task` method is fine.

Any field of a nullable result may be read after the null test, as often as
you like: `if (claim is null || claim.Amount < 0) return 0; return
claim.Amount;` proves `r >= 0` (GitHub #226).

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

*M6.*

C# `int` and `long` arithmetic wraps around in its default context, and
Warrant models it as the CLR runs it. But a wrap that nobody wrote on purpose is
a bug, so wherever Warrant proves something there is one rule (GitHub #183,
#235, #236, #244): `+`, `-`, `*`, unary `-`, `++`, `--` and compound assignment
on `int` and `long` must not overflow. In a `[Verified]` method's body a
possible overflow fails the build at the operation:

```text
error WRT0001: The contract of 'Prices.Discounted(int, int)' could not be proved: arithmetic overflow: this int/long operation may overflow, where C# would wrap (write unchecked(...) if wrapping is intended): …
```

The condition is proved under what is known at the operation: the method's
`Spec.Requires`, the `if` branch and `switch` section taken, the guard of a
`?:`, `&&` or `||` around it, earlier operations' values, and the
`Spec.Ensures` of a method called before it. When one fails, choose:

- **Bound it.** Add the bound the business logic already guarantees:
  `Spec.Requires(discount >= 0)`, `Spec.Requires(amount <= 1_000_000_000)`.
  Each verified caller now has to show it, and a theorem that calls the method
  has to stay inside it (a `Spec.Implies` condition). A guard in the code
  (`if (x < 1000) return x + 1;`) or a callee's `Spec.Ensures` works too
  ([proofs that work](proofs-that-work.md#a-bounded-method)).
- **Say it wraps on purpose** with `unchecked(...)` or an `unchecked { }`
  block, for hash codes, checksums and code whose point is the wrap-around.
  Explicit `unchecked` has no condition and keeps C#'s wrapped value.
- **Use a wider type** for the intermediate value (`long`), if that's what the
  code should have done anyway.
- **Use `checked`**. Then overflow throws `OverflowException` instead of
  wrapping, and the method's contract obligation has to show it can't happen:
  a contract cannot allow an implicit exception. With
  `Spec.Requires(a >= 0 && a <= 1_000_000 && b >= 0 && b <= 1_000_000)`,
  `return checked(a + b);` is proved; without the bounds, the build fails at
  `a + b` with `overflow in a checked operation`. If the code should throw on
  overflow, throw explicitly (next guide).

The default procedure's `omega` reads linear arithmetic only, so a product
`a * b` of two variables is bounded only through literal bounds on both
factors: `Spec.Requires(0 <= price && price <= 10000 && 0 <= quantity &&
quantity <= 1000)` proves `price * quantity` (GitHub #257), but a factor
bounded only by another variable (`b <= a`) is not, so bound each factor by a
literal. The default procedure also knows nothing of a recursive call's result
(a recursive method has no `Spec.Ensures` yet). These are gaps in the checker,
not in your code. A `[ProofFor]` script does not help a pure method here: it
proves the contract obligation, and the no-overflow obligations are the
default procedure's alone. Write `unchecked` only where wrapping is what the
code means; it removes the check.

What it does know: a local merged from branches keeps the value each branch
gave it (#255), a `switch` section over a `[Closed]` enum knows which members
it takes (#258), and a recursive method may bound its parameters with
`Spec.Requires`, which each recursive call must then satisfy (#256).

In a project with `<CheckForOverflowUnderflow>true</CheckForOverflowUnderflow>`,
all arithmetic is checked, and Warrant follows the project setting.

In what you state, overflow is never silent either (GitHub #183, #235, #236): `+`, `-`,
`*` and unary `-` on `int` and `long` in a `Spec.Requires`, a `Spec.Ensures`,
a `Spec.Assert` or a `[Theorem]`'s statement must not overflow, and a possible overflow fails
the proof at that operation with `well-definedness of a Spec expression`.
Bound the operands (`Spec.Implies(x < 1000 && x > -1000, ...)` in a theorem,
`Spec.Requires` in a method), or, when the claim is about wrapping, write
`unchecked(...)`: explicit `unchecked` wraps on purpose and has no obligation
([proofs that work](proofs-that-work.md#a-bounded-theorem)).

`decimal` (M6) doesn't wrap: `a + b` and `a - b` throw `OverflowException`
when the result is out of range, even in `unchecked` code. A method that adds
`decimal`s therefore needs bounds on its inputs in `Spec.Requires`.
`Tactic.Omega()` reads a `decimal` literal's value (GitHub #217), so a bound
such as `a < 1000m` is a fact `omega` can use.

## Specify a method that throws

*M6.*

Exceptions are part of the model, and the verifier treats two kinds
differently:

- **Implicit exceptions** (a division by zero, `int.MinValue / -1`, checked
  overflow, `Math.Abs(int.MinValue)`, `x.Value` on null, a null dereference)
  are never allowed. The proof must show each one can't happen under the
  method's `Spec.Requires`, or the build fails at that operation.
- **Explicit throws** (`throw new T(...)`, with constant or parameter
  arguments and `T` a `System` exception or a plain subclass of one) and
  exceptions from a dependency are allowed. `Spec.Ensures` constrains
  **normal** returns only, and the report lists each throw the verifier
  could not show unreachable under "Assumed (exceptions)".

`Spec.Requires` is not checked at run time (see
[Add preconditions and postconditions](#add-preconditions-and-postconditions)).
To protect a method that unverified code can call, check the input with a
guard that throws, which the proof covers. As the first member of
`public static class Installments`, in a file `Installments.cs` with the same
first lines as `Pricing.cs` above:

```csharp
[Verified]
public static int PerItem(int total, int count)
{
    if (count <= 0) throw new ArgumentOutOfRangeException(nameof(count));
    return total / count;
}
```

This is proved: after the guard, `count` is positive, so the division can't
divide by zero or overflow. The report says what the proof leaves out:

```text
  Assumed (exceptions):
    - Pricing.Installments.PerItem(int, int) may throw System.ArgumentOutOfRangeException (the throw at Installments.cs:11); its proof says nothing about a call that ends in it
```

The same method with `Spec.Requires(count > 0)` in place of the guard is also
proved, but then a caller Warrant doesn't verify can still pass 0, and the
division throws `DivideByZeroException` at run time. With neither, the build
fails at the division twice: `division by zero` and
`overflow in a checked operation` (`int.MinValue / -1`).

- A throw the verifier can show unreachable under `Spec.Requires` is not
  listed.
- To prove a method never throws explicitly, add `Spec.NoThrow()` after its
  `Spec.Requires` (and before any `Spec.Ensures`). The build then fails at any
  `throw` the `Spec.Requires` does not rule out, with `an explicit throw is
  reachable under the Requires (Spec.NoThrow)`, instead of listing it. The
  guard can stay for callers Warrant doesn't verify:

  ```csharp
  [Verified]
  public static int PerItem(int total, int count)
  {
      Spec.Requires(count > 0);
      Spec.NoThrow();
      if (count <= 0)
      {
          throw new ArgumentOutOfRangeException(nameof(count));
      }
      return total / count;
  }
  ```

  An exception from a dependency is still allowed and listed. A verified
  method it calls that can throw needs `Spec.NoThrow` too, or the build fails
  at the call; a caller without `Spec.NoThrow` uses its contract as before.
  `Spec.NoThrow` is not valid in a `[ContractFor]` class.
- A method that throws on every path proves any `Spec.Ensures`, since it
  never returns normally; the report lists the throw.
- `try`/`catch` is rejected (WRT0002 `try`), and no milestone schedules it.
- To say which calls an exception can come from, `Spec.ThrowsOnlyFrom(...)` is
  *proposed* (§12 Q20).

## Relate two calls of a method that can throw

*M6.*

A `[Theorem]` cannot call a method that can raise (one that throws, divides by
a variable, uses checked arithmetic, reads a nullable value, calls a method
with `Spec.Requires`, and so on): the build rejects it with WRT0002
`theorem calling a raising method`, because a theorem is a claim and the
method is a program. That method's `Spec.Ensures` speaks about one call, so a
property that relates two calls, such as monotonicity, needs one of two routes.

**A wrapper method.** Write a `[Verified]` method that makes both calls and
states the relation as its own `Spec.Ensures`. The default procedure proves it
with no script: at each call it checks the callee's `Spec.Requires` and uses
its `Spec.Ensures`, without unfolding the callee.

```csharp
[Verified]
public static int Scale(int x)
{
    Spec.Requires(x >= -1000 && x <= 1000);
    Spec.Ensures<int>(r => r == x + x);
    if (x < 0) throw new ArgumentException("x");
    return checked(x + x);
}

[Verified]
public static bool Monotone(int x, int y)
{
    Spec.Requires(0 <= x && x <= y && y <= 1000);
    Spec.Ensures<bool>(r => r);
    return Scale(x) <= Scale(y);
}
```

Both are proved. The wrapper knows only what the callee's `Spec.Ensures`
says, so that `Spec.Ensures` must be strong enough to imply the relation:
`r >= 0` alone would not prove `Monotone`. The report lists `Scale`'s contract
under the assumptions of `Monotone`. Nothing calls `Monotone`; it exists to be
proved.

**An exact `Spec.Ensures`.** When the method's `Spec.Ensures` pins its result,
`r == <pure expression>`, the relation is a theorem about that expression, or
about a pure `[Verified]` helper that computes it:

```csharp
[Theorem]
static Proof DoubleIsMonotone(int x, int y) =>
    Prove.That(Spec.Implies(0 <= x && x <= y && y <= 1000, x + x <= y + y))
         .By(Tactic.Simp(), Tactic.Omega());
```

Both routes work for `r == x * 3` too: `omega` alone cannot always use the
bounds to rule out `int` multiplication's wrap-around, so when it fails,
`Tactic.Omega()` proves `x * 3` in range under them and uses its exact value
(GitHub #237).

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

This is proved. (The real code this comes from compares `Guid?` values.
Nullable values are accepted from M6; `Guid` waits for §12 Q20, which no
milestone schedules.)

`[Theorem]` methods are never emitted into your call graph. You can leave them
in production code.

## Specify an expression-bodied member

*M6.*

`Spec.Ensures` is a statement, so it needs a block body; in an
expression-bodied member it is WRT0002 (design §12 Q17). Rewrite

```csharp
[Verified]
public static int Capped(int amount, int limit) => amount > limit ? limit : amount;
```

as

```csharp
[Verified]
public static int Capped(int amount, int limit)
{
    Spec.Ensures<int>(r => r <= limit);
    return amount > limit ? limit : amount;
}
```

This is proved with no script. Or leave the member alone and state the
property as a `[Theorem]` about it, which needs no change to the member, as
long as the member cannot throw (a theorem cannot call one that can). A code
fix that does the rewrite is deferred.

A `bool` postcondition that needs a case split on a `bool` parameter, such as
`r => !flagged || r`, or on a null test, such as
`r => x is null ? r == 0 : r == x.Value`, is proved too: the default procedure
splits a `bool` that `omega` leaves, up to three of them on one path
(GitHub #227, #245).

## Keep logging out of the proof

*Proposed (§12 Q20); not in M6, and it needs M7's strings.*

Logging calls in a verified method are calls to code without a contract, and
interpolated messages pull strings into the proof. The proposed fix is a
standard contract that says logging has no effect on verified state, listed in
the assumption report like any other contract. Until then a verified method
cannot log: a contract class for your logging interface is accepted, but a
verified call to a member whose signature has a `string` is rejected
(WRT0002), so keep logging in the unverified caller.

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
`Warrant: n verified units, n theorems proved, n not proved.` (the proved and
not-proved figures count theorems; when a method's contract or another
non-theorem unit fails, the line adds `; n other units not verified`, GitHub
#225); a project that
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
