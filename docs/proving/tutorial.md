# Tutorial: your first proofs

> Part 1 runs today (M5a): every output in it was copied from `warrant verify`
> run on the code it shows. Part 2 is still target syntax: M6 built contracts
> and contract classes, but Part 2 has not been run, and it differs from what
> M6 does in places. The build writes no report (run
> `warrant verify --report`), the report's layout is the one in the
> [reference](reference.md#assumption-report), and a failing contract shows
> its goal, not a counterexample. See the
> [how-to guides](how-to.md#verify-a-method-that-calls-a-database-or-service)
> for an example that runs, and the [status note](README.md).

In this tutorial you will take a small insurance payout calculation, prove three
things about it, watch Warrant refuse a fourth claim that looks obviously true,
fix the claim, and then verify a method that reads from a database. It takes
about 30 minutes.

You will need the .NET 10 SDK and an empty class library.

## Part 1: a pure method

### Step 1: add Warrant

```sh
dotnet new classlib -n Payouts
cd Payouts
dotnet add package Warrant
dotnet add package Warrant.Build
```

`Warrant` holds the attributes and the `Spec`, `Prove` and `Tactic` classes.
None of them do anything at run time. `Warrant.Build` runs the verifier after
every build, and fails the build when a theorem is not proved.

The packages are not on nuget.org yet. Until they are, build the `warrant`
tool from source ([REPRODUCING.md](../../REPRODUCING.md)) and run
`warrant verify .` in the project's directory after each change. It runs the
same verification as the build and prints the same diagnostics. The outputs
below are from `warrant verify`; `dotnet build` shows the diagnostics in
MSBuild's format, with the file, line and column in front of every line, and
ends with the same `Warrant:` summary line.

### Step 2: write the method

Replace `Class1.cs` with `Payouts.cs`:

```csharp
using Warrant;

namespace Payouts;

public static class PayoutRules
{
    /// <summary>What the insurer pays: the loss above the deductible, capped at the limit.</summary>
    [Verified]
    public static int Payout(int loss, int deductible, int limit)
    {
        if (loss <= deductible) return 0;
        var covered = loss - deductible;
        return covered > limit ? limit : covered;
    }
}
```

`[Verified]` tells Warrant to translate this method into its logic. Verify:

```text
verifying 1 file(s) in .
  Payouts.PayoutRules.Payout(int, int, int)  unproved
./Payouts.cs(12,23): error WRT0001: The contract of 'PayoutRules.Payout(int, int, int)' could not be proved: arithmetic overflow: this int/long operation may overflow, where C# would wrap (write unchecked(...) if wrapping is intended): omega could not prove the goal:
  case h.left
  loss deductible limit : Int32
  h : loss.toInt - deductible.toInt < -2147483648 ∨ 2147483647 < loss.toInt - deductible.toInt
  h : deductible < loss
  ⊢ False
Warrant: 1 verified units, 0 theorems proved, 0 not proved.
```

Before you have claimed anything, Warrant already has one question about the
method: can `loss - deductible` (line 12, column 23) overflow? In C# it would
silently wrap around, and Warrant treats that as a bug unless the code says
`unchecked`. Under what it knows there (`deductible < loss`, from the `if`), it
cannot rule it out: with `loss = int.MaxValue` and `deductible = -1` the
difference does not fit in an `int`.

A deductible is never negative, so say so with a precondition, as the first line
of the method:

```csharp
        Spec.Requires(deductible >= 0);
```

Verify again:

```text
verifying 1 file(s) in .
  Payouts.PayoutRules.Payout(int, int, int)  translated
Warrant: 1 verified units, 0 theorems proved, 0 not proved.
```

The method is checked: its arithmetic cannot overflow under its precondition.
Nothing has been proved about what it computes yet.

### Step 3: prove a fact about one input

Add a second class to the same file:

```csharp
static class PayoutTheorems
{
    [Theorem]
    static Proof CappedAtTheLimit() =>
        Prove.That(PayoutRules.Payout(loss: 1000, deductible: 250, limit: 500) == 500);

    [Theorem]
    static Proof NothingBelowTheDeductible() =>
        Prove.That(PayoutRules.Payout(loss: 100, deductible: 250, limit: 500) == 0);
}
```

Verify again:

```text
verifying 1 file(s) in .
  Payouts.PayoutRules.Payout(int, int, int)           translated
  Payouts.PayoutTheorems.CappedAtTheLimit()           proved (rfl)
  Payouts.PayoutTheorems.NothingBelowTheDeductible()  proved (rfl)
Warrant: 3 verified units, 2 theorems proved, 0 not proved.
```

These look like unit tests, and for now they are: each one checks one input.
The difference is that they are checked by evaluating the translated method
inside the kernel, not by running it (`rfl`). Each also checks that its
arguments meet `Payout`'s precondition: a theorem may only ask about a method
where the method's own `Spec.Requires` holds. Notice that you never call a
`[Theorem]` method yourself; calling one is error WRT0003.

### Step 4: prove something for every input

Theorems with parameters are claims about **all** values of those parameters.
Add to `PayoutTheorems`:

```csharp
    [Theorem]
    static Proof PayoutIsNeverNegative(int loss, int deductible, int limit) =>
        Prove.That(PayoutRules.Payout(loss, deductible, limit) >= 0)
             .By(Tactic.Unfold(nameof(PayoutRules.Payout)), Tactic.Simp(), Tactic.Omega());
```

`.By(...)` is the proof script: unfold the method's definition, simplify, then
let `omega` (a decision procedure for integer arithmetic) finish. Verify:

```text
verifying 1 file(s) in .
  Payouts.PayoutRules.Payout(int, int, int)                    translated
  Payouts.PayoutTheorems.CappedAtTheLimit()                    proved (rfl)
  Payouts.PayoutTheorems.NothingBelowTheDeductible()           proved (rfl)
  Payouts.PayoutTheorems.PayoutIsNeverNegative(int, int, int)  unproved
./Payouts.cs(30,20): error WRT0001: Theorem 'PayoutTheorems.PayoutIsNeverNegative(int, int, int)' could not be proved: omega could not prove the goal:
  a possible counterexample may satisfy the constraints
    -2147483648 ≤ a ≤ -1
  where
   a := deductible.toInt

  loss deductible limit : Int32
  ⊢ deductible ≥ 0
Warrant: 4 verified units, 2 theorems proved, 1 not proved.
```

The location (line 30, column 20) is the call `PayoutRules.Payout(...)`, and the
goal is `Payout`'s precondition: the theorem asks about every `deductible`,
including the negative ones `Payout` does not accept. Read the first line and
the last block first; the constraints in between are `omega`'s description of
where it could not rule out a failure, here every negative deductible. The
theorem was wrong, not the proof.

### Step 5: state what you actually mean

Payouts are only meaningful for non-negative deductibles and limits. Say so:

```csharp
    [Theorem]
    static Proof PayoutIsNeverNegative(int loss, int deductible, int limit) =>
        Prove.That(Spec.Implies(deductible >= 0 && limit >= 0,
                                PayoutRules.Payout(loss, deductible, limit) >= 0))
             .By(Tactic.Unfold(nameof(PayoutRules.Payout)), Tactic.Simp(), Tactic.Omega());
```

Verify. It passes:

```text
  Payouts.PayoutTheorems.PayoutIsNeverNegative(int, int, int)  proved (script)
Warrant: 4 verified units, 3 theorems proved, 0 not proved.
```

Now try removing `deductible >= 0` from the condition, leaving
`Spec.Implies(limit >= 0, …)`, and verify again. The precondition fails again,
now with the premise `limit ≥ 0` among the hypotheses:

```text
… could not be proved: omega could not prove the goal:
  …
  loss deductible limit : Int32
  h : limit ≥ 0
  ⊢ deductible ≥ 0
```

Without the precondition, `loss - deductible` could be `0 - int.MinValue`, which
is `int.MaxValue + 1` and wraps around to `int.MinValue` in C#. Warrant models
`int` the way the CLR runs it, but it does not let a verified method or a
theorem lean on the wrap-around by accident: arithmetic that may overflow is an
error unless it is written `unchecked(...)`. Put the condition back.

### Step 6: one more, without help

Write a theorem that the payout never exceeds the limit when the limit is
non-negative. Use the same proof script. (Hint: what does `Payout`'s
precondition ask of the theorem?)

## Part 2: a method that reads from a database

### Step 7: a service with an external dependency

Add `Approvals.cs`:

```csharp
using Warrant;

namespace Payouts;

public sealed record Policy(int Id, int Deductible, int Limit, bool IsActive);

public enum ApprovalResult { Approved, PolicyNotFound, PolicyInactive, NothingToPay }

public interface IPolicyStore
{
    Task<Policy?> GetPolicy(int policyId);
}

public sealed class Approvals(IPolicyStore store)
{
    [Verified]
    public async Task<ApprovalResult> Approve(int policyId, int loss)
    {
        Spec.Ensures<ApprovalResult>(r => Spec.Implies(r == ApprovalResult.Approved, loss > 0));

        var policy = await store.GetPolicy(policyId);
        if (policy is null) return ApprovalResult.PolicyNotFound;
        if (!policy.IsActive) return ApprovalResult.PolicyInactive;
        if (PayoutRules.Payout(loss, policy.Deductible, policy.Limit) <= 0) return ApprovalResult.NothingToPay;
        return ApprovalResult.Approved;
    }
}
```

`Spec.Ensures` states a postcondition: whenever `Approve` returns `Approved`,
the loss was positive. Build:

```text
Approvals.cs(21,40): error WRT0005: 'IPolicyStore.GetPolicy' is called from a verified method but has no contract.
```

Warrant doesn't know what the database returns, and it won't guess.

### Step 8: write the contract

Add to the same file:

```csharp
[ContractFor(typeof(IPolicyStore))]
file abstract class PolicyStoreContract : IPolicyStore
{
    public Task<Policy?> GetPolicy(int policyId)
    {
        Spec.Ensures<Policy?>(p => p is null || (p.Id == policyId && p.Deductible >= 0 && p.Limit >= 0));
        return default!;
    }
}
```

This is an **assumption**: "the store returns the policy asked for, and stored
policies have non-negative deductibles and limits". Nothing checks it. Warrant
proves that `Approve` is correct for every store that keeps this promise.

Build. It passes, and a report appears at `obj/warrant/report.md`:

```text
Approvals.Approve         VERIFIED
  Assumed (contracts):
    - IPolicyStore.GetPolicy returns null or the requested policy, with Deductible >= 0 and Limit >= 0
  Assumed (global):
    - Non-nullable reference annotations on Policy hold
  Proved:
    - Approved implies loss > 0
```

Read the "Assumed" section as the list of things a reviewer has to believe.
If a policy row in production could have a negative limit, this is where you'd
find out the proof doesn't cover it.

### Step 9: check the proof used your contract

Delete `p.Deductible >= 0 &&` from the contract and build. The call to
`Payout` now fails its precondition, `deductible >= 0`: nothing says a stored
deductible is not negative. Now put it back
and delete `&& p.Limit >= 0` instead. The build still passes: the postcondition
never needed the limit. Experiments like this show which assumptions a proof
actually depends on. Put the contract back as it was.

## What you've done

You marked a method `[Verified]`, proved concrete and universal theorems about
it, bounded its arithmetic so it cannot overflow, read a failed goal, turned a
false claim into a true one, wrote a postcondition, and verified a method against a database
contract.

Next:

- The [how-to guides](how-to.md) cover loops, closed sets, mutable objects and
  what to do when tactics give up.
- [How Warrant thinks about your code](explanation.md) explains why `int`
  wraps, why contracts are hypotheses, and what the kernel does and doesn't
  promise.
