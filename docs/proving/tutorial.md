# Tutorial: your first proofs

> Target syntax; see the [status note](README.md). Part 1 needs M5a, part 2 needs M6.

In this tutorial you will take a small insurance payout calculation, prove three
things about it, watch LeanSharp refuse a fourth claim that looks obviously true,
fix the claim, and then verify a method that reads from a database. It takes
about 30 minutes.

You will need the .NET 10 SDK and an empty class library.

## Part 1: a pure method

### Step 1: add LeanSharp

```sh
dotnet new classlib -n Payouts
cd Payouts
dotnet add package LeanSharp
dotnet add package LeanSharp.Build
```

`LeanSharp` holds the attributes and the `Spec`, `Prove` and `Tactic` classes.
None of them do anything at run time. `LeanSharp.Build` runs the verifier after
every build.

### Step 2: write the method

Replace `Class1.cs` with `Payouts.cs`:

```csharp
using LeanSharp;

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

`[Verified]` tells LeanSharp to translate this method into its logic. Build:

```sh
dotnet build
```

The build succeeds and prints one line from LeanSharp:

```text
LeanSharp: 1 verified unit, 0 theorems.
```

Nothing has been proved yet. LeanSharp has only checked that the method is
inside the supported subset and translated it.

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

Build again:

```text
LeanSharp: 1 verified unit, 2 theorems proved.
```

These look like unit tests, and for now they are: each one checks one input.
The difference is that they are checked by evaluating the translated method
inside the kernel, not by running it. Notice that you never call a `[Theorem]`
method yourself; the analyzer reports an error if you try.

### Step 4: prove something for every input

Theorems with parameters are claims about **all** values of those parameters.
Add:

```csharp
    [Theorem]
    static Proof PayoutIsNeverNegative(int loss, int deductible, int limit) =>
        Prove.That(PayoutRules.Payout(loss, deductible, limit) >= 0)
             .By(Tactic.Unfold(nameof(PayoutRules.Payout)), Tactic.Simp(), Tactic.Omega());
```

`.By(...)` is the proof script: unfold the method's definition, simplify, then
let `omega` (a decision procedure for integer arithmetic) finish. Build:

```text
Payouts.cs(31,5): error LSV0001: Theorem 'PayoutIsNeverNegative' could not be proved.
  omega found a counterexample:
    loss = 1, deductible = 0, limit = -1
  Unsolved goal:
    loss deductible limit : Int32
    h : deductible < loss
    ⊢ 0 ≤ if limit < loss - deductible then limit else loss - deductible
```

The build failed, and the counterexample is right: with a negative limit, the
method returns a negative payout. The theorem was wrong, not the proof.

### Step 5: state what you actually mean

Payouts are only meaningful for non-negative deductibles and limits. Say so:

```csharp
    [Theorem]
    static Proof PayoutIsNeverNegative(int loss, int deductible, int limit) =>
        Prove.That(Spec.Implies(deductible >= 0 && limit >= 0,
                                PayoutRules.Payout(loss, deductible, limit) >= 0))
             .By(Tactic.Unfold(nameof(PayoutRules.Payout)), Tactic.Simp(), Tactic.Omega());
```

Build. It passes.

Now try removing `deductible >= 0` from the condition and building again. The
counterexample this time is less obvious:

```text
    loss = 2147483647, deductible = -1, limit = 0
```

`loss - deductible` is `int.MaxValue + 1`, which wraps around to
`int.MinValue` in C#. LeanSharp models `int` the way the CLR runs it, so it
finds the overflow that a proof about mathematical integers would have missed.
Put the condition back.

### Step 6: one more, without help

Write a theorem that the payout never exceeds the limit when the limit is
non-negative. Use the same proof script. (Hint: does it need `deductible >= 0`?
Try it without, and read the counterexample if it fails.)

## Part 2: a method that reads from a database

### Step 7: a service with an external dependency

Add `Approvals.cs`:

```csharp
using LeanSharp;

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
Approvals.cs(21,40): error LSV0005: 'IPolicyStore.GetPolicy' is called from a verified method but has no contract.
```

LeanSharp doesn't know what the database returns, and it won't guess.

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
policies have non-negative deductibles and limits". Nothing checks it. LeanSharp
proves that `Approve` is correct for every store that keeps this promise.

Build. It passes, and a report appears at `obj/leansharp/report.md`:

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

Delete `p.Deductible >= 0 &&` from the contract and build. The postcondition
now fails:

```text
    loss = 0, p.Deductible = -5, p.Limit = 10
```

With a negative deductible, a zero loss still produces a payout. Now put it back
and delete `&& p.Limit >= 0` instead. The build still passes: the postcondition
never needed the limit. Experiments like this show which assumptions a proof
actually depends on. Put the contract back as it was.

## What you've done

You marked a method `[Verified]`, proved concrete and universal theorems about
it, read a counterexample (including an overflow), turned a false claim into a
true one, wrote a postcondition, and verified a method against a database
contract.

Next:

- The [how-to guides](how-to.md) cover loops, closed sets, mutable objects and
  what to do when tactics give up.
- [How LeanSharp thinks about your code](explanation.md) explains why `int`
  wraps, why contracts are hypotheses, and what the kernel does and doesn't
  promise.
