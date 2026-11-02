# Writing proofs with LeanSharp

> Status: **written ahead of the implementation.** Everything here describes the
> target surface in [design §5](../design.md#5-the-c-surface). Nothing in it runs
> yet. Each feature is marked with the milestone that delivers it (§11), and
> anything marked *proposed* is not in the design yet; it is tracked in §12. When
> the implementation and these pages disagree, the implementation wins and these
> pages get fixed.

This guide is for C# developers who want to prove things about their own code.
You don't need to know Lean. You do need to be comfortable writing a unit test,
since a LeanSharp theorem plays the same role for every input at once.

The guide follows the [Divio documentation system](https://docs.divio.com/documentation-system/),
in four parts that answer four different needs:

| | When you are… | Read |
|---|---|---|
| **Tutorial** | new, and want to see it work end to end | [Your first proofs](tutorial.md) |
| **How-to guides** | trying to get a specific thing done | [How-to guides](how-to.md) |
| **Reference** | looking up an attribute, a `Spec` method, a tactic or a diagnostic | [Reference](reference.md) |
| **Explanation** | wondering why it works this way | [How LeanSharp thinks about your code](explanation.md) |

If you only read one page, read the tutorial. If a proof is failing and you don't
know why, start with [Reading a failed proof](how-to.md#read-a-failed-proof).

## What you can verify, by milestone

| Milestone | You can… |
|---|---|
| M4 | mark pure methods over `int`/`long`/`bool`, enums and records `[Verified]`, and prove facts about concrete inputs |
| M5a | prove theorems for **all** inputs with tactics, see failed proofs as build errors, use recursion |
| M6 | write `Spec.Requires`/`Spec.Ensures`, verify methods that call databases and services through contract classes, use `/`, `%`, checked arithmetic and basic `decimal` |
| M7 | verify loops, mutable objects, regions inside unverified methods, full `decimal` and strings |
