# Writing proofs with Warrant

> Status: **mostly written ahead of the implementation.** Everything here
> describes the target surface in [design §5](../design.md#5-the-c-surface).
> Only the M4 parts run today, and not yet from a build (see
> [What runs in M4](#what-runs-in-m4)). Each feature is marked with the
> milestone that delivers it (§11), and anything marked *proposed* is not in the
> design yet; it is tracked in §12. When the implementation and these pages
> disagree, the implementation wins and these pages get fixed.

This guide is for C# developers who want to prove things about their own code.
You don't need to know Lean. You do need to be comfortable writing a unit test,
since a Warrant theorem plays the same role for every input at once.

The guide follows the [Divio documentation system](https://docs.divio.com/documentation-system/),
in four parts that answer four different needs:

| | When you are… | Read |
|---|---|---|
| **Tutorial** | new, and want to see it work end to end | [Your first proofs](tutorial.md) |
| **How-to guides** | trying to get a specific thing done | [How-to guides](how-to.md) |
| **Reference** | looking up an attribute, a `Spec` method, a tactic or a diagnostic | [Reference](reference.md) |
| **Explanation** | wondering why it works this way | [How Warrant thinks about your code](explanation.md) |

If you only read one page, read the tutorial. If a proof is failing and you don't
know why, start with [Reading a failed proof](how-to.md#read-a-failed-proof).

## What you can verify, by milestone

| Milestone | You can… |
|---|---|
| M4 | mark pure methods over `int`/`long`/`bool`, enums and records `[Verified]`, and prove facts about concrete inputs, with `warrant translate` |
| M5a | prove theorems for **all** inputs with tactics, see failed proofs as build errors, use recursion |
| M6 | write `Spec.Requires`/`Spec.Ensures`, verify methods that call databases and services through contract classes, use `/`, `%`, checked arithmetic and basic `decimal` |
| M7 | verify loops, mutable objects, regions inside unverified methods, full `decimal` and strings |

## What runs in M4

M4 has no build integration: `dotnet build` does not verify anything until
M5a's MSBuild task. What you can run is:

- **`warrant translate <directory>`.** It compiles every `.cs` file under the
  directory with the `Warrant` attributes, translates the `[Verified]` members
  and `[Theorem]`s in the [M4 subset](reference.md#the-m4-subset), and prints
  one line per member: `translated`, `proved (rfl)`, `proved (decide)` or
  `false`, followed by any diagnostics in the compiler's format. `--report`
  writes the assumption report. See [REPRODUCING.md](../../REPRODUCING.md) for
  the commands.
- **The test suite** (`dotnet test`), which runs the M4 corpus in
  `tests/corpus/m4/` and checks the translation against the compiled .NET code.

In M4 a theorem has no parameters, so it states a fact about concrete inputs,
such as `Payout(1000, 250, 500) == 500`, and Warrant proves it by computation.
Theorems for all inputs need M5a's tactics.
