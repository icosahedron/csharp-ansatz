# Writing proofs with Warrant

> Status: **partly written ahead of the implementation.** These pages
> describe the target surface in [design §5](../design.md#5-the-c-surface).
> The M4, M5a and M5b parts run today (see [What runs today](#what-runs-today));
> M6 and later do not. Each feature is marked with the milestone that delivers
> it (§11), and anything marked *proposed* is not in the design yet; it is
> tracked in §12. When the implementation and these pages disagree, the
> implementation wins and these pages get fixed.

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

[Proofs that work today](proofs-that-work.md) lists every theorem the corpus proves, how each is proved, and the
three kernels that check them.

If you only read one page, read the tutorial. If a proof is failing and you don't
know why, start with [Reading a failed proof](how-to.md#read-a-failed-proof).

## What you can verify, by milestone

| Milestone | You can… |
|---|---|
| M4 | mark pure methods over `int`/`long`/`bool`, enums and records `[Verified]`, and prove facts about concrete inputs, with `warrant translate` |
| M5a | prove theorems for **all** inputs with tactics, see failed proofs as build errors, use self-recursion with `Spec.Decreases` |
| M5b | rebuild without re-proving (a result cache, re-checked by the kernel with `WarrantRecheck`), keep the checked library loaded in a verification server, cancel a long verification, step through a failed proof with `warrant explain`, see unsupported code in the IDE as you type |
| M6 | write `Spec.Requires`/`Spec.Ensures`, verify methods that call databases and services through contract classes, use `/`, `%`, checked arithmetic and basic `decimal` |
| M7 | verify loops, mutable objects, regions inside unverified methods, full `decimal` and strings |

## What runs today

What runs is M4, M5a ([docs/m5a/](../m5a/README.md)) and M5b
([docs/m5b/](../m5b/README.md)):

- **The build.** A project that references the `Warrant` and `Warrant.Build`
  packages is verified by `dotnet build` and by Visual Studio's MSBuild after
  every compile. A theorem that is not proved fails the build with WRT0001,
  its goal and, when the search finds one, a counterexample. The packages are
  not published to nuget.org yet; the build integration tests pack them
  locally (see [REPRODUCING.md](../../REPRODUCING.md)). From M5b the build
  verifies through a per-user verification server, which it starts when none
  runs, and keeps each unit's result in a cache under `obj/warrant/cache/`, so
  an unchanged rebuild runs no tactics; `WarrantRecheck=true` has the kernel
  re-check every cached proof ([reference](reference.md#msbuild-properties)).
- **`warrant verify`.** The same verification from the command line, on a
  directory of `.cs` files or on the argument file the build writes. It prints
  one line per unit (`translated`, `proved (rfl)`, `proved (decide)`,
  `proved (script)`, `unproved`, `false`, …), the diagnostics in the
  compiler's format, and a summary. `--report` writes the assumption report.
  It verifies in-process unless `--server auto` is given.
- **`warrant explain`.** One unit's proof script step by step, with the goals
  before and after each tactic ([how-to](how-to.md#read-a-failed-proof)).
- **`warrant server`.** `status`, `cancel`, `shutdown` and `report` for the
  verification server.
- **The IDE analyzer.** The `Warrant` package reports unsupported code and
  malformed proof scripts as you type, with the build's own messages.
- **`warrant import` and `check-store`.** Lean libraries in an on-disk store,
  for the CLI; proofs still see only the semantics bundle.
- **`warrant translate`.** M4's verb, which translates and proves by
  computation only.
- **The test suite** (`dotnet test`), which runs the M4 and M5a corpora in
  `tests/corpus/` and checks the translation against the compiled .NET code.

A theorem with parameters states a fact about every value of them and needs a
proof script, `.By(...)`, with the tactics in the
[reference](reference.md#tactic-proof-scripts). A theorem without parameters
can still be proved by computation, as in M4. Recursion works when the method
states a measure with `Spec.Decreases`. Contracts (`Spec.Requires`,
`Spec.Ensures`), external calls, `/`, `%`, `decimal` and strings need M6 or
later.
