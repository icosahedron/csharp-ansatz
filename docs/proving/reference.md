# Reference

> Target syntax; see the [status note](README.md). The **Since** column gives
> the milestone (§11). *Proposed* entries are not in the design yet; the
> question number points to §12. Diagnostic numbers are provisional.

- [Packages](#packages)
- [Attributes](#attributes)
- [`Spec`: specifications](#spec-specifications)
- [`Prove` and `Proof`: theorems](#prove-and-proof-theorems)
- [`Tactic`: proof scripts](#tactic-proof-scripts)
- [`Lean`: library references](#lean-library-references)
- [`Verify`: regions](#verify-regions)
- [Supported C#](#supported-c)
- [Type mapping](#type-mapping)
- [Diagnostics](#diagnostics)
- [MSBuild properties](#msbuild-properties)
- [CLI](#cli)
- [Assumption report](#assumption-report)

## Packages

| Package | Target | Add to | Contents |
|---|---|---|---|
| `Warrant` | netstandard2.0 | the project being verified | Attributes, `Spec`, `Prove`, `Tactic`, `Lean`, `Verify`. No run-time behaviour. |
| `Warrant.Build` | netstandard2.0 | the project being verified | MSBuild task and analyzers. Development dependency. |
| `warrant` | net10.0 | a dotnet tool | The CLI and verification engine. |

## Attributes

| Attribute | On | Since | Meaning |
|---|---|---|---|
| `[Verified]` | method, property, local function | M4 | Translate this member and check its specs. Its callees must be `[Verified]`, have a contract, or be in the semantics library. |
| `[Theorem]` | static method returning `Proof` | M4 | A claim to prove. Parameters are universally quantified (M5a). Never executed; calling one is error WRT0003. |
| `[Closed]` | `enum` | M4 | The enum has only its named values. Casts from integers are reported. |
| `[Closed]` | sealed class with static instances | M4 | The same for closed-set ("smart enum") classes, recognised by shape: sealed, only private constructors, static get-only instances of the type. Any other shape is an error. |
| `[ContractFor(typeof(T))]` | abstract class implementing `T` | M6 | Assumed behaviour of `T`'s members. Never verified; always reported. |
| `[ProofFor(nameof(M))]` | static method | M6 | Supplies tactic hints for the obligations of member `M`. |

## `Spec`: specifications

All `Spec` methods are `[Conditional("WARRANT_CONTRACTS")]` and disappear
from the compiled IL. In specs, `&&`, `||`, `!` and `==` read as logical
and, or, not and equality.

| Member | Since | Where | Meaning |
|---|---|---|---|
| `Spec.Implies(bool a, bool b)` | M4 | any spec | `a → b` |
| `Spec.ForAll<T>(Func<T, bool>)` | M5a | any spec | `∀ x : T, …`. Several type parameters for several variables. |
| `Spec.Exists<T>(Func<T, bool>)` | M5a | any spec | `∃ x : T, …` |
| `Spec.Requires(bool)` | M6 | start of a method body | Precondition. Assumed in the body, checked at each verified call site. |
| `Spec.Ensures<T>(Func<T, bool>)` | M6 | start of a method body | Postcondition on normal return; the argument is the return value. |
| `Spec.Ensures(Func<bool>)` | M6 | start of a `void` / `Task` method | Postcondition with no return value. |
| `Spec.Assert(bool, params Tactic[])` | M6 | statement | A fact to prove at this point, then usable afterwards. |
| `Spec.Invariant(bool)` | M7 | start of a loop body | Holds before every iteration. |
| `Spec.Decreases(int)` | M5a (recursion), M7 (loops) | start of a method or loop body | A non-negative measure that strictly decreases on each recursive call or iteration. |
| `Spec.Old<T>(T)` | *proposed, Q6* | `Spec.Ensures` | The value of an expression on entry. |
| `Spec.Modifies(params object[])` | *proposed, Q6/Q20* | start of a method body | Only these objects may change. No arguments: nothing changes. |
| `Spec.ThrowsOnlyFrom(Expression<Action>)` | *proposed, Q20* | start of a method body | Exceptions can escape only from the named call. |
| `Spec.CallCount(Delegate)` | *proposed, Q5* | `Spec.Ensures` | How many times an external member was called. |
| `Spec.Iteration()` | *proposed, Q20* | `Spec.Invariant` in `foreach` | Number of completed iterations. |

## `Prove` and `Proof`: theorems

```csharp
[Theorem]
static Proof Name(T1 x1, T2 x2) =>
    Prove.That(bool claim)
         .By(params Tactic[] steps);   // optional; M5a
```

| Member | Since | Meaning |
|---|---|---|
| `Prove.That(bool)` | M4 | The claim. Without `.By`, the translator tries `rfl` then `decide` (M4) and then the default pipeline (M6). |
| `.By(params Tactic[])` | M5a | Run these tactics in order on the goal. |

## `Tactic`: proof scripts

Tactics run in the untrusted part of Warrant and produce proof terms. Only
the kernel's check of those terms is trusted, so a tactic bug can make a proof
fail but cannot make a false theorem pass.

| Tactic | Since | Effect |
|---|---|---|
| `Tactic.Unfold(params string[] names)` | M5a | Replace calls to the named members by their definitions. Use `nameof`. |
| `Tactic.Simp(params object[] lemmas)` | M5a | Simplify with the default simp set plus the given lemmas (`nameof` of a theorem or `Lean.Const`). |
| `Tactic.Omega()` | M5a | Decide linear integer arithmetic over `int`, `long`, `Int`, `Nat` (through the bridging lemmas). Reports a counterexample when it can. |
| `Tactic.Intro(params string[])` | M5a | Move `∀` variables and `→` hypotheses above the line. |
| `Tactic.Exact(object)` | M5a | Close the goal with a lemma or hypothesis. |
| `Tactic.Apply(object)` | M5a | Reduce the goal using a lemma whose conclusion matches. |
| `Tactic.Cases(object x)` | M5a | One goal per constructor of `x` (`bool`, closed enum, nullable, record). |
| `Tactic.Induction(object x)` | M5a | Induction on `x`. |
| `Tactic.AllGoals(Tactic)` | M5a | Run a tactic on every open goal. |
| `Tactic.Try(Tactic)` | M5a | Run a tactic; ignore failure. |
| `Tactic.Decide()` | *proposed, Q20* | Decide a claim over finite domains by evaluation. |
| `Tactic.Split()` | *proposed, Q20* | Case-split an `if` or `?:` in the goal. |
| `Tactic.Grind()` | M8 | Congruence closure and E-matching. |

The default pipeline for contracts (M6) is VC generation, then `Simp`, then `Omega`.

## `Lean`: library references

| Member | Since | Meaning |
|---|---|---|
| `Lean.Const("Nat.add_comm")` | M5a | A declaration from the loaded store (Init, the semantics library, and later Std and Mathlib). |

Typed handles such as `Mathlib.Nat.AddComm` come in M8.

## `Verify`: regions

*M7. Placeholder syntax (Q4).*

```csharp
using (Verify.Region(
    returns:      (T r) => ...,          // every return inside the region
    throws:       (Exception e) => ...,  // every throw that escapes it
    fallsThrough: () => ...))            // reaching the end of the block
{
    ...
}
```

Inputs are the variables live on entry. A clause is required for every kind of
exit the block contains.

## Supported C#

| Construct | Since | Notes |
|---|---|---|
| `int`, `long`, `bool`, records, `enum` | M4 | |
| `if`, `switch` statements and expressions, `?:`, `return` | M4 | |
| `let`-style locals (assigned once or reassigned without loops) | M4 | |
| Recursion (structural, or with `Spec.Decreases`) | M5a | |
| `/`, `%`, `checked` | M6 | Division by zero and checked overflow are exceptions. |
| `throw`, `try`/`catch`, null | M6 | |
| `async`/`await` of verified or contracted calls | M6 | |
| `decimal`: comparisons, `+`, `-` | M6 | `1.0m == 1.00m`, also inside records. |
| Loops, mutable classes, `decimal` `*` `/` and rounding, strings | M7 | |
| Collections (`IReadOnlyList<T>`, LINQ), generics, other integer types | *unscheduled, Q14/Q18* | |
| `Guid` | *proposed, Q20* | Opaque, with equality. |
| `float`, `double`, `unsafe`, `dynamic`, reflection, threads | never | Error WRT0002. |

## Type mapping

Summary of [design §6.1](../design.md#61-type-mapping).

| C# | Model |
|---|---|
| `bool` | `Bool` (a proposition inside specs) |
| `int`, `long`, `short`, `sbyte` | `Int32`, `Int64`, `Int16`, `Int8`: two's complement, wrapping |
| `uint`, `ulong`, `ushort`, `byte` | `UInt32` … `UInt8` |
| `checked(...)` | throws `OverflowException` |
| `BigInteger` | `Int` |
| `decimal` | 96-bit mantissa and scale |
| `T?` | `Option T`; non-nullable annotations are assumptions |
| `record` | structure, value equality |
| `enum` | integer with named constants; closed if `[Closed]` |
| `[Closed]` class | `inductive` with one constructor per static instance |
| exceptions | the error branch of the effect monad |

## Diagnostics

Numbers are provisional.

| Code | Severity | Raised by | Meaning |
|---|---|---|---|
| WRT0001 | error | build task | A theorem, postcondition, precondition at a call site, invariant or assertion could not be proved. Shows the goal and any counterexample. |
| WRT0002 | error | analyzer | Construct outside the supported subset in a `[Verified]` member. Names the construct. |
| WRT0003 | error | analyzer | Call to a `[Theorem]` method. |
| WRT0004 | error | analyzer | Malformed spec: `Spec` call outside its allowed position, or a side effect inside a spec. |
| WRT0005 | error | analyzer | Call from a verified member to a member with no contract and no `[Verified]`. |
| WRT0006 | error | build task | Verification ran out of fuel or time. Treated as a failure, never as success. |
| WRT0007 | error | analyzer | A region contract has no clause for one of the region's exits. |
| WRT0008 | warning | analyzer | `[Closed]` type is cast from an integer. |

## MSBuild properties

| Property | Default | Meaning |
|---|---|---|
| `WarrantRecheck` | `false` | Re-check cached proof certificates with the kernel alone. Recommended in CI. |
| `CheckForOverflowUnderflow` | `false` | The standard C# setting. Warrant models arithmetic the same way. |

Other properties (fuel, time limits, report paths) depend on §12 Q8.

## CLI

| Command | Since | Purpose |
|---|---|---|
| `warrant verify <project>` | M5a | Verify in-process, without the server. |
| `warrant explain <unit>` | M5b | Print goals, hypotheses and the tactic trace. |
| `warrant export --unit <unit> --out <file>` | M5a | Write the unit's certificate as lean4export NDJSON. |
| `warrant check-store` | M5b | Re-check every declaration in the store. |
| `warrant import` | M5b | Add an NDJSON bundle to the store. |

## Assumption report

Written to `obj/warrant/report.md` and `report.json` on every build.

```text
<Type>.<Member>          VERIFIED | FAILED | TIMEOUT   (kernel: Warrant <version>, cert <hash>)
  Assumed (contracts):    one line per contract clause the proof used
  Assumed (global):       non-null annotations, no concurrent modification, the semantics library
  Proved:                 one line per spec or theorem
```
