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
| `[Verified]` | method, property | M4 | Translate this member and check its specs. Its callees must be `[Verified]`, have a contract, or be in the semantics library. In M4 the member must be static, or an instance member of a sealed record. Local functions cannot be `[Verified]` in M4, and a local function inside verified code is WRT0002 (region syntax, §12 Q4, may change this). |
| `[Theorem]` | static method returning `Proof` | M4 | A claim to prove. Parameters are universally quantified (M5a); in M4 a theorem has no parameters, and one with parameters is WRT0002. Never executed; calling one is error WRT0003. |
| `[Closed]` | `enum` | M4 | The enum has only its named values, which must be distinct (two members with one value are WRT0002). Integer casts and unboxing to the enum, anywhere in the compilation, are warning WRT0008, and so is an enum with no member valued 0, because `default` then holds an unnamed value. |
| `[Closed]` | sealed class with static instances | M4 | The same for closed-set ("smart enum") classes, recognised by shape: sealed; only private constructors and no primary constructor; every static member of the class's own type is a get-only auto-property or `static readonly` field initialised with a `new` of the class; the constructors are called nowhere else; and there is at least one instance. Any other shape is error WRT0009. Instances are compared with `==`; reading their fields or properties in verified code is WRT0002. |
| `[ContractFor(typeof(T))]` | abstract class implementing `T` | M6 | Assumed behaviour of `T`'s members. Never verified; always reported. |
| `[ProofFor(nameof(M))]` | static method | M6 | Supplies tactic hints for the obligations of member `M`. |

## `Spec`: specifications

The `void` `Spec` methods (`Requires`, `Ensures`, `Assert`, `Invariant`,
`Decreases`) are `[Conditional("WARRANT_CONTRACTS")]` and disappear from the
compiled IL. Methods that return a value cannot be: C# allows `[Conditional]`
only on `void` methods (error CS0578). So `Spec.Implies` stays in the IL and
computes `!a || b` if it ever runs, and `Prove.That` (below) throws
`InvalidOperationException`. In specs, `&&`, `||`, `!` and `==` read as
logical and, or, not and equality.

| Member | Since | Where | Meaning |
|---|---|---|---|
| `Spec.Implies(bool a, bool b)` | M4 | a theorem statement; inside other specs from M6 | `a → b`. In M4, any use outside a theorem statement is WRT0004. |
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
| `Prove.That(bool)` | M4 | The claim. A theorem's body is a single `Prove.That` call, and a call anywhere else is WRT0004. Without `.By`, the translator tries `rfl` then `decide` (M4) and then the default pipeline (M6). |
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
| `int`, `long`, `bool`, sealed records, `enum`, `[Closed]` enums and classes | M4 | See [the M4 subset](#the-m4-subset). |
| `if`, `switch` statements and expressions, `?:`, `return` | M4 | |
| Locals, assigned once or reassigned without loops, including `+=` and `++` | M4 | Parameters cannot be assigned. |
| Recursion (structural, or with `Spec.Decreases`) | M5a | |
| `/`, `%`, `checked` | M6 | Division by zero and checked overflow are exceptions. |
| `throw`, `try`/`catch`, null | M6 | |
| `async`/`await` of verified or contracted calls | M6 | |
| `decimal`: comparisons, `+`, `-` | M6 | `1.0m == 1.00m`, also inside records. |
| Loops, mutable classes, `decimal` `*` `/` and rounding, strings | M7 | |
| Collections (`IReadOnlyList<T>`, LINQ), generics, other integer types | *unscheduled, Q14/Q18* | |
| `Guid` | *proposed, Q20* | Opaque, with equality. |
| `float`, `double`, `unsafe`, `dynamic`, reflection, threads | never | Error WRT0002. |

### The M4 subset

M4 accepts exactly the following. Everything else in a `[Verified]` member or
a theorem is rejected with a diagnostic that names the construct.

| Kind | Accepted in M4 |
|---|---|
| Members | `[Verified]` static methods and properties; `[Verified]` instance methods and computed properties of a sealed record; `[Theorem]` static methods with no parameters whose body is `Prove.That(...)`. |
| Types | `int`, `long`, `bool`. Sealed positional record classes with compiler-generated equality and no instance state besides their positional properties. Enums whose underlying type is `int` or `long`. `[Closed]` enums with distinct member values, and `[Closed]` classes with the closed shape. |
| Values | Literals and constants (a constant expression becomes the constant the compiler folds it to); parameters and locals; enum members and closed-class instances; `new R(...)`, property reads and `with` on records. |
| Operators | `+`, `-`, `*` and unary `-`, `+` on `int` and `long`, unchecked; `==`, `!=`, `<`, `<=`, `>`, `>=` on `int`, `long` and open enums; `==`, `!=` on `bool`, records and closed types; `&&`, `\|\|`, `!`, `&`, `\|`, `^` on `bool`; `?:`. |
| Conversions | `int` to `long`; `long` to `int`, unchecked; an open enum to and from its underlying type. |
| Calls | `[Verified]` members. |
| Statements | Local declarations with an initialiser; `=`, compound assignment, `++` and `--` on locals; `if`/`else`; `switch` statements; `return`. |
| `switch` | Over `int`, `long` and open enums: constant, `_`/`default`, relational (`< 5`) patterns and `and`/`or`/`not` of them; a switch expression needs a `_` arm. Over a `[Closed]` enum: constants, `or` and `_`; a switch expression may instead cover every member. |
| Theorem statements | Everything above, plus `Spec.Implies`. |

These are rejected in M4. The first column is the construct name the
diagnostic message uses.

| Construct | Code | Notes |
|---|---|---|
| `recursion` | WRT0002 | Direct or mutual. M5a. |
| `theorem with parameters` | WRT0002 | M5a. |
| `division`, `remainder` | WRT0002 | M6. A constant expression such as `unchecked(int.MinValue / -1)` is folded first and accepted. |
| `checked arithmetic` | WRT0002 | `checked(...)`, or any arithmetic or narrowing cast in a project with `CheckForOverflowUnderflow` on. A checked widening cast cannot overflow and is accepted. M6. |
| `integer bitwise operator`, `shift` | WRT0002 | `&`, `\|`, `^`, `~`, `<<`, `>>`, `>>>` on integers. Not scheduled. |
| `throw`, `try` | WRT0002 | M6. |
| `non-exhaustive switch over an open enum` | WRT0002 | A switch expression over an open enum without `_`: .NET throws for unnamed values. M6. |
| `null`, `nullable type` | WRT0002 | Including nullable parameters such as `Payment?`. M6. |
| `loop` | WRT0002 | `for`, `foreach`, `while`, `do`. M7. |
| `string`, `decimal` | WRT0002 | M6 and M7. |
| `floating point` | WRT0002 | Never. |
| `local function` | WRT0002 | |
| `unreachable code` | WRT0002 | |
| `integer cast to a closed enum`, `unboxing to a closed enum`, `default of a closed enum` | WRT0002 | Each could give a `[Closed]` enum an unnamed value. A cast also gets WRT0008. |
| `closed enum with duplicate values` | WRT0002 | Two members would be different constructors, while the CLR says they are equal. |
| `relational pattern over a closed type`, `relational comparison over a closed type` | WRT0002 | Closed types have no order. |
| `and/not pattern over a closed type` | WRT0002 | A switch over a closed type is its recursor, so each arm must name members: constants, `or` and `_`. |
| `closed class instance member` | WRT0002 | The model keeps only which instance a value is. |
| `switch section mixing default with case labels` | WRT0002 | `case 1: default:`. Write the `case` as its own section. |
| `unsealed record`, `record struct`, `record with its own equality`, `record with other instance state`, `record with a base record`, `record that is not positional` | WRT0002 | `==` on a record must be field-by-field over its positional properties. |
| `record with its own copy constructor` | WRT0002 | `with` runs the copy constructor, and the model copies the fields, as only the compiler's copy constructor does. |
| `preprocessor conditional` | WRT0002 | Any `#if` in the compilation stops translation, because M4 does not know the defines of the real build. M5a takes them from `Csc`. |
| `cyclic record types` | WRT0002 | Without `null`, no value of such a type can be built. |
| `reserved member name` | WRT0002 | A member of a record or closed type named `rec`, `recOn`, `casesOn`, `noConfusion`, `noConfusionType`, `below`, `brecOn`, `ctorIdx` or `injEq`. |
| `instance member of a class` | WRT0002 | Only records may have verified instance members. |
| `generic type`, `generic member` | WRT0002 | §12 Q14. |
| `depends on a rejected unit` | WRT0002 | A member that uses a rejected type or calls a rejected member. |
| `case guard`, `switch arm guard`, `lambda`, `user-defined operator`, `user-defined conversion`, `indexer`, `property setter`, `ref parameter`, `ref return`, `params argument`, `object initializer`, `object creation`, `constructor other than the primary constructor`, `with on a type that is not a record`, `with on a property that is not positional`, `assignment to a parameter`, `assignment to a field or property`, `local without an initializer`, `expression statement`, `jump statement`, `increment of a non-integer`, `enum arithmetic`, `closed enum constant that names no member`, `pattern that is not a constant`, `type defined outside the compilation`, `enum with an underlying type other than int or long`, `positional property that is not the compiler's auto-property`, `member without a body`, `theorem that is not static`, `theorem that is not Prove.That` | WRT0002 | Less common constructs, each named in its message. Anything else gets a name that starts with `unsupported` (`unsupported expression`, `unsupported operator`, …). |
| A call to a `[Theorem]` | WRT0003 | |
| `Spec.Implies outside a theorem statement`, `Prove.That outside a theorem statement` | WRT0004 | |
| A call to a member that is neither `[Verified]` nor modelled | WRT0005 | For example `System.Math.Abs(int)`. |
| `integer cast to a closed enum`, `unboxing to a closed enum`, `arithmetic on a closed enum`, `closed enum without a member valued 0` | WRT0008 (warning) | Anywhere in the compilation, verified or not. |
| A `[Closed]` class without the closed shape | WRT0009 | Names the failed step: `not sealed`, `constructor that is not private`, `static instance that is not an initialised get-only auto-property or readonly field`, `static constructor`, `constructor called outside the static instances`, or `no static instances`. |

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
| `record` | single-constructor `inductive`; `==` is a generated field-by-field `$eq` |
| `enum` | integer with named constants; closed if `[Closed]` |
| `[Closed]` enum or class | `inductive` with one constructor per member or static instance; `==` compares a generated `$index` |
| exceptions | the error branch of the effect monad |

## Diagnostics

Numbers are provisional.

| Code | Severity | Raised by | Meaning |
|---|---|---|---|
| WRT0001 | error | build task | A theorem, postcondition, precondition at a call site, invariant or assertion could not be proved. Shows the goal and any counterexample. In M4: the theorem is false; the message quotes the claim and, for a single `==`, `<`, `<=`, `>` or `>=`, the value of each side (`unknown` for records and closed types). |
| WRT0002 | error | analyzer | Construct outside the supported subset in a `[Verified]` member. Names the construct. |
| WRT0003 | error | analyzer | Call to a `[Theorem]` method. |
| WRT0004 | error | analyzer | Malformed spec: `Spec` call outside its allowed position, or a side effect inside a spec. In M4: `Spec.Implies` or `Prove.That` outside a theorem statement. |
| WRT0005 | error | analyzer | Call from a verified member to a member with no contract and no `[Verified]`. |
| WRT0006 | error | build task | Verification ran out of fuel or time. Treated as a failure, never as success. |
| WRT0007 | error | analyzer | A region contract has no clause for one of the region's exits. |
| WRT0008 | warning | analyzer | A `[Closed]` enum can hold an unnamed value: an integer cast or unboxing conversion to it anywhere in the compilation, or the enum has no member valued 0. |
| WRT0009 | error | analyzer | A `[Closed]` class does not have the closed shape. Names the failed step. |

M4 has no analyzer (M5b) and no build task (M5a): extraction raises WRT0002 to
WRT0005, WRT0008 and WRT0009 itself, and `warrant translate` reports WRT0001
and WRT0006.

## MSBuild properties

| Property | Default | Meaning |
|---|---|---|
| `WarrantRecheck` | `false` | Re-check cached proof certificates with the kernel alone. Recommended in CI. |
| `CheckForOverflowUnderflow` | `false` | The standard C# setting. Warrant models arithmetic the same way. |

Other properties (fuel, time limits, report paths) depend on §12 Q8.

## CLI

| Command | Since | Purpose |
|---|---|---|
| `warrant check <file.ndjson[.gz]>` | M2 | Check a lean4export file with Warrant's kernel. |
| `warrant export <in> <out>` | M3 | Check a lean4export file, then write what the kernel admitted, for another kernel to re-check. |
| `warrant translate <directory> [--out <file.ndjson>] [--report <file.md>] [--check-overflow] [--bundle <path>]` | M4 | Compile every `.cs` file under the directory, translate its `[Verified]` members and theorems, and print one line per unit plus diagnostics. `--out` writes the semantics bundle and every admitted declaration as lean4export NDJSON; `--report` writes the assumption report as Markdown. Exit 0 when everything translated and every theorem was proved, 1 otherwise, 2 for bad arguments or unreadable input. |
| `warrant verify <project>` | M5a | Verify in-process, without the server. |
| `warrant explain <unit>` | M5b | Print goals, hypotheses and the tactic trace. |
| `warrant export --unit <unit> --out <file>` | M5a | Write the unit's certificate as lean4export NDJSON. |
| `warrant check-store` | M5b | Re-check every declaration in the store. |
| `warrant import` | M5b | Add an NDJSON bundle to the store. |

## Assumption report

Written to `obj/warrant/report.md` and `report.json` on every build (M5a). In
M4, `warrant translate --report` writes the Markdown form; each unit's line
names its status (`TRANSLATED`, `VERIFIED` or `FAILED`), the kernel version and
the semantics bundle's hash, followed by its assumptions.

```text
<Type>.<Member>          VERIFIED | FAILED | TIMEOUT   (kernel: Warrant <version>, cert <hash>)
  Assumed (contracts):    one line per contract clause the proof used
  Assumed (global):       non-null annotations, no concurrent modification, the semantics library
  Proved:                 one line per spec or theorem
```
