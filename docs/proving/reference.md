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
| `Warrant.Build` | netstandard2.0 | the project being verified | The MSBuild task (M5a), which runs the `warrant` CLI it carries under `tools/net10.0/any/`; analyzers come in M5b. Development dependency. |
| `warrant` | net10.0 | a dotnet tool | The CLI and verification engine. |

Neither package is on nuget.org yet; the build integration tests pack them
locally ([REPRODUCING.md](../../REPRODUCING.md)).

## Attributes

| Attribute | On | Since | Meaning |
|---|---|---|---|
| `[Verified]` | method, property | M4 | Translate this member and check its specs. Its callees must be `[Verified]`, have a contract, or be in the semantics library. In M4 the member must be static, or an instance member of a sealed record. Local functions cannot be `[Verified]` in M4, and a local function inside verified code is WRT0002 (region syntax, §12 Q4, may change this). |
| `[Theorem]` | static method returning `Proof` | M4 | A claim to prove. Parameters are universally quantified (M5a); in M4 a theorem has no parameters, and one with parameters is WRT0002. Never executed; calling one is error WRT0003. |
| `[Theorem(TimeoutSeconds = …, TacticFuel = …, KernelFuel = …)]` | the same | M5a | This theorem's budgets: wall-clock seconds, tactic fuel and kernel fuel. Each is a compile-time constant; 0 or unset means the project's setting ([MSBuild properties](#msbuild-properties)). Running out is WRT0006. |
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
| `Spec.ForAll<T>(Func<T, bool>)` | M5a | a theorem statement | `∀ x : T, …`. The claim is a lambda with one parameter and an expression body; nest calls for several variables. Elsewhere it is WRT0004. Throws if it ever runs. |
| `Spec.Exists<T>(Func<T, bool>)` | M5a | a theorem statement | `∃ x : T, …`, with the same rules. |
| `Spec.Requires(bool)` | M6 | start of a method body | Precondition. Assumed in the body, checked at each verified call site. |
| `Spec.Ensures<T>(Func<T, bool>)` | M6 | start of a method body | Postcondition on normal return; the argument is the return value. |
| `Spec.Ensures(Func<bool>)` | M6 | start of a `void` / `Task` method | Postcondition with no return value. |
| `Spec.Assert(bool, params Tactic[])` | M6 | statement | A fact to prove at this point, then usable afterwards. |
| `Spec.Invariant(bool)` | M7 | start of a loop body | Holds before every iteration. |
| `Spec.Decreases(long)` | M5a (recursion), M7 (loops) | first statement of a self-recursive method's block body; start of a loop body (M7) | A measure that strictly decreases on each recursive call or iteration. An `int` argument widens implicitly and is translated in its own type. The measure is clamped at 0, so a call from a state whose measure is already 0 or less cannot be shown to decrease. |
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
| `Prove.That(bool)` | M4 | The claim. A theorem's body is a single `Prove.That` call, and a call anywhere else is WRT0004. Without `.By`, a claim with no parameters or quantifiers is proved by `rfl` or `decide` (M4); a claim with them fails with "unsolved goals", its goal and any counterexample. The default pipeline (M6) will run here. |
| `.By(params Tactic[])` | M5a | Run these tactics in order on the goal. The engine first introduces the theorem's parameters under their C# names. Write the tactics as arguments, not as an array. |

## `Tactic`: proof scripts

Tactics run in the untrusted part of Warrant and produce proof terms. Only
the kernel's check of those terms is trusted, so a tactic bug can make a proof
fail but cannot make a false theorem pass.

Arguments name things in three ways. `nameof(M)` names one `[Verified]`
member or `[Theorem]` of the compilation; an overloaded name is WRT0004. A
string literal names a variable or hypothesis in the goal, such as `"x"` or
`"h"`. `Lean.Const("…")` names a declaration in the semantics bundle.

| Tactic | Since | Effect |
|---|---|---|
| `Tactic.Unfold(params string[] names)` | M5a | Replace each named member by its definition, in turn. Use `nameof`; a string literal is WRT0004. A recursive method is rewritten once with its equation lemma. Fails if the member is not in the goal. |
| `Tactic.Simp(params object[] lemmas)` | M5a | Simplify the goal with the default simp set plus the given lemmas (`nameof` of a theorem, or `Lean.Const`). A string literal is WRT0004. Naming a `[Verified]` method does not unfold it. Closes the goal if it simplifies to `True`. |
| `Tactic.Simp(…).With(decide: …, contextual: …)` | M5a | Turn simp's options on or off. Both are on by default: `decide` settles closed propositions by evaluation, and `contextual` uses an implication's premise while simplifying its conclusion. |
| `Tactic.Omega()` | M5a | Decide linear integer arithmetic over `int`, `long`, `Int` and `Nat`, after moving `int` and `long` facts to `Int` with the bridging lemmas. Uses the hypotheses. On failure it reports Lean's constraints, and the engine adds a counterexample when its boundary search finds one. |
| `Tactic.Intro(params string[] names)` | M5a | Move `∀` variables and `→` premises above the line, one per name; with no names, one, under its own name. |
| `Tactic.Exact(object term)` | M5a | Close the goal with a hypothesis (`"h"`), a theorem (`nameof`) or a bundle lemma (`Lean.Const`). |
| `Tactic.Apply(object term)` | M5a | Reduce the goal with a hypothesis, theorem or lemma whose conclusion matches it; its remaining premises become new goals. |
| `Tactic.Cases(object x)` | M5a | One goal per constructor of the variable or hypothesis named `x` (a string): `bool`, a `[Closed]` enum or class, a record. A type with indices, such as an equation, is not supported yet. |
| `Tactic.Induction(object x)` | M5a | Induction on the variable named `x` (a string), through its type's recursor; each recursive field gets an induction hypothesis named after it, such as `n_ih`. M5a's own types are not recursive, so on them this splits like `Cases`; induction over integers, or over a recursive method's measure, is not supported. |
| `Tactic.AllGoals(Tactic)` | M5a | Run a tactic on every open goal. |
| `Tactic.Try(Tactic)` | M5a | Run a tactic; on failure, leave the goals as they were. |
| `Tactic.Decide()` | *proposed, Q20* | Decide a claim over finite domains by evaluation. |
| `Tactic.Split()` | *proposed, Q20* | Case-split an `if` or `?:` in the goal. |
| `Tactic.Grind()` | M8 | Congruence closure and E-matching. |

The default pipeline for contracts (M6) is VC generation, then `Simp`, then `Omega`.

## `Lean`: library references

| Member | Since | Meaning |
|---|---|---|
| `Lean.Const("Int32.lt_iff_toInt_lt")` | M5a | A declaration in the semantics bundle: the semantics library and the part of Init that `lean/bundle-roots.txt` reaches. Other Init lemmas, such as `Nat.add_comm`, are not in it and fail with "unknown constant". The whole store (Init, then Std and Mathlib) comes with M5b's store. Takes a string literal; it cannot name a variable or a member to unfold. |

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
| Recursion: a method that calls itself, with `Spec.Decreases` as the first statement of a block body | M5a | Mutual recursion, recursion without `Spec.Decreases` and a recursive call inside another's argument are WRT0002. Structural recursion waits for recursive types. |
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
| `recursion` | WRT0002 | Direct or mutual. M5a accepts direct recursion with `Spec.Decreases` (below). |
| `theorem with parameters` | WRT0002 | Accepted from M5a. |
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
| `intercepted call` | WRT0002 | A call that a generated interceptor (`[InterceptsLocation]`) replaces. Reported by `warrant verify --csc-args` and the build (M5a). |
| `unreachable code` | WRT0002 | |
| `integer cast to a closed enum`, `unboxing to a closed enum`, `default of a closed enum` | WRT0002 | Each could give a `[Closed]` enum an unnamed value. A cast also gets WRT0008. |
| `closed enum with duplicate values` | WRT0002 | Two members would be different constructors, while the CLR says they are equal. |
| `relational pattern over a closed type`, `relational comparison over a closed type` | WRT0002 | Closed types have no order. |
| `and/not pattern over a closed type` | WRT0002 | A switch over a closed type is its recursor, so each arm must name members: constants, `or` and `_`. |
| `closed class instance member` | WRT0002 | The model keeps only which instance a value is. |
| `switch section mixing default with case labels` | WRT0002 | `case 1: default:`. Write the `case` as its own section. |
| `unsealed record`, `record struct`, `record with its own equality`, `record with other instance state`, `record with a base record`, `record that is not positional` | WRT0002 | `==` on a record must be field-by-field over its positional properties. |
| `record with its own copy constructor` | WRT0002 | `with` runs the copy constructor, and the model copies the fields, as only the compiler's copy constructor does. |
| `preprocessor conditional` | WRT0002 | A member that translates differently depending on which `#if` symbols the build defines, for example one with an `#if DEBUG` in its body, or one that calls an overload declared under `#if`. Extraction compares every combination of the symbols the conditions test (at most six), skipping combinations that do not compile. Code an `#if` does not affect is translated as usual. M5a takes the real defines from `Csc`. |
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

### The M5a additions

M5a accepts, on top of the M4 subset: theorems with parameters; `Spec.ForAll`
and `Spec.Exists` in theorem statements; `.By(...)` scripts; and a method that
calls itself when its block body starts with `Spec.Decreases`. It adds these
rejections:

| Construct | Code | Notes |
|---|---|---|
| `recursion without Spec.Decreases` | WRT0002 | Including any expression-bodied recursive method, which has no statement to hold the measure. |
| `Spec.Decreases not first` | WRT0002 | The measure is read on entry. |
| `mutual recursion` | WRT0002 | Even with a measure on each method. |
| `nested recursion` | WRT0002 | A recursive call inside another recursive call's argument, such as `F(F(n - 1))`. |
| `lambda with statements` | WRT0002 | The claim of `Spec.ForAll` or `Spec.Exists` must be an expression. |
| `Spec.ForAll outside a theorem statement`, `Spec.Exists outside a theorem statement` | WRT0004 | |
| `quantifier whose claim is not a lambda` | WRT0004 | Including a lambda with more than one parameter. |
| `proof script outside a theorem` | WRT0004 | A `Tactic` or `Lean` call, or `.By`, anywhere but a theorem's script. |
| `nameof of an overloaded method`, `nameof that names no verified member or theorem` | WRT0004 | |
| `string literal where a lemma is expected`, `string literal where a member name is expected` | WRT0004 | In `Tactic.Simp` and `Tactic.Unfold`. |
| `unsupported script argument` | WRT0004 | A step that is not a `Tactic.X(...)` call, an option value that is not a constant, an argument array, or `Lean.Const` of a non-literal. |
| `theorem used in its own proof` | WRT0004 | |

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
| WRT0001 | error | build task | A theorem, postcondition, precondition at a call site, invariant or assertion could not be proved. Shows the goal and any counterexample. In M4: the theorem is false; the message quotes the claim and, for a single `==`, `<`, `<=`, `>` or `>=`, the value of each side (`unknown` for records and closed types). From M5a also: a theorem or a recursive call's decrease obligation was not proved ("could not be proved", "could not be shown to decrease"); the message's first line names the theorem, the tactic's first line and any counterexample, and the later lines give the tactic's details and the goals. |
| WRT0002 | error | analyzer | Construct outside the supported subset in a `[Verified]` member. Names the construct. |
| WRT0003 | error | analyzer | Call to a `[Theorem]` method. |
| WRT0004 | error | analyzer | Malformed spec: `Spec` call outside its allowed position, or a side effect inside a spec. In M4: `Spec.Implies` or `Prove.That` outside a theorem statement. From M5a also: misplaced quantifiers and malformed proof scripts ([The M5a additions](#the-m5a-additions)). |
| WRT0005 | error | analyzer | Call from a verified member to a member with no contract and no `[Verified]`. |
| WRT0006 | error | build task | Verification ran out of fuel or time. Treated as a failure, never as success. From M5a the message names which: `tactic fuel ran out (n steps)`, `kernel fuel ran out (n steps)` or `the time limit of n s was reached`. |
| WRT0007 | error | analyzer | A region contract has no clause for one of the region's exits. |
| WRT0008 | warning | analyzer | A `[Closed]` enum can hold an unnamed value: an integer cast or unboxing conversion to it anywhere in the compilation, or the enum has no member valued 0. |
| WRT0009 | error | analyzer | A `[Closed]` class does not have the closed shape. Names the failed step. |
| WRT0010 | error | build task | Internal error (M5a): the kernel rejected a term Warrant built, the engine could not translate or admit a unit, or the `warrant` CLI failed (the message quotes the end of its error output). Never means the claim is false. Report it as a bug. |
| WRT0011 | warning | `Warrant` package | Nothing is verified (M5a): the project references `Warrant` but not `Warrant.Build`, or sets `WarrantEnabled` to something other than `true`. Silence it with `NoWarn`. Its location is the package's `build/Warrant.targets`. |
| WRT0012 | error | build task | The compilation cannot be rebuilt from Csc's arguments (M5a). Warrant runs the project's source generators, so this means the code does not compile, or a generator could not load (for example one built for a compiler newer than Warrant's Roslyn 5.9.0) or threw; a generator problem fails even when the code compiles without its output. Names the missing symbols and the generator problem. |

There is no analyzer until M5b: extraction raises WRT0002 to WRT0005, WRT0008
and WRT0009 itself, and `warrant translate` and `warrant verify` report them
with the engine's WRT0001, WRT0006 and WRT0010. The build task reports what
`warrant verify` reports, plus WRT0010 when the CLI fails; WRT0011 comes from
the `Warrant` package's own targets.

## MSBuild properties

| Property | Since | Default | Meaning |
|---|---|---|---|
| `WarrantEnabled` | M5a | `true` | Run `warrant verify` after `CoreCompile`. Any other value turns verification off, and the `Warrant` package then warns WRT0011. |
| `WarrantKernelFuel` | M5a | 20,000,000 | Kernel steps per theorem. |
| `WarrantTacticFuel` | M5a | 171,970 | Tactic steps per theorem. |
| `WarrantTimeoutSeconds` | M5a | 30 | Wall-clock seconds per theorem, for tactics and kernel together. |
| `WarrantRecheck` | M5b | `false` | Re-check cached proof certificates with the kernel alone. Recommended in CI. M5a has no cache: every build re-checks every proof. |
| `CheckForOverflowUnderflow` | M4 | `false` | The standard C# setting. Warrant models arithmetic the same way. |

A theorem's own `[Theorem(...)]` arguments override the three budgets. Design-time
builds never verify, and a multi-targeted project verifies once, in the build
of the first entry of `TargetFrameworks`. A build of a single framework that is not
the first (`dotnet build -f`) does not verify, and does not warn.

## CLI

| Command | Since | Purpose |
|---|---|---|
| `warrant check <file.ndjson[.gz]> [--fuel <n>] [--admit-rejected] [--quiet] [--slowest <n>]` | M2 | Check a lean4export file with Warrant's kernel. `--quiet` prints only the summary; `--slowest <n>` also lists the n declarations that took longest, with the time and the memory allocated for each (M5b, used for [the Mathlib run](../mathlib.md)). |
| `warrant export <in> <out>` | M3 | Check a lean4export file, then write what the kernel admitted, for another kernel to re-check. |
| `warrant translate <directory> [--out <file.ndjson>] [--report <file.md>] [--check-overflow] [--bundle <path>]` | M4 | Compile every `.cs` file under the directory, translate its `[Verified]` members and theorems, and print one line per unit plus diagnostics. `--out` writes the semantics bundle and every admitted declaration as lean4export NDJSON; `--report` writes the assumption report as Markdown. Exit 0 when everything translated and every theorem was proved, 1 otherwise, 2 for bad arguments or unreadable input. |
| `warrant verify --csc-args <file> [--project-dir <dir>] [options]`, `warrant verify <directory> [options]` | M5a | Verify in-process, without the server: from the argument file the build writes (as the build task does), or from every `.cs` file under a directory, as `translate` compiles it. Prints one line per unit, the diagnostics and `Warrant: n verified units, n theorems proved, n not proved.` Options: `--format text\|msbuild` (`msbuild` writes one tab-separated `WRT1` record per diagnostic, for the build task); `--out <file.ndjson>` (the bundle and every admitted declaration, as `translate --out`); `--report <dir>` (`report.md` and `report.json`); `--kernel-fuel <n>`, `--tactic-fuel <n>`, `--timeout <seconds>`; `--bundle <path>` (the attribute sidecar must sit next to the bundle and name its hash); `--keep-conditional-check` (keep M4's `#if` combination check with `--csc-args`). The directory mode uses the corpus kernel fuel, 100M. Exit 0 when every theorem was proved (warnings allowed), 1 when an error was reported, 2 for bad arguments or unreadable input, including a missing bundle or a missing or mismatched sidecar. A `<project>` form that evaluates the project file is follow-up work. |
| `warrant explain <unit>` | M5b | Print goals, hypotheses and the tactic trace. |
| `warrant export --unit <unit> --out <file>` | *not built* | Write one unit's certificate. Until then, `warrant verify --out` writes every admitted declaration with the bundle. |
| `warrant check-store` | M5b | Re-check every declaration in the store. |
| `warrant import` | M5b | Add an NDJSON bundle to the store. |

## Assumption report

`warrant translate --report <file.md>` (M4) writes the Markdown form, and
`warrant verify --report <dir>` (M5a) writes `report.md` and `report.json`.
The build does not write a report in M5a. Each unit's line names its status
(`TRANSLATED`, `VERIFIED` or `FAILED`), how a theorem was proved or why it
failed, the kernel version and the semantics bundle's hash, followed by its
assumptions. From M5a, a recursive method, and every unit that depends on one,
lists `Each recursive call returns without exhausting the stack` under
`Assumed (global)`: the model has no stack, and a call that would overflow
the CLR's stack is outside the proof. For example (from
`warrant verify tests/corpus/m5a/accepted --report <dir>`):

```text
Corpus.Recursion.Sum(int)                             TRANSLATED   (kernel: Warrant 1.0, bundle: warrant-semantics sha256:cc74b3a23fc7)
  Assumed (global):
    - Each recursive call returns without exhausting the stack
    - Arithmetic wraps on overflow (overflow checking is off)
    - The semantics bundle models C# 14 int, long and bool
```

The target layout, with contracts (M6):

```text
<Type>.<Member>          VERIFIED | FAILED | TIMEOUT   (kernel: Warrant <version>, cert <hash>)
  Assumed (contracts):    one line per contract clause the proof used
  Assumed (global):       non-null annotations, no concurrent modification, the semantics library
  Proved:                 one line per spec or theorem
```
