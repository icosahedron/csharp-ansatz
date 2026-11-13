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
| `Warrant` | netstandard2.0 | the project being verified | Attributes, `Spec`, `Prove`, `Tactic`, `Lean`, `Verify`. No run-time behaviour. From M5b it also carries the IDE analyzer (`analyzers/dotnet/cs/Warrant.Analyzers.dll`), which runs only in design-time builds. |
| `Warrant.Build` | netstandard2.0 | the project being verified | The MSBuild task (M5a), which runs the `warrant` CLI it carries under `tools/net10.0/any/`, and, from M5b, the verification server `warrant-server.dll` beside it. Development dependency. |
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
| `[Closed]` | sealed class with static instances | M4 | The same for closed-set ("smart enum") classes, recognised by shape: sealed; only private constructors and no primary constructor; every static member of the class's own type is a get-only auto-property or `static readonly` field initialised with a `new` of the class; the constructors are called nowhere else, and no visible code creates an instance or replaces a static one without one (`MemberwiseClone` in the class or a base class, a `with` expression, or an `[UnsafeAccessor]` that calls a constructor or `MemberwiseClone` or reaches a field); and there is at least one instance. Any other shape is error WRT0009. Instances are compared with `==`; reading their fields or properties in verified code is WRT0002. |
| `[ContractFor(typeof(T))]` | `file` or `internal` abstract class implementing interface `T` | M6 | Assumed behaviour of `T`'s members, stated with `Spec.Requires` and `Spec.Ensures` ([the M6 dependency rejections](#the-m6-dependency-rejections) give the shape). Never verified; the contracts a proof uses are always reported. |
| `[ProofFor(nameof(M))]` | static, parameterless method in `M`'s class whose body is `Prove.Contract().By(...)` | M6 | Its script proves `M`'s contract obligation in place of the default procedure. |

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
| `Spec.Implies(bool a, bool b)` | M4; in contracts M6 (#213) | a theorem statement, or a `Spec.Requires` or `Spec.Ensures` condition | `a → b`. In a contract, `b`'s partial operations and overflow checks are under `a`. Anywhere else, `Spec.Assert` included, it is WRT0004; write `!a \|\| b` there. |
| `Spec.ForAll<T>(Func<T, bool>)` | M5a | a theorem statement | `∀ x : T, …`. The claim is a lambda with one parameter and an expression body; nest calls for several variables. Elsewhere it is WRT0004. Throws if it ever runs. |
| `Spec.Exists<T>(Func<T, bool>)` | M5a | a theorem statement | `∃ x : T, …`, with the same rules. |
| `Spec.Requires(bool)` | M6 | start of a block body, after any `Spec.Decreases` | Precondition. Assumed in the body, proved at each verified call site. Not checked at run time or at call sites Warrant does not verify; the report lists it. |
| `Spec.NoThrow()` | M6 (#182) | start of a block body, after any `Spec.Requires` and before any `Spec.Ensures`; at most once | No explicit `throw` of the method is reachable under its `Spec.Requires`: a reachable one fails the build at the `throw` instead of being listed. An exception from a dependency is still allowed. A raising verified callee needs it too. Holds already of a method that cannot raise. Not valid in a `[ContractFor]` class. |
| `Spec.Ensures<T>(Func<T, bool>)` | M6 | start of a block body, after any `Spec.Requires` and `Spec.NoThrow` | Postcondition on normal return; the argument is the return value. `T` is the return type, or the awaited type of `Task<T>`/`ValueTask<T>`. A path that ends in an explicit `throw` or a dependency's exception need not satisfy it, and the report lists that path. |
| `Spec.Ensures(Func<bool>)` | M6 | start of a `void`, `Task` or `ValueTask` method's block body | Postcondition with no return value. |
| `Spec.Assert(bool, params Tactic[])` | M6 | statement | A fact to prove at this point, by its script if it has one, then usable afterwards. |
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
| `Prove.That(bool)` | M4 | The claim. A theorem's body is a single `Prove.That` call, and a call anywhere else is WRT0004. Without `.By`, a claim with no parameters or quantifiers is proved by `rfl` or `decide` (M4); a claim with them fails with "unsolved goals", its goal and any counterexample. M6's default procedure runs on contract obligations only; no milestone schedules a default pipeline for `Prove.That`. A theorem cannot call a method that can throw (`theorem calling a raising method`); state the property as that method's `Spec.Ensures`, or a relation between two calls as the `Spec.Ensures` of a verified method that makes both. |
| `.By(params Tactic[])` | M5a | Run these tactics in order on the goal. The engine first introduces the theorem's parameters under their C# names. Write the tactics as arguments, not as an array. |
| `Prove.Contract().By(params Tactic[])` | M6 | The body of a `[ProofFor(nameof(M))]` method: a script for `M`'s contract obligation, a `Std.Do` triple, after its binders are introduced. |

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
| `Tactic.VcGen()` | M6 | Run the VC walker on a contract obligation and leave its conditions, after the VC simp set, as goals. Only in a `[ProofFor]` or `Spec.Assert` script; in a theorem's script it is WRT0004. |
| `Tactic.Decide()` | *proposed, Q20* | Decide a claim over finite domains by evaluation. |
| `Tactic.Split()` | *proposed, Q20* | Case-split an `if` or `?:` in the goal. |
| `Tactic.Grind()` | M8 | Congruence closure and E-matching. |

The default procedure for contracts (M6) runs on every contract obligation without a `[ProofFor]` script: the VC
walker follows the method's program, a VC simp set (the default set plus `Std.Do`'s assertion lemmas) simplifies each
condition it leaves, and `Omega` closes it. Each condition that does not close is WRT0001 at the operation or `Spec`
call that produced it ([docs/m6/07](../m6/07-vc-generation.md)).

## `Lean`: library references

| Member | Since | Meaning |
|---|---|---|
| `Lean.Const("Int32.lt_iff_toInt_lt")` | M5a | A declaration in the semantics bundle: the semantics library and the part of Init that `lean/bundle-roots.txt` reaches. Other Init lemmas, such as `Nat.add_comm`, are not in it and fail with "unknown constant". M5b's store holds Init and Mathlib for the CLI's `import` and `check-store`, but proofs still see only the bundle. M6 added the `Std.Do` constants its contracts use to the bundle, not the store; using the store as the verification environment is not scheduled. Takes a string literal; it cannot name a variable or a member to unfold. |

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
| `/`, `%`, `checked` on `int` and `long` | M6 | Division by zero, `MinValue / -1` and checked overflow are exceptions, which a method's contract obligation must rule out. |
| `+`, `-`, `*`, unary `-` on `int` and `long` in a theorem statement, `Spec.Requires`, `Spec.Ensures` or `Spec.Assert` | M6 follow-ups | Must not overflow (GitHub #183, #235, #236): each is a well-definedness condition, under the guards around it, that fails the proof at the operation. `unchecked(...)` wraps on purpose with none. |
| `+`, `-`, `*`, unary `-`, `++`, `--` and compound assignment on `int` and `long` in a `[Verified]` method's body | M6 follow-ups | Must not overflow (GitHub #244): each is a condition under the method's `Spec.Requires`, the branches and `switch` sections taken, the guards around it and, in a method that can throw or calls one with a `Spec.Requires`, all the VC walk knows (a callee's `Spec.Ensures` among it); a possible overflow fails the method at the operation with `arithmetic overflow`, and its callers are skipped. The value is still C#'s wrapped one. `unchecked(...)` and `unchecked { }` wrap on purpose with none; `checked` throws as before. |
| `throw new T(...)`, nullable values (`int?`, `Payment?`, …) | M6 | See the `throw` and `null` rows below. |
| `Spec.Requires`, `Spec.Ensures`, `Spec.Assert`, `[ProofFor]` | M6 | See [the M6 contract rejections](#the-m6-contract-rejections). |
| Calls through an interface with a `[ContractFor]` class; `async`/`await` of verified or contracted calls | M6 | See [the M6 dependency rejections](#the-m6-dependency-rejections). |
| `decimal`: literals, comparisons, `==`, `+`, `-`, unary `-`; `Math.Min`, `Max`, `Abs` | M6 | `1.0m == 1.00m`, also inside records. |
| `try`/`catch`/`finally` | *unscheduled* | Error WRT0002 (`try`). |
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
| `division`, `remainder` | WRT0002 | M6 extracts `/` and `%` on `int` and `long` in a `[Verified]` method. By a constant other than 0 and -1 they cannot throw, so they stay pure, are accepted in a theorem statement too, and can be proved about (M6 U9); by anything else they can throw, so the method becomes a `ClrM` program that M6's contract obligations prove about, and a theorem statement rejects them. A constant expression such as `unchecked(int.MinValue / -1)` is folded first and accepted. |
| `checked arithmetic` | WRT0002 | `checked(...)`, or any arithmetic or narrowing cast in a project with `CheckForOverflowUnderflow` on. A checked widening cast cannot overflow and is accepted. M6 extracts the rest in a `[Verified]` method; still rejected in a theorem statement, where a checked narrowing cast is named `checked narrowing`. |
| `integer bitwise operator`, `shift` | WRT0002 | `&`, `\|`, `^`, `~`, `<<`, `>>`, `>>>` on integers. Not scheduled. |
| `throw`, `try` | WRT0002 | M6 extracts `throw new T(...)` in a `[Verified]` method when each argument is a constant or a parameter and `T` is a `System` exception or a plain subclass of one: a constructor with an empty body that only calls its base, a `System` exception, with constants and its parameters. Otherwise `rethrow`, `throw of a value other than a new exception`, `exception argument that is not a constant or a parameter` or `exception type that is not a System exception or a plain subclass of one`. `throw` in a theorem statement and `try` stay rejected. |
| `non-exhaustive switch over an open enum` | WRT0002 | A switch expression over an open enum without `_`: .NET throws for unnamed values. M6 did not build it, and it is not scheduled. |
| `null`, `nullable type` | WRT0002 | M6 accepts `int?`, `long?`, `bool?`, `decimal?` and nullable references to records and closed classes (`Payment?`) with `null`, `is null`, `is not null`, `== null`, `!= null`, `HasValue`, `Value`, `(int)x`, `??` and `GetValueOrDefault()`, and proves what a method does with them. A record with a nullable field does not translate yet (GitHub #218). A value declared `T?` used where a `T` is required (an argument, a returned value, a member access) is a check that it is not null, whatever the compiler's flow analysis says. `null` is still rejected for a value not declared nullable, which is assumed non-null, and `nullable type` for other nullable types. Also `lifted comparison` and `lifted arithmetic` (`x > 0`, `x == 5`, `a + b` on nullable values), `null-forgiving operator` (`!`), `switch on a nullable value`, and `nullable read` or `non-null unwrap` in a theorem statement. |
| `loop` | WRT0002 | `for`, `foreach`, `while`, `do`. M7. |
| `string` | WRT0002 | M7. |
| `decimal operator other than + and -`, `decimal arithmetic` | WRT0002 | M6 extracts `decimal` literals (exactly, scale included), comparisons, `==` (numeric, so `1.0m == 1.00m`), `+`, `-`, unary `-` and record fields; `*`, `/` and `%` wait for M7. `+` and `-` can throw, so they are rejected in a theorem statement as `decimal arithmetic`. |
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
| `unsealed record`, `record struct`, `record with its own equality`, `record with other instance state`, `record with a base record`, `record that is not positional`, `record field of a closed class with its own equality` | WRT0002 | `==` on a record must be field-by-field over its positional properties, each compared as the model compares it. |
| `record with its own copy constructor` | WRT0002 | `with` runs the copy constructor, and the model copies the fields, as only the compiler's copy constructor does. |
| `preprocessor conditional` | WRT0002 | A member that translates differently depending on which `#if` symbols the build defines, for example one with an `#if DEBUG` in its body, or one that calls an overload declared under `#if`. Extraction compares every combination of the symbols the conditions test (at most six), skipping combinations that do not compile. Code an `#if` does not affect is translated as usual. M5a takes the real defines from `Csc`. |
| `cyclic record types` | WRT0002 | Without `null`, no value of such a type can be built. |
| `reserved member name` | WRT0002 | A member of a record or closed type named `rec`, `recOn`, `casesOn`, `noConfusion`, `noConfusionType`, `below`, `brecOn`, `ctorIdx` or `injEq`. |
| `instance member of a class` | WRT0002 | Only records may have verified instance members, and, from M6, a class's instance methods, which may call dependencies (see the M6 dependency rejections). A property of a class, an instance member of a struct or of a `[Closed]` class is still rejected. |
| `generic type`, `generic member` | WRT0002 | §12 Q14. |
| `depends on a rejected unit` | WRT0002 | A member that uses a rejected type or calls a rejected member. |
| `case guard`, `switch arm guard`, `lambda`, `user-defined operator`, `user-defined conversion`, `indexer`, `property setter`, `ref parameter`, `ref return`, `ref local`, `ref conditional`, `params argument`, `object initializer`, `object creation`, `constructor other than the primary constructor`, `with on a type that is not a record`, `with on a property that is not positional`, `assignment to a parameter`, `assignment to a field or property`, `local without an initializer`, `expression statement`, `jump statement`, `increment of a non-integer`, `enum arithmetic`, `closed enum constant that names no member`, `pattern that is not a constant`, `type defined outside the compilation`, `enum with an underlying type other than int or long`, `positional property that is not the compiler's auto-property`, `member without a body`, `theorem that is not static`, `theorem that is not Prove.That` | WRT0002 | Less common constructs, each named in its message. Anything else gets a name that starts with `unsupported` (`unsupported expression`, `unsupported operator`, …). |
| A call to a `[Theorem]` | WRT0003 | |
| `Spec.Implies outside a theorem statement`, `Prove.That outside a theorem statement` | WRT0004 | |
| A call to a member that is neither `[Verified]` nor modelled | WRT0005 | For example `System.Math.Round(double)`. From M6, `Math.Min`, `Math.Max` and `Math.Abs` on `int`, `long` and `decimal` are modelled; `Math.Abs`, which can throw, is rejected in a theorem statement as `modelled member M:System.Math.Abs(System.Int32)` (or `Int64`, WRT0002). |
| `integer cast to a closed enum`, `unboxing to a closed enum`, `arithmetic on a closed enum`, `closed enum without a member valued 0` | WRT0008 (warning) | Anywhere in the compilation, verified or not. |
| A `[Closed]` class without the closed shape | WRT0009 | Names the failed step: `not sealed`, `constructor that is not private`, `static instance that is not an initialised get-only auto-property or readonly field`, `static constructor`, `constructor or initialiser that could throw`, `constructor called outside the static instances`, `instance created or changed without a constructor call`, or `no static instances`. |

### The M5a additions

M5a accepts, on top of the M4 subset: theorems with parameters; `Spec.ForAll`
and `Spec.Exists` in theorem statements; `.By(...)` scripts; and a method that
calls itself when its block body starts with `Spec.Decreases`. It adds these
rejections:

| Construct | Code | Notes |
|---|---|---|
| `recursion without Spec.Decreases` | WRT0002 | Including any expression-bodied recursive method, which has no statement to hold the measure. |
| `Spec.Decreases not first` | WRT0002 | The measure is read on entry. From M6 it also comes before any `Spec.Requires` and `Spec.Ensures`. |
| `mutual recursion` | WRT0002 | Even with a measure on each method. |
| `nested recursion` | WRT0002 | A recursive call inside another recursive call's argument, such as `F(F(n - 1))`. |
| `lambda with statements` | WRT0002 | The claim of `Spec.ForAll` or `Spec.Exists` must be an expression. |
| `Spec.ForAll outside a theorem statement`, `Spec.Exists outside a theorem statement` | WRT0004 | |
| `quantifier whose claim is not a lambda` | WRT0004 | Including a lambda with more than one parameter. |
| `proof script outside a theorem` | WRT0004 | A `Tactic` or `Lean` call, or `.By`, anywhere but a theorem's script, a `[ProofFor]` method's script or a `Spec.Assert` script (M6). |
| `nameof of an overloaded method`, `nameof that names no verified member or theorem` | WRT0004 | |
| `string literal where a lemma is expected`, `string literal where a member name is expected` | WRT0004 | In `Tactic.Simp` and `Tactic.Unfold`. |
| `unsupported script argument` | WRT0004 | A step that is not a `Tactic.X(...)` call, an option value that is not a constant, an argument array, or `Lean.Const` of a non-literal. |
| `theorem used in its own proof` | WRT0004 | |

### The M6 contract rejections

M6 extraction reads `Spec.Requires`, `Spec.Ensures` and `Spec.Assert` in a
`[Verified]` method or property, and the script of a `[ProofFor(nameof(M))]`
method, which becomes `M`'s script. `Tactic.VcGen()` is a step of a
`[ProofFor]` or `Spec.Assert` script only; in a theorem's script it is still
`unsupported script argument`. The contract obligation and how it is proved are in
[docs/m6/06](../m6/06-contract-obligations.md) and [07](../m6/07-vc-generation.md).
These are rejected:

| Construct | Code | Notes |
|---|---|---|
| `Spec.Requires not leading the body`, `Spec.NoThrow not leading the body`, `Spec.Ensures not leading the body` | WRT0002 | They must lead the block body: after any `Spec.Decreases`, and before any other statement. |
| `Spec.Requires after Spec.Ensures`, `Spec.Requires after Spec.NoThrow`, `Spec.NoThrow after Spec.Ensures` | WRT0002 | The order is `Spec.Decreases`, then `Spec.Requires`, then `Spec.NoThrow`, then `Spec.Ensures`. |
| `second Spec.NoThrow` | WRT0002 | At most one. |
| `Spec.NoThrow in a contract member` | WRT0002 | Reported for the `[ContractFor]` class: `Spec.NoThrow` is for a verified method's own body. |
| `Spec.Requires in an expression-bodied member`, `Spec.NoThrow in an expression-bodied member`, `Spec.Ensures in an expression-bodied member`, `Spec.Assert in an expression-bodied member`, `Spec.Assert outside a statement` | WRT0002 | A contract needs a block body (design Q17). |
| `Spec.Ensures type argument that is not the return type` | WRT0002 | `T` in `Spec.Ensures<T>` is the return type, nullable annotation included, or the awaited type of `Task<T>` or `ValueTask<T>`. The message names it. |
| `Spec.Ensures without the result`, `Spec.Ensures with a result on a method that returns none` | WRT0002 | `Spec.Ensures(() => ...)` is for `void`, `Task` and `ValueTask` methods only. |
| `Spec.Ensures whose condition is not a lambda` | WRT0004 | |
| `contract on a recursive method` | WRT0002 | Its recursive call cannot use its own contract before it is proved. |
| `recursion with effects` | WRT0002 | A recursive method that can raise: one that throws, divides by a variable, reads a nullable value, calls a method with `Spec.Requires`, and so on, itself or through a callee. The message names the construct and the callee. |
| `Spec expression calling a raising method` | WRT0002 | A `Spec.Requires` or `Spec.Ensures` is a claim, so it cannot call a method that can raise. A call to a method that cannot raise is accepted, even when that method has a `Spec.Requires`. |
| `theorem calling a raising method` | WRT0002 | A theorem statement that calls a method that can raise, directly or through its callees; the message names the construct and where it is. State the property as a `Spec.Ensures` instead, or, for a property relating two calls, as the `Spec.Ensures` of a verified method that makes both calls ([how-to](how-to.md#relate-two-calls-of-a-method-that-can-throw)). A raising operation in the statement itself is named as the operation (`division`, `nullable read`, `checked arithmetic`, …). Division or remainder by a constant other than 0 and -1 cannot raise, and is accepted. |
| `[ProofFor] naming no method`, `[ProofFor] of an overloaded method`, `[ProofFor] of a member that is not verified` | WRT0002 | `[ProofFor(nameof(M))]` names one `[Verified]` member of its own class, without overloads. |
| `[ProofFor] method that is not static and parameterless`, `[ProofFor] body that is not Prove.Contract().By(...)` | WRT0002 | |
| `second [ProofFor] for a method` | WRT0002 | The message names the first, whose script is kept. |

### The M6 dependency rejections

M6 extraction also reads `[ContractFor(typeof(I))]` classes, the dependencies
of a class's `[Verified]` instance methods, and `async` methods. A dependency
is an instance `readonly` field declared in the method's own class, or a
primary-constructor parameter of that class that nothing assigns, of an
interface type whose `[ContractFor]` class is in the same project; the
interface may come from any assembly. Each member called through a dependency
gets a contract unit from its contract class. A call returning `Task`,
`Task<T>`, `ValueTask` or `ValueTask<T>` must be the direct operand of `await`.
Such a method is translated with one operation per member it calls and that
member's contract as a hypothesis of its obligation. The default procedure uses
that hypothesis at each call (M6 U20): the member's `Spec.Requires` is a VC at
the call, its `Spec.Ensures` holds after it, and an exception from it is
allowed and reported. Two calls are unrelated unless the contract relates
them. These are rejected:

| Construct | Code | Notes |
|---|---|---|
| `member access on this`, `dependency used other than to call a member`, `property of a dependency` | WRT0002 | Any other use of the class's state: a field or property that is not a dependency, a call to another instance method, `this`, or a dependency used as a value. |
| `mutable dependency field`, `assigned primary-constructor parameter`, `static dependency`, `inherited dependency`, `generic interface dependency` | WRT0002 | A dependency that breaks the rules above. A primary-constructor parameter is assigned if anything in the class, lambdas included, assigns it or passes it by `ref` or `out`. |
| `dependency without a contract class`, `dependency whose contract class is rejected` | WRT0002 | The interface has no `[ContractFor]` class in this project, or its class has not the contract shape. |
| `dependency call in a Spec expression` | WRT0002 | A `Spec` condition is a claim, so it cannot call a dependency. |
| `interface member with two contract classes`, `interface member without a contract member` | WRT0002 | Reported for the member's contract unit when a verified method calls it: an inherited member, such as `Dispose`, that two contract classes state, or an interface member with a default body that its contract class does not state. |
| `Task-returning call that is not awaited`, `ConfigureAwait`, `Task combinator`, `await of something other than a call`, `async void method` | WRT0002 | A task that is discarded, stored or returned, `Task.Delay`, `Task.WhenAll` and other members of `Task` and `ValueTask`. |
| `return without a value` | WRT0002 | A `void`, `Task` or `ValueTask` method ends by reaching the end of its body. A `CancellationToken` parameter is rejected too, as `unsupported type`: VIR has no form for either yet (GitHub #215). |
| `named arguments out of order with a dependency call` | WRT0002 | Arguments that await or call a dependency must be written in parameter order. |
| `call to an instance method of a class` | WRT0002 | A class's verified instance method has no receiver in the model, only its dependencies, so nothing else can call it. |
| `[ContractFor] of a type that is not an interface`, `contract class that is not file or internal`, `contract class that is not abstract`, `generic contract class`, `contract class that does not implement exactly its interface`, `contract class member that is not a member of its interface`, `contract member whose nullability differs from its interface`, `contract member body other than Spec calls and return default!`, `second contract class for an interface` | WRT0002 | The contract shape, reported for the class whether or not it is used. A member's body is `Spec.Requires` and `Spec.Ensures` calls then `return default!;`, those calls alone for a `void` member, `=> default!`, or none (`abstract`). The second class for an interface names the first. A member whose signature has an unmodelled type is accepted until a verified call uses it. |

## Type mapping

Summary of [design §6.1](../design.md#61-type-mapping).

| C# | Model |
|---|---|
| `bool` | `Bool` (a proposition inside specs) |
| `int`, `long`, `short`, `sbyte` | `Int32`, `Int64`, `Int16`, `Int8`: two's complement, wrapping |
| `uint`, `ulong`, `ushort`, `byte` | `UInt32` … `UInt8` |
| `checked(...)` | throws `OverflowException` |
| `unchecked(...)`, `unchecked { }` | wraps on purpose: no overflow obligation in a statement, spec or method body (GitHub #236, #244) |
| `BigInteger` | `Int` (not built; specs have no unbounded integer yet, GitHub #160) |
| `decimal` | 96-bit mantissa and scale; `==` and order by value (M6) |
| `T?` | `Option T` (M6); non-nullable annotations are assumptions |
| `record` | single-constructor `inductive`; `==` is a generated field-by-field `$eq` |
| `enum` | integer with named constants; closed if `[Closed]` |
| `[Closed]` enum or class | `inductive` with one constructor per member or static instance; `==` compares a generated `$index` |
| exceptions | the error branch of the effect monad `ClrM` (M6) |
| `Task<T>`, `ValueTask<T>`; `Task`, `ValueTask` | a `ClrM` program returning `T`; returning `Unit` (M6) |
| an interface with a `[ContractFor]` class | one operation per member called, with its contract as a hypothesis (M6) |

## Diagnostics

Numbers are provisional.

| Code | Severity | Raised by | Meaning |
|---|---|---|---|
| WRT0001 | error | build task | A theorem, postcondition, precondition at a call site, invariant or assertion could not be proved. Shows the goal and any counterexample. In M4: the theorem is false; the message quotes the claim and, for a single `==`, `<`, `<=`, `>` or `>=`, the value of each side (`unknown` for records and closed types). From M5a also: a theorem or a recursive call's decrease obligation was not proved ("could not be proved", "could not be shown to decrease"); the message's first line names the theorem, the tactic's first line and any counterexample, and the later lines give the tactic's details and the goals. From M6 also: "The contract of 'M' could not be proved", one error per failing condition, at the operation or `Spec` call that produced it, starting with its kind (`division by zero`, `overflow in a checked operation`, `null read`, `null passed where a non-null value is required`, `precondition of a callee at this call`, `precondition of a dependency member at this call`, `postcondition of the method`, `Spec.Assert`, `well-definedness of a Spec expression`, `arithmetic overflow` (default-context arithmetic in the method's body, #244), `a program shape the VC walker has no rule for`, and under `Spec.NoThrow` `an explicit throw is reachable under the Requires (Spec.NoThrow)` and `a callee without Spec.NoThrow may throw explicitly at this call (Spec.NoThrow)`), then its path conditions and goal; no counterexample. An unsatisfiable `Spec.Requires` or contract member is WRT0001 at its `Spec` line. A `[ProofFor]` script that fails is reported where it fails. |
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

Extraction raises WRT0002 to WRT0005, WRT0008 and WRT0009, and `warrant
translate` and `warrant verify` report them with the engine's WRT0001, WRT0006
and WRT0010. The build task reports what `warrant verify` reports, plus WRT0010
when the CLI fails; WRT0011 comes from the `Warrant` package's own targets.

From M5b the `Warrant` package's analyzer reports extraction's diagnostics in
the IDE as you type, at the same places and with the same messages, because it
runs extraction's own rules. It sees the active configuration only, so the
`preprocessor conditional` check stays the build's, and it never reports proof
results (WRT0001, WRT0006). It runs only in design-time builds: in a build, the
CLI reports each diagnostic once and verifies everything else. WRT0008 is a
property of the whole compilation, so Visual Studio shows it only with full
solution analysis on. A diagnostic about a record or enum that a member uses is
reported at the type, and the member gets "depends on a rejected unit".

## MSBuild properties

| Property | Since | Default | Meaning |
|---|---|---|---|
| `WarrantEnabled` | M5a | `true` | Run `warrant verify` after `CoreCompile`. Any other value turns verification off, and the `Warrant` package then warns WRT0011. |
| `WarrantKernelFuel` | M5a | 20,000,000 | Kernel steps per theorem. |
| `WarrantTacticFuel` | M5a | 171,970 | Tactic steps per theorem. |
| `WarrantTimeoutSeconds` | M5a | 30 | Wall-clock seconds per theorem, for tactics and kernel together. |
| `WarrantUseServer` | M5b | `true`; `false` when `ContinuousIntegrationBuild` is `true` | Verify through the per-user verification server, starting it when none runs (`--server auto`). A server that cannot be started, reached or trusted makes the build verify in-process and log why, as a message, not a warning. `false` always verifies in-process (`--server off`). |
| `WarrantRecheck` | M5b | `false` | Have the kernel re-check every cached proof against the theorem as it is built from the current code, without running tactics (`--recheck`). A cached proof the kernel rejects is WRT0010 and its entry is deleted. Without it a cache hit is trusted. Recommended in CI. |
| `WarrantCacheDir` | M5b | `$(BaseIntermediateOutputPath)warrant/cache/` | The project's result cache (`--cache-dir`). `dotnet clean` and Rebuild delete the entries in it, and nothing else. |
| `WarrantUseCache` | M5b | `true` | `false` verifies without the result cache: nothing is read or written. |
| `CheckForOverflowUnderflow` | M4 | `false` | The standard C# setting. Warrant models arithmetic the same way. |

A theorem's own `[Theorem(...)]` arguments override the three budgets, and from M5b
they apply to every unit: a definition, its equation lemma or a decrease proof
that runs out is WRT0006 too. Design-time builds never verify. A
multi-targeted project verifies in the build of every entry of
`TargetFrameworks`, so a build of a single framework (`dotnet build -f`)
verifies that framework, and a diagnostic is reported once for each
framework's build it occurs in.

## CLI

| Command | Since | Purpose |
|---|---|---|
| `warrant check <file.ndjson[.gz]> [--fuel <n>] [--admit-rejected] [--quiet] [--slowest <n>]` | M2 | Check a lean4export file with Warrant's kernel. `--quiet` prints only the summary; `--slowest <n>` also lists the n declarations that took longest, with the time and the memory allocated for each (M5b, used for [the Mathlib run](../mathlib.md)). |
| `warrant export <in> <out>` | M3 | Check a lean4export file, then write what the kernel admitted, for another kernel to re-check. |
| `warrant translate <directory> [--out <file.ndjson>] [--report <file.md>] [--check-overflow] [--bundle <path>]` | M4 | Compile every `.cs` file under the directory, translate its `[Verified]` members and theorems, and print one line per unit plus diagnostics. `--out` writes the semantics bundle and every admitted declaration as lean4export NDJSON; `--report` writes the assumption report as Markdown. Exit 0 when everything translated and every theorem was proved, 1 otherwise, 2 for bad arguments or unreadable input, including a missing bundle or a missing or mismatched sidecar. Like `verify`, it loads the attribute sidecar beside the bundle, so it proves contracts as `verify` does (GitHub #220). |
| `warrant verify --csc-args <file> [--project-dir <dir>] [options]`, `warrant verify <directory> [options]` | M5a | Verify from the argument file the build writes (as the build task does), or from every `.cs` file under a directory, as `translate` compiles it. Prints one line per unit, the diagnostics and `Warrant: n verified units, n theorems proved, n not proved.` (the last two count theorems: a method whose contract obligation is proved is `translated`; when a method, type or contract unit is not verified, its obligation failing say, the line adds `; n other units not verified`, GitHub #225); from M5b the summary adds `(k from cache)` and `(k from cache, k rechecked)`, counting theorems and recursive methods, and, with `--server auto`, `[server]` or `[in-process]`. M5b options: `--server auto\|off` (through the verification server, falling back to in-process when it cannot be used, or in-process; in-process when not given); `--cache-dir <dir>` (read and write the result cache there; not with `--out`); `--recheck` (the kernel re-checks every cached proof); `--timings` (after the summary, how long reaching the server took, the request's time and each unit's time and source: `server`, `in-process`, `cache` or `rechecked`). The first Ctrl+C cancels the run, on the server too; a second ends the process. M5a options: `--format text\|msbuild` (`msbuild` writes one tab-separated `WRT1` record per diagnostic, for the build task); `--out <file.ndjson>` (the bundle and every admitted declaration, as `translate --out`); `--report <dir>` (`report.md` and `report.json`); `--kernel-fuel <n>`, `--tactic-fuel <n>`, `--timeout <seconds>`; `--bundle <path>` (the attribute sidecar must sit next to the bundle and name its hash); `--keep-conditional-check` (keep M4's `#if` combination check with `--csc-args`). The directory mode uses the corpus kernel fuel, 100M. Exit 0 when every theorem was proved (warnings allowed), 1 when an error was reported, 2 for bad arguments or unreadable input, including a missing bundle or a missing or mismatched sidecar. A `<project>` form that evaluates the project file is follow-up work. |
| `warrant explain <unit> [--project-dir <dir>] [--csc-args <file>] [--sources <dir>] [--server auto\|off]` | M5b | Verify one unit and the units it needs, and print each tactic of its proof script as its source reads, where it is, and the goals before and after it, or why it failed; then the unit's outcome as `verify` reports it. `<unit>` is the name a diagnostic gives (`Increments.AlwaysLarger(int)`), any dotted end of the display name, with or without its parameters, or the documentation-comment ID; an unknown or ambiguous name lists the units. It explains the project's last verifying build as that build verified it, from the newest `obj/**/warrant.explain` the build writes (the argument file of the target framework that verified, the referenced projects' source records, and `--keep-conditional-check`), unless `--csc-args` or a `--sources` directory is given; a project with no such file and exactly one `obj/**/warrant.csc.args` uses that file. It also takes `--reference-source` and `--keep-conditional-check`, and `--bundle`, `--kernel-fuel`, `--tactic-fuel` and `--timeout` as `verify` does, and never uses the result cache. Exit 0 when the unit verified, 1 when it did not, 2 for bad arguments or an unknown unit. |
| `warrant server status \| cancel <id> \| shutdown \| report <project dir>` | M5b | Manage the verification server a build of this toolchain uses; none of them starts one. `status` prints the process id, endpoint, toolchain identity, uptime, bundle hash, GC heap, working set, cache counters (hits, misses, tactic runs, rechecked) and the running requests with their ids. `cancel <id>` stops a running request. `shutdown` stops the server once its running requests finish. `report` prints the JSON assumption report of the project's last verify through the server, the `report.json` that `--report` writes. With no server running each says so; exit 0 for `status` and `shutdown` then, 1 for `cancel` and `report`, and 1 when `cancel` finds no such request. |
| `warrant import <file.ndjson[.gz]>... --store <dir> [--verified] [--fuel <n>]` | M5b | Write a new version of a store from the files, in order ([store v1](../m5b/05-store.md)). |
| `warrant check-store <dir> [--fuel <n>] [--quiet]` | M5b | Re-check every declaration of the store with the kernel, with `warrant check`'s summary and exit codes. |
| `warrant sample-store <dir> [--count <n>] [--seed <n>]` | M5b | Open the store's current version, look up n distinct constants chosen at random by name (1,000 and seed 1 by default), and print the time taken, the GC heap and the working set: a measurement of the store, used by `scripts/measure-m5b.sh`. |

From M5b, `verify --out` and `--report` work through the server too: `--out` writes the certificates the server's
`export` returns, byte for byte what an in-process run writes, and `--report` renders the same reports on either path.

## Assumption report

`warrant translate --report <file.md>` (M4) writes the Markdown form, and
`warrant verify --report <dir>` (M5a) writes `report.md` and `report.json`.
The build does not write a report. From M5b, a verify through the server keeps
the project's last JSON report there, and `warrant server report <project dir>`
prints it. Each unit's line names its status
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
    - Arithmetic wraps on overflow, except in a checked region, where it throws (overflow checking is off)
    - The semantics bundle models C# 14 int, long, bool and decimal, their nullable forms, records, enums, closed classes, throw and the exceptions arithmetic, division and null access raise, and Math.Min, Math.Max and Math.Abs on int, long and decimal; decimal arithmetic throws on overflow in every region
    - The only axioms are Lean's standard ones: propext, Classical.choice, Quot.sound
```

From M6, a method with contracts also lists `Assumed (contracts)`: its own `Spec.Requires`, which is assumed on
entry and not checked at run time or at call sites Warrant does not verify; each verified callee's proved contract; and
each dependency member's contract, quoted from its contract class. `Assumed (exceptions)` lists each explicit `throw`
the walker could not show unreachable, each one that propagates through a verified callee, and each dependency call,
with its source line, because the proof says nothing about a call that ends in one. `Assumed (parameters)` gains that
each dependency, and each non-nullable reference a dependency returns, is not null. In `report.json` these are the
`caller-precondition`, `callee-contract`, `external-contract` and `may-throw` kinds. A method whose contract obligation
is proved keeps the status `TRANSLATED`; `VERIFIED` is for theorems. For example (`tests/corpus/m6/ProcessPayment.report.txt`,
abridged):

```text
Corpus.M6.Payments.PaymentService.ProcessPayment(int)                     TRANSLATED   (kernel: …, bundle: …)
  Assumed (parameters):
    - store is not null
    - store.GetPayment() is not null
    - store.SavePayment() is not null
  Assumed (contracts):
    - Every implementation of Corpus.M6.Payments.IPaymentStore.GetPayment(int) keeps its contract: Spec.Ensures<Payment?>(r => r is null || r.Id == id)
    - Every implementation of Corpus.M6.Payments.IPaymentStore.SavePayment(Corpus.M6.Payments.Payment) keeps its contract, which states nothing: a call may return any value or throw
  Assumed (exceptions):
    - Corpus.M6.Payments.PaymentService.ProcessPayment(int) may throw an exception from Corpus.M6.Payments.IPaymentStore.GetPayment(int) (the call at accepted/Payments.cs:48); its proof says nothing about a call that ends in it
    - …
  Assumed (global):
    - …
```

The layout the design once sketched, with a `Proved:` section, a certificate hash and a `TIMEOUT` status, was not
built.
