# 3. Extraction

> Part of the [M4 design](README.md). Decisions: KTD3, KTD4, KTD6, KTD10, KTD11, KTD13, KTD15, KTD18, KTD21, KTD22 in the [plan](../plans/2026-11-02-1245-feat-m4-pure-subset-plan.md).

Extraction turns C# that Roslyn has already bound into VIR (chapter 4), and rejects everything outside the M4 subset with a diagnostic that names the construct.
It is `src/Warrant.Extraction`, a netstandard2.0 library so that the M5b analyzer can share it (design §3.2).
It is part of the trusted base (KTD22): a mistake here is a faithfulness gap, which is why the differential tests in chapter 7 run end to end, from C# source to kernel.

## Building the compilation

Extraction works on a `CSharpCompilation`; it never parses files on its own.
The compilation comes from a factory in `src/Warrant.Frontend` (net10.0), which the tests and the `warrant translate` verb use (KTD4).
For the corpus it sets:

- references from `Basic.Reference.Assemblies.Net100` (1.8.14), plus the `Warrant` package assembly, loaded from an image embedded in `Warrant.Frontend` (a copied `Warrant.dll` would collide with the CLI's own `warrant.dll`, because assembly names compare case-insensitively);
- `LanguageVersion.CSharp14`, pinned, so that a Roslyn upgrade cannot change the language under the corpus;
- `NullableContextOptions.Enable`, because with nullable analysis off an unannotated parameter's annotation is `None`, and a non-null assumption (below) could not be told from "nobody said";
- deterministic output, source paths relative and sorted, and the overflow-checking setting as an explicit parameter.

These options decide what the C# means, so they are trusted input, like extraction itself (KTD22).
M5a's build task will not use the corpus settings: it takes the references, defines, `LangVersion` and overflow setting from the inputs `Csc` received (design §8.3).
Until then no defines are known, so code under `#if` could be code that no real build runs, or could declare an overload or a type that changes what other code binds to.
Extraction therefore collects the symbols every `#if` and `#elif` condition tests, extracts the compilation once for each combination of them that compiles (a combination that does not compile is not a real build), and keeps a unit only if its VIR is byte-for-byte the same in all of them.
A unit that differs is WRT0002 `preprocessor conditional`, and its users are rejected as depending on it; a proof about a unit that is kept holds in every build.
Warnings (WRT0008) from every combination are reported. More than six symbols (64 combinations) is WRT0002 for the whole compilation.
MSBuildWorkspace is not used: it would add an MSBuild dependency to the tests for no benefit while the inputs are a fixed corpus.

The factory and extraction are separate assemblies because they have different Roslyn constraints:

- `Warrant.Extraction` is netstandard2.0, and the M5b analyzer loads it into the compiler.
  A compiler refuses an analyzer built against a newer Roslyn than its own (warning CS8032), so extraction is compiled against **Roslyn 4.8.0**, the version in Visual Studio 2022 17.8 and the .NET 8 SDK.
  M5b kept that floor when it packaged the analyzer, which is tested under Roslyn 4.8 and 5.9 ([docs/m5b/06](../m5b/06-analyzers.md)).
- `Warrant.Frontend` runs only in Warrant's own net10.0 processes (tests, the CLI, later the M5a child process), so it can reference **Roslyn 5.0.0**, which knows C# 14.
  It also carries the reference assemblies, tens of megabytes that have no place in an analyzer.

If the compilation has errors, extraction stops and reports them.
It never translates code that does not compile.

## Finding the units

A unit is a member marked `[Verified]` or `[Theorem]`, or a type that such a member uses: a record, an open enum or a closed type (KTD21).
Types are units of their own so that each one is translated once, from one place, and so that a change to a record changes the closure hash of every unit that depends on it (chapter 4).

Extraction also scans the *whole* compilation, not only verified members, for integer casts and unboxing conversions to `[Closed]` enums, and for arithmetic whose result is one (`p + 1`, `p++`, `p | Phase.Open`): each one is warning WRT0008, because it can produce a value the closed model says cannot exist.

Calls between verified members, and uses of types, form a graph.
A cycle of calls is recursion, which M4 rejects (WRT0002, construct "recursion").
A cycle of record types, where a record has a field whose type leads back to it, is rejected too: without `null`, no value of such a type can be built.
Otherwise units are ordered so that every dependency comes before its users, which is the order the kernel needs to admit them; ties are broken by documentation-comment ID, compared ordinally, so the order is the same on every machine.

## Walking the operation tree

Extraction reads Roslyn's `IOperation` tree, not its control-flow graph (KTD4).
For M4's subset the tree is already structured: an `if` is an `IConditionalOperation` with two branches, not a set of basic blocks joined by jumps.
The control-flow graph would add flow-capture temporaries and synthesized blocks that extraction would have to fold back into structure, which is the step that prior verifiers (Charon, for Aeneas) describe as heuristic.
M4 does not need the graph at all: Roslyn already rejects a method in which some path does not return (error CS0161).

The walk is an allow-list.
Each node is accepted only if its kind, its operator kind, its operand types and its checked flag are on the list; anything else becomes WRT0002 with the construct named.

| Accepted in M4 | Notes |
|---|---|
| `int`, `long`, `bool` literals | Taken from `ConstantValue`, range-checked (chapter 1). |
| Any `int`, `long` or `bool` node with a constant value | Lowered to that constant, because that is what the IL contains (KTD13). A constant of enum type becomes the member it names instead; for a closed enum, a constant that names no member is rejected. Roslyn folds `unchecked(int.MinValue / -1)` to `int.MinValue` while the CLR would throw at run time for non-constant operands, so folding first keeps the model equal to the IL. |
| Parameters and locals | Locals may be reassigned (chapter 4). |
| `+`, `-`, `*` on `int`/`long`, unary `-` and `+` | Only when not checked. |
| `==`, `!=`, `<`, `<=`, `>`, `>=` on `int`/`long`/open enums | |
| `==`, `!=` on `bool`, records and closed types | Records and closed types: chapter 5. `<` and the other orderings on a closed type are rejected. |
| `&&`, `\|\|`, `!`, and `&`, `\|`, `^` on `bool` | Integer `&`, `\|`, `^`, `~` are rejected. |
| `?:` | |
| Conversions `int`→`long` (implicit), `long`→`int` (explicit, unchecked), open enum ↔ its underlying type | Every Roslyn conversion becomes an explicit VIR node. |
| Calls to `[Verified]` static members, and to `[Verified]` instance members of records | |
| Record construction (`new P(...)`, target-typed `new(...)`), property reads, `with` | Sealed records with compiler-generated equality and no other instance state. |
| Enum members, static instances of closed classes | Closed-enum members map to constructors by value. |
| `switch` expressions and statements | Over integers and open enums, patterns are constants, `_`/`default`, relational (`< 5`), and `and`/`or`/`not` of those. Over a `[Closed]` enum, patterns are constants, `or` and `_`; relational, `and` and `not` patterns over closed types are rejected (WRT0002), because a switch over a closed type is its recursor and each arm must name members. Case guards (`when`) are rejected. |
| `if`/`else`, `return`, local declarations, `=`, compound assignment and `++`/`--` as statements | On locals only. |
| `Spec.Implies`, `Prove.That` | Only inside a `[Theorem]` statement (chapter 6); anywhere else they are WRT0004. |

### The checked flag

Roslyn marks each arithmetic node with `IsChecked`, which already combines `checked(...)` with the project-wide `CheckForOverflowUnderflow` setting.
Extraction rejects a node when it is checked **and** it can overflow: binary arithmetic, unary minus, increments and narrowing conversions.
It does not reject a checked *widening* conversion (`int` to `long`), which Roslyn also flags when the project setting is on but which cannot overflow (KTD15).
So in a project with overflow checking on, every `+` is rejected until M6, as the design requires, and nothing else is.

### Switch expressions over open enums

A C# switch expression that covers every named member of an ordinary enum is still not exhaustive: any other value of the underlying type makes the CLR throw `SwitchExpressionException`.
M4 has no exceptions, so it accepts a switch expression only when it has a `_` arm, or when its scrutinee is a `[Closed]` type and every member is covered (KTD15).
A switch *statement* without `default` is different: it falls through to the next statement, and the translation models exactly that (chapter 5).

One shape of switch statement is rejected: a section that carries both `default` and `case` labels, such as `case 1: default: return 0;`.
Translation tests the `case` sections in order and puts the default branch last, as C# behaves, and a section shared between a `case` and `default` would have to be in two places at once.
Writing the `case` label as its own section, or dropping it, says the same thing.

## Records

A record is accepted when it is a `sealed` record class, positional, has the equality the compiler generates, and has no instance state besides its positional properties.
Extraction checks that:

- `Equals(T)`, `GetHashCode`, `EqualityContract` and the `==` operator are all implicitly declared;
- each positional property is the compiler's auto-property;
- the record declares no other instance field, and no other property with a backing field.
- the copy constructor is the compiler's, because `with` runs it and the model copies the fields;
- no positional property's type is a `[Closed]` class with its own equality (`record field of a closed class with its own equality`). The generated `Equals` compares such a field through `EqualityComparer<T>.Default.Equals`, which reaches the class's `Equals`, while the model compares instances.

A user-written `Equals` would make `==` mean something other than field-by-field equality, and an unsealed record can be compared with a subclass instance whose `EqualityContract` differs.
Extra instance state is subtler: the generated `Equals` compares *every* instance field, so a record with `public int Extra { get; init; }` beside its positional properties is equal to another only if `Extra` matches too, while a model built from the primary constructor would ignore it (KTD10).
A user-written copy constructor can set the copy's properties to anything, so `(r with { }).X` need not be `r.X`.
All four are rejected.
Computed properties such as `public bool IsLarge => Amount > 1000;` have no backing field, so they are fine, and they can be `[Verified]` instance members.

Field order is the primary constructor's parameter order, which is also the order of the generated `Equals`.

### Reserved member names

A member of a record or closed type named `rec`, `recOn`, `casesOn`, `noConfusion`, `noConfusionType`, `below`, `brecOn`, `ctorIdx` or `injEq` is rejected (KTD6).
These are the names Lean gives the auxiliary constructions of an inductive type, and they live in the type's namespace: the kernel already generates `T.rec`, and M5a's tactics will need the others.

## Closed types

A `[Closed]` enum is accepted if its underlying type is `int` or `long` and its members all have distinct values.
VIR records each member's value, and every constant of the enum's type is mapped to the one member with that value.
Two members with the same value (`Default = Pending`) would otherwise become two constructors that the kernel proves different, while the CLR says they are equal, so such an enum is rejected (WRT0002).
Extraction also warns (WRT0008) when the enum has no member valued 0, because `default`, an uninitialised field or a zeroed array then holds a value the model says cannot exist.
A `[Closed]` class is accepted if it has the closed shape (design D13), checked like this:

1. The class is `sealed`.
2. Every instance constructor is `private`, and the class has no primary constructor.
3. Every `static` member whose type is the class itself is either a get-only auto-property with an initialiser (`{ get; } = new(...)`) or a `static readonly` field with an initialiser, and the initialiser is a `new` of the class itself. A property with a getter body or an expression body (`=> new(...)`) fails this step, because it returns a new instance on every read. So does an initialiser that is not a `new`: with `public static Outcome B { get; } = A;`, `A` and `B` are one object, but the model would make them two constructors that the kernel proves different.
   A static constructor also fails this step: it runs after the initialisers and can assign `B = A` itself (or throw).
   So does any construction that could throw (`constructor or initialiser that could throw`). A throw while the instances are created would fail the type initialiser, and every use of the class would throw `TypeInitializationException`, while the model still has the instances.
   Until M6 models exceptions, only code that cannot throw is allowed, on the class and on each of its base classes:
   - the static instances' `new(...)` calls, with constant arguments and no object initialiser;
   - every other static initialiser of the class itself a constant, and every instance initialiser, on the class or a base class, a constant or a primary-constructor parameter (`public TValue Value { get; } = value;` stores into the backing field, like an assignment in a constructor body);
   - each instance constructor, a `this(...)` or `base(...)` call whose arguments are constants or parameters, then only assignments of constants or parameters to the class's own fields and auto-properties that no override can replace (not `virtual`, `abstract` or `override`, whose setter could be an override's);
   - a base class's primary constructor passing only constants or parameters to its own base;
   - no static constructor on a base class, and no base class from another assembly, whose constructors cannot be read.

   A base class's static initialisers are not checked (#47): without a static constructor the class is `beforefieldinit`, so the runtime runs them when one of its static fields is first read, not when an instance is created, and nothing allowed above reads one.
   So a smart-enum base class may keep `static readonly Lazy<...>` lookup tables.
   A generic base class is checked through its original definition.

   Implicit identity, numeric, reference and nullable conversions are allowed, because none of them throws; a user-defined conversion runs code (`static readonly System.Index Start = -1` throws), so it is not.
4. The private constructors are called nowhere else, so no other instance can be created without reflection.
5. There is at least one such member.

A class that fails any step is error WRT0009, naming the step (KTD18).
The instances, in declaration order, become the type's constructors (chapter 5).
For a class split across partial declarations, the order is by file path and then by position, so it is still deterministic.

Instance fields and properties of a closed class are ignored by the model, and reading one in verified code is WRT0002: M4 cannot model what `Outcome.Matched.Name` returns.

If the class or one of its base classes overrides `Equals` or defines `==`, the model still treats equality as "same instance".
That is true for the closed-set pattern only if the override agrees with identity on the static instances, so extraction records it as an assumption, and the differential tests check it (KTD11).
They check `==`, `Equals(object)` and `EqualityComparer<T>.Default.Equals` separately.
A record's generated `Equals` compares a closed-class field through the last of those, and the assumption would not reach the units that compare the record, so a record field of a closed class with its own equality is rejected instead (see "Records").

## Assumptions

Each unit collects the assumptions its translation relies on, for the assumption report (chapter 7):

- **Non-null values.** A record or closed-class parameter whose type is not annotated nullable is assumed non-null, and so is every record or closed-class field reachable from it.
  The CLR does not enforce either.
  A record parameter that the method reads throws `NullReferenceException` at the first member access; a closed-class value is only ever compared, so `null` simply behaves as one more value the model does not have.
  A parameter annotated nullable (`Payment?`) is rejected until M6 brings `Option`.
- **Closed values.** For each `[Closed]` type the unit uses: only its named members exist, and for a class with its own equality, that equality agrees with identity.
- **Global.** The semantics bundle, the overflow setting the unit was translated under, and that the only axioms are Lean's standard three (chapter 1).
  They are the same for every unit in a run, and the report lists them under "Assumed (global)" (chapter 7).

## Diagnostics

Diagnostic numbers are provisional, as in the [reference](../proving/reference.md).
M4 has no analyzer, so extraction raises the analyzer's checks itself; M5b's analyzer calls the same code.

| Code | Severity | Raised when |
|---|---|---|
| WRT0002 | error | A construct outside the M4 subset, named in the message. |
| WRT0003 | error | A call to a `[Theorem]` method. |
| WRT0004 | error | `Spec.Implies` or `Prove.That` used outside a theorem statement. |
| WRT0005 | error | A call from verified code to a member that is neither verified nor modelled. |
| WRT0008 | warning | Anywhere in the compilation: an integer cast or unboxing conversion to a `[Closed]` enum, arithmetic producing one, or a `[Closed]` enum with no member valued 0. |
| WRT0009 | error | A `[Closed]` class without the closed shape, naming the failed step. New in M4. |

WRT0001 (not proved) and WRT0006 (out of fuel) come from checking, not extraction (chapter 6).

## Determinism

The same compilation must always give byte-identical VIR, because VIR is hashed (chapter 4) and the hash keys M5b's result cache.
Extraction therefore identifies symbols by documentation-comment ID, sorts with ordinal string comparison, never iterates a hash-ordered collection to produce output, never uses `string.GetHashCode` (randomised per process), and formats numbers with the invariant culture.
