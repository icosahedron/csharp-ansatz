# 4. Extraction

> Part of the [M6 design](README.md). Decisions: KTD5, KTD8, KTD9, KTD10, KTD11, KTD16, KTD19, KTD22 and KTD23.
> Units: U5 (surface), U6 (VIR), U7, U17, U8, U18 (extraction).

Extraction is trusted: it decides what a C# method means before anything is proved about it.
M6 grows it by several constructs, so the plan split the work into four sequential units, each with its rejected-corpus
members, analyzer parity and the M4 members it flips: U7 (throw, checked arithmetic, `/`, `%`, `Math`), U17 (nullable
values and `decimal`), U8 (contracts) and U18 (dependencies, contract classes, `async`).
The build and the IDE analyzer run the same rules (docs/m5b/06), so everything below is reported as you type too.

## The surface

`src/Warrant/Spec.cs` and `src/Warrant/Contracts.cs` (U5) add:

| Member | Meaning |
|---|---|
| `Spec.Requires(bool)` | The method's precondition. |
| `Spec.NoThrow()` | No explicit `throw` of the method is reachable under its `Requires` (#182, chapter 6). |
| `Spec.Ensures<T>(Func<T, bool>)` | Its postcondition on normal return; the lambda's parameter is the result. |
| `Spec.Ensures(Func<bool>)` | The same for a method with no result: `void`, `Task`, `ValueTask`. |
| `Spec.Assert(bool, params Tactic[])` | A fact to prove at this point, with an optional script (KTD16). |
| `[ContractFor(typeof(I))]` | The class states what `I`'s members are assumed to do (R7). |
| `[ProofFor(nameof(M))]` | The method's script proves `M`'s contract obligation (KTD16). |
| `Prove.Contract()` | What a `[ProofFor]` method's body attaches its script to: `Prove.Contract().By(...)`. |
| `Tactic.VcGen()` | A script step that runs the VC walker (chapter 7). |

The five `Spec` methods are `[Conditional("WARRANT_CONTRACTS")]`, as `Spec.Decreases` is (KTD8): a normal build leaves
no call in the IL (a test checks this), so contracts cost nothing at run time, and nothing checks a `Spec.Requires` at
run time either (chapter 8).

## VIR version 3

VIR goes to version 3, additively (KTD19, U6): new types (`decimal`, `unit`, `nullable{T}`, `task{T}`), operators (`div`,
`rem`, a `checked` flag on arithmetic and narrowing, a decimal comparison kind), expressions (`DecimalLitExpr` with sign,
96-bit mantissa and scale, `NullExpr`, `IsNullExpr`, `UnwrapExpr` with a value or non-null kind, `CoalesceExpr`,
`ThrowExpr`, `AwaitExpr`, `ExternalCallExpr`, `ModelledCallExpr`), statements (`throw`, `eval`, `requires`, `nothrow`
(#182), `ensures`, `assert`), a function's optional dependencies, a contract unit kind and four assumption kinds.
Before version 3 was released, the follow-ups to M6 added one more form to it rather than a version 4: the overflow
value `unchecked` (#236), on `+`, `-`, `*`, unary `-` and `long` to `int` narrowing inside an explicit `unchecked(...)`
expression or `unchecked { }` block, the nearest such context deciding (an `unchecked` inside a `checked` wraps, and the
reverse raises).
`wrap` is now only C#'s default context, which must not overflow where Warrant proves something (#183, #236; method
bodies are #244); `unchecked` wraps on purpose, with no obligation; a unit's `facts` stay `wrap` or `checked`, and a
reader rejects `unchecked` there.
A unit that uses no version-3 form encodes as in version 2 apart from its `vir` field, which every unit's bytes contain,
so every unit and closure hash changed once and every M5b cache entry was invalidated, as U1's new bundle hash did
anyway.
`VirReader` rejects a unit newer than the version it knows, naming the version.
The M4 and M5a corpora are pinned to their version-2 encodings.

U6 also made every place that would have accepted a new form by default reject it explicitly until its unit landed, so
no unit could slip through half-supported.

## Which units can raise

`src/Warrant.Vir/Effects.cs` is one pure function over VIR (KTD11) that extraction, the analyzer and translation all
call, so they cannot disagree.
A function or theorem can raise when it contains:

- `throw`; checked `+`, `-`, `*`, unary `-` or narrowing; `decimal` `+` or `-` (checked in every context);
- `/` or `%` whose divisor is not a literal other than 0 and -1;
- a nullable read or non-null unwrap; a modelled member that throws (`Math.Abs` on `int` or `long`);
- an external call, `await`, `Spec.Assert`;
- in a function, a call to a function that has `Spec.Requires`, so the walker sees the call and its precondition (#69);

or when it calls a function that can raise.
All units of one strongly connected component of the call graph raise together.
`year % 4` does not raise, so a method that only uses it keeps its pure translation (chapter 5).
The claims inside `Spec.Requires` and `Spec.Ensures` are never run and are not scanned; their partial operations get
well-definedness obligations instead (chapter 6).

From that analysis come KTD11's rejections, all WRT0002, naming the construct and where it raises
(`src/Warrant.Extraction/Extractor.Effects.cs`):

| Construct | Why |
|---|---|
| `recursion with effects` | A recursive call inside a `bind` is out of reach of M5a's decrease obligations. |
| `contract on a recursive method` | A `Spec.Ensures`: its recursive call cannot use its own unproved triple. A `Spec.Requires` is allowed, and each recursive call is checked against it (#256). |
| `theorem calling a raising method` | A theorem is a `Prop`, not a program. The message says to state the property as a `Spec.Ensures`, or, for a property relating two calls, as the `Spec.Ensures` of a verified method that makes both calls (#181). |
| the raising operation itself (`division`, `nullable read`, `checked arithmetic`, `decimal arithmetic`, …) in a theorem statement | Lean's total operations would make `a / 0 == 0` provable. Same advice. |
| `Spec expression calling a raising method` | A `ClrM` program cannot sit inside a `Prop` (#165). |

A relational property of a raising method, such as monotonicity, needs two calls in one statement, and neither a
theorem nor a `Spec.Ensures` can state it; whether M6 should offer a route is the owner's open decision #181.

## Throw, checked arithmetic, `/`, `%` and `Math` (U7)

- `/` and `%` on `int` and `long`, including `/=` and `%=`. They throw in any context, so they always carry `wrap`
  rather than `checked` (KTD6).
- Checked arithmetic, from `checked(...)` or a `CheckForOverflowUnderflow` project: `+`, `-`, `*`, unary `-`, `++`/`--`
  and `long` to `int` narrowing; widening still wraps. The same operations inside an explicit `unchecked(...)` or
  `unchecked { }` carry `unchecked` (#236), whatever the project's setting; elsewhere they carry the project's default,
  `wrap` or `checked`.
- `throw new T(...)` as a statement, a throw expression or a whole expression body, when every argument is a constant
  or a parameter and `T` is a `System` exception or a plain subclass of one. A user exception type is checked strictly:
  a non-constant field or property initialiser, a static constructor, a primary constructor, or a base that is not a
  `System` exception is rejected, since any of them could make the program throw something other than the recorded
  type. `rethrow`, `try`, `finally` and `catch` stay rejected (`try`): nothing in M6 needs to catch, and matching a catch
  needs the CLR's exception hierarchy in trusted code.
- `Math.Min`, `Math.Max` and `Math.Abs` through the KTD23 table (`ModelledMembers.cs`), which fills the WRT0005 branch
  whose message already said "verified or modelled members". `Math.Round`, `Math.Sign` and the rest stay WRT0005.

## Nullable values and `decimal` (U17)

`int?`, `long?`, `bool?`, `decimal?` and nullable references to records and closed classes, for parameters, returns,
locals, record fields and `Spec.ForAll` variables, with `null`, `is null`, `is not null`, `== null`, `!= null`,
`HasValue`, `Value`, `(T)x`, `??` and `GetValueOrDefault()`.
The plan named only `int?` and `long?` (R2); `bool?` and `decimal?` came along because VIR's nullable type allows them,
and open-enum nullables stay rejected.

Where a `T?` value meets a place that needs a `T`, extraction inserts the non-null unwrap of KTD5 (#163), whatever
Roslyn's flow analysis says. A `var` reference local takes its initializer's type, since C# makes every `var` reference
local nullable and M4's locals would otherwise have changed.
Rejected, each by name: `null-forgiving operator` (`!`, found from syntax, since Roslyn has no operation for it),
`lifted comparison` and `lifted arithmetic` (`x > 0`, `x == 5`, `a + b` on nullable values, and `==` between two values
either of which is nullable, #76), `switch on a nullable value`, and in a theorem statement `nullable read`,
`non-null unwrap` and `decimal arithmetic`.
`GetValueOrDefault(d)` with an argument is not modelled (WRT0005). `decimal` is chapter 3.

## Contracts (U8)

A block body may start with `Spec` statements in a fixed order: `Spec.Decreases` if any, then `Spec.Requires`, then
`Spec.NoThrow` at most once (#182), then `Spec.Ensures` (KTD8, #88).
`Spec.NoThrow` takes no argument and becomes the VIR statement `nothrow{}`; it is rejected in a `[ContractFor]` class
member ("Spec.NoThrow in a contract member"), whose dependency's exceptions are always allowed.
Anything out of order or after another statement is WRT0002 saying what to do.
An expression-bodied member takes no contract (design Q17); the message says to use a block body, and the code fix that
would rewrite it is deferred.
`Ensures<T>`'s `T` must be the return type, nullable annotation included, or the awaited type of `Task<T>` or
`ValueTask<T>`; the message names the expected type (#105).

`Spec.Assert` becomes an `AssertStmt` where it stands, with its script.

A `[ProofFor(nameof(M))]` method is a static, parameterless method in `M`'s class whose body is
`Prove.Contract().By(...)` (KTD16); its script becomes `M`'s unit script, read as a theorem's script is, with
`Tactic.VcGen()` allowed (it is still `unsupported script argument` in a theorem's script).
`[ProofFor]` methods are indexed once per compilation (`ProofIndex.cs`) and shared with the analyzer, which now visits
them, so a problem with the `[ProofFor]` method itself is reported on it: no such method, an overloaded `M` (which
`nameof` cannot tell apart), an `M` that is not verified, another signature or body, and a second `[ProofFor]` for
`M`, which names the first.

`Spec.Implies` is accepted in theorem statements and, since the owner's decision on #213 (2026-11-12), inside a
`Spec.Requires` or `Spec.Ensures` condition, where it becomes an `ImpliesExpr` as in a theorem statement and translation
treats its premise as a guard of its conclusion (chapter 6). Anywhere else, `Spec.Assert` included, it is still WRT0004
(`Spec.Implies outside a theorem statement`).

## Dependencies, contract classes and `async` (U18)

**Dependencies** (KTD9).
A verified instance method of a class may call members of an interface through:

- a `readonly` instance field declared in its own class, or
- a primary-constructor parameter of its class that nothing assigns or passes by `ref` or `out` (design Q20's
  extension),

when the interface has a `[ContractFor]` class in the method's own compilation.
The interface may come from any assembly, since it is never translated.
Each call is an `ExternalCallExpr(type, dependencyIndex, memberKey, args)`, and the unit records one
`VirDependency(Name, Interface, Members)` per field or parameter, in order of first use.
Each member key is the key of that member's contract unit and is among the unit's dependencies, so editing a contract
class changes every caller's closure hash (#166).
Every other use of the class's state is rejected: `member access on this`, `dependency used other than to call a
member`, `property of a dependency`, and the dependencies that break the rule (`mutable dependency field`,
`assigned primary-constructor parameter`, `static dependency`, `inherited dependency`, `generic interface dependency`).
A dependency call inside a `Spec` expression is rejected: there is no world to run it in.
A class's verified instance method has no receiver in the model, only its dependencies, so a call to one from outside
it is rejected too.

**Contract classes** (KTD10).
`ContractIndex.cs` reads them once per compilation and shares them with the analyzer.
A contract class must be `file` or `internal`, `abstract` and non-generic, implement exactly the interface it names,
and contain only that interface's members (inherited ones, such as `IDisposable.Dispose`, included).
A member's body is `Spec.Requires`/`Spec.Ensures` calls then `return default!;`, those calls alone for a `void` member,
`=> default!`, which assumes nothing about the result, or none (`abstract`), which assumes nothing either.
A member whose signature uses an unmodelled type is accepted, and only a verified call to it is rejected.
A second contract class for one interface is rejected, naming the first.
Anything else is rejected with the step that failed, so a contract cannot hide code that would run.

Each interface member a verified method calls becomes a contract unit, keyed by the interface member, holding only its
contract member's leading `Spec.Requires` and `Spec.Ensures`.

**`async`** (KTD22).
`Task<T>` and `ValueTask<T>` return types become `task{T}`, `Task` and `ValueTask` `task{unit}`, and `void` `unit`.
An awaited call is an `AwaitExpr`; a statement that only calls (`F(x);`, `await F(x);`) is an `EvalStmt`.
A call that returns a task is accepted only as the direct operand of `await` (#67): an async method's exception is
captured in its task, so a discarded, stored or returned task would make the model throw where the CLR returns.
`_ = M();`, `var t = M(); await t;`, `ConfigureAwait`, `Task.WhenAll` and the other `Task` members, and `async void` are
rejected by name.

**Assumptions** recorded at extraction (chapter 8 renders them): `NonNull` for each dependency a method calls through,
for each non-nullable reference a called member returns, the `Task` included (#71; a `ValueTask` is a struct and gets
none), and for each non-nullable awaited reference and its record's reference fields; `ExternalContract` per member
called; and since U10, `CallerPrecondition` for a method's own `Spec.Requires` (#89).
The plan had `ExternalContract` added in U19 or U20; extraction already knows the member keys, so U18 adds it.

A few guards the plan did not ask for, each against an ambiguity that would otherwise pick an arbitrary contract or
evaluation order: an inherited member stated by two contract classes, a default-interface member without a contract
member, and named arguments out of order around a dependency or awaited call (the model evaluates in parameter order).

**Cancellation tokens and `return;`** (#215).
A `CancellationToken` parameter of a verified method or a contract member is `opaque{T:System.Threading.CancellationToken}`,
as KTD22 calls tokens opaque parameters, and its only use is to be passed on unchanged as an argument, to a dependency
member or a verified method.
Anything else that has a token type is `cancellation token other than a parameter`: `default`, `CancellationToken.None`,
an optional token argument left out, a local, a field of a record, a theorem's parameter, a `Spec.ForAll` over tokens.
Reading one (`ct.IsCancellationRequested`, `ct.ThrowIfCancellationRequested()`) calls an unverified member (WRT0005).
So nothing a proof reads depends on which token was passed; chapter 5 says how translation binds it.
A bare `return;` in a `void`, `Task` or `ValueTask` method is `return{lit{unit, 0}}`, the unit value a method that ends by
reaching the end of its body returns too.

## What moved between corpora

R14 says every accepted M4 and M5a member translates as before and every rejected one stays rejected, except those
whose construct M6 supports.
Those moved, keys unchanged, from `tests/corpus/m4/` to `tests/corpus/m6/`, and the M4 README's flip list records each:
`Halve`, `Remainder`, `Throws`, `NullableParameter`, `ReturnsNull` and `Decimals` are now proved; `CheckedAdd`,
`CallsUnverified` and the checked-project trio are now refuted (their implicit exceptions are possible); `Counter.Next`
is still rejected, now as `member access on this`.
New M4 members (`CallsUnmodelled`, `Tally.Current`) keep one rejected member for each diagnostic the moves would have
left uncovered.
The M4 and M5a VIR hashes are pinned and did not change.
