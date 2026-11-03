# How Warrant thinks about your code

> This page explains the ideas behind the [tutorial](tutorial.md) and the
> [how-to guides](how-to.md). It is background reading, not instructions. The
> full argument is in the [design document](../design.md).

## A proof is about a model of your method

When you mark a method `[Verified]`, Warrant doesn't run it. It translates the
method into a definition in Lean's logic, and your theorems are about that
definition. Your C# still runs exactly as you wrote it.

The proof is only as good as the match between the two, which the design calls
the *faithfulness gap*. Warrant narrows it in three ways:

- **The model follows the CLR, not mathematics.** `int` is a 32-bit
  two's-complement number that wraps around. `x + 1 > x` is false for
  `int.MaxValue`, so Warrant refuses to prove it. A model where `int` was an
  unbounded integer would be easier to prove things about, and those proofs
  would be wrong about your program.
- **Anything it can't model is an error.** It never approximates silently. A
  `[Verified]` method that uses `double` or reflection fails the build with
  WRT0002, instead of being translated into something close.
- **The model is tested against the real method.** For each translated method,
  Warrant generates inputs, runs your compiled code and the translated
  definition, and requires the results to agree.

That's why a counterexample in a failed proof is worth taking seriously. It
comes from a model built to behave like the CLR, so it usually reproduces in a
unit test.

## Theorems are tests for every input

A unit test checks one input. A `[Theorem]` with parameters checks every value
of every parameter: all four billion `int`s, every `null`, every combination.
That's also why a theorem fails where your tests passed. It reaches inputs your
tests never tried, such as a negative limit, an overflow or a null.

The other side of this: a theorem says exactly what it says. If you prove
`Payout(...) >= 0` only when `limit >= 0`, you have learned nothing about
negative limits. Conditions in `Spec.Implies` and `Spec.Requires` are where a
proof's scope is decided. Read them as carefully as the conclusion.

## Who you have to trust

Proof search is complicated. It includes the tactics, simplification, the
translation of contracts into goals, and caching. Warrant keeps all of it
**outside** what you have to trust. Tactics produce a proof term, which is a
complete, explicit derivation. A small checker, the **kernel**, then checks
that term step by step. The kernel is a port of Lean 4's kernel. Its verdicts
are cross-checked against Lean's own kernel on Lean's entire standard library.

So a bug in a tactic can make a true theorem fail to prove, but it can't make a
false theorem pass. That is also why a cached proof can be re-checked cheaply
(`WarrantRecheck`). Checking a proof is much faster than finding one.

What you **do** have to trust:

| Trusted | Why |
|---|---|
| The kernel | It decides what is proved. |
| The translation of C# into the model | The faithfulness gap above. |
| The definitions in the semantics library | The claim that "this is what `int` subtraction does". The lemmas about them are proved, not trusted. |
| Your contracts and the global assumptions | By design. See the next section. |

The assumption report is the list of things in the last row for each method.

## Contracts are hypotheses, not facts

A method that reads from a database can't be proved correct outright, because
Warrant can't see the database. A contract class says what you **assume** the
database does. Warrant then proves a conditional statement:

> For every implementation of `IPolicyStore` that keeps this contract, `Approve`
> keeps its contract.

The contract never becomes a global fact. That matters. If a contract is wrong,
or even contradictory, it can only weaken the proofs of the methods that use
it. It can't be used to prove something unrelated elsewhere in the program.
Lean calls global facts *axioms*, and a single bad axiom makes every statement
provable. Warrant doesn't create any.

The report lists every contract clause and every global assumption (for
example, "non-nullable annotations hold" or "nothing modifies this object
concurrently"). A proof can't do better than the assumptions it rests on, so
the report is where a reviewer should start.

## Why the specs are C# calls

Specifications are ordinary C#: `Spec.Ensures<int>(r => r >= 0)`. This has
practical advantages:

- Roslyn binds and type-checks them. Renaming a parameter renames it in the
  spec, and a typo is a compile error, not a verifier error.
- `&&`, `==` and `!` already mean what you'd expect. Warrant reinterprets
  them as logic only inside specs.
- The ones that return nothing (`Spec.Requires`, `Spec.Ensures`, `Spec.Assert`) are `[Conditional]`, so they don't exist in the compiled program. C# allows `[Conditional]` only on `void` methods, so value-returning helpers such as `Spec.Implies` and `Prove.That` stay in the IL; they are valid only inside theorem statements.

The cost is that C# attribute arguments must be constants, so specs can't live
in attributes. They sit at the top of method bodies, in the Code Contracts
tradition. Specs about interfaces live in contract classes.

## What Warrant doesn't do

- It doesn't change your program. Nothing it proves is used at run time.
- It doesn't prove anything about SQL, the database or external services. Those
  are always contracts.
- It doesn't handle concurrency, `unsafe`, reflection or floating point.
- Proved code can still fail in production if an assumption in its report is
  false. The proof makes those assumptions explicit, which turns them into
  something a reviewer can check.

## Choosing what to verify

Verification costs more than testing, and not everything is worth it. Good
candidates share three traits:

- **The rule matters.** Routing, eligibility, money, access control. A wrong
  answer is expensive or hard to notice.
- **The rule is crisp.** You can state what "correct" means in one or two
  lines. "Payouts never exceed the limit" is a good spec. "The email looks
  right" is not.
- **The edge cases are many.** Several flags interacting, ordering rules,
  thresholds, nulls. That's where tests miss cases and theorems don't.

Start with pure methods (M4 and M5a). Move to contracts (M6) once your team is
used to reading goals and assumption reports.
