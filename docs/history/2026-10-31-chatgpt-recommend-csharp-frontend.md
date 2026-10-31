# ChatGPT conversation: "Recommend CSharp Frontend"

- **Date:** 2026-10-31
- **Source:** shared ChatGPT conversation, `https://chatgpt.com/share/6ae6563c-08d4-83ea-ae80-37772f65d883`
- **Participants:** the project author and ChatGPT
- **Role in the project:** the starting point for LeanSharp's design. The design
  continued in a Claude Code session
  ([summary](2026-10-31-claude-design-session.md)) and is now captured in
  [`../design.md`](../design.md).

> **Provenance note.** This is the conversation text, extracted from a saved
> copy of the shared page. Only the conversation is kept; the ChatGPT interface
> (sidebar, account details) is omitted. Wording is unchanged. Formatting
> (headings, code blocks, tables, one formula) was reconstructed from the HTML,
> and bold and italics were lost. Inline citation chips are shown as
> _[cited: GitHub]_.
>
> **Accuracy note.** Some of ChatGPT's statements about Ansatz are inaccurate
> (for example the kernel node list, the location of `init-medium.ndjson`, and
> the Mathlib declaration counts). See *Appendix A* of the design document for
> the corrections, which were checked against the Ansatz source.

---

## User

Ansatz converted the Lean kernel to Java for use in Clojure. This seems like it would make eligible for C# to be a conversion target. And then we could write theorems in C#. Clojure has macros that make this portion trivial, but what method would you recommend for C#?

My initial thought was to add compiler extensions to Roslyn, but I don’t know if this is the appropriate method. (We already use compiler extensions in our code.)

## ChatGPT

I think your idea of using Roslyn is a good one, but I would approach it somewhat differently than modifying or extending the C# compiler itself.

My recommendation would be to use Roslyn source generators and analyzers to build an embedded theorem-proving language in C#, with the Lean kernel providing the trusted verification layer.

There are actually two interesting approaches here:

- Make C# a frontend for Lean, allowing you to express Lean terms, types, and proofs using C# syntax.
- Make C# a language with theorem-proving capabilities, where ordinary C# methods can carry specifications and proofs, somewhat like Dafny, Verus, or F*.

The first is considerably easier. The second is much more interesting, particularly if your goal is to verify actual C# programs.

The important distinction is that porting the Lean kernel to Java—or subsequently to C#—doesn't automatically make C# a theorem-proving language. The kernel checks proofs expressed in Lean's underlying type theory. You still need a frontend that translates C# expressions into terms that the kernel understands.

Here's how I'd approach that frontend.

### 1. What Ansatz actually provides

Looking at Ansatz's implementation, it's more ambitious than simply translating the Lean kernel.

Its architecture has three major components:

| Component | Ansatz | C# equivalent |
|---|---|---|
| Trusted kernel | Java | Port to C# or bridge to Java |
| Elaboration and tactics | Clojure | C# library |
| Surface language | Clojure macros | Roslyn |
| Runtime compilation | Clojure → JVM | C# → .NET |
| Proof libraries | Imported Mathlib | Same imported declarations |

Ansatz also supports tactics such as simp, omega, grind, and induction.

This is significant because you could potentially reuse much more than the kernel. You could port its elaborator and tactic implementations, or initially communicate with them through a JVM process.

The project's documentation also describes exporting proofs to Lean 4 for independent checking. That would be a particularly valuable feature for a C# implementation. _[cited: GitHub]_

### 2. How I would represent theorems in C#

I would start with ordinary C# methods annotated with attributes.

For example, imagine this:

```csharp
using Lean;

public static partial class Arithmetic
{
    [Theorem]
    public static Prop AddZero(Nat n)
        => n + 0 == n;

    [Proof(nameof(AddZero))]
    public static Proof AddZeroProof()
        => Tactics.Rfl();
}
```

This is illustrative syntax, not an existing API.

The Roslyn analyzer would:

- Discover methods annotated with [Theorem].
- Extract their syntax trees.
- Translate the theorem statements into Lean expressions.
- Elaborate the associated proofs.
- Submit the resulting proof terms to the kernel.
- Report verification failures as compiler diagnostics.

For example:

```text
error LEAN001:
Theorem 'AddZero' could not be verified.

Goal:
  n + 0 = n

Location:
  Arithmetic.cs(7,12)
```

One detail: C#'s == normally returns bool. You would need a special symbolic Prop representation and appropriate operator overloads, or an alternative such as Eq(n + 0, n).

That is manageable, but it's an early example of the differences between C# and Lean's type systems.

#### An alternative: expression-based proofs

You could also use a fluent API:

```csharp
[Theorem]
public static Proof AddZero(Nat n) =>
    Prove.That(Eq(n + 0, n))
         .By(Rfl());
```

This is attractive because it stays entirely within valid C# syntax.

It also gives you an obvious place to introduce tactics:

```csharp
[Theorem]
public static Proof AdditionCommutative(Nat a, Nat b) =>
    Prove.That(Eq(a + b, b + a))
         .By(
             Induction(a),
             AllGoals(Simp())
         );
```

I would probably begin here.

However, these methods must be interpreted symbolically. Executing Rfl() as an ordinary C# method cannot itself establish a theorem.

### 3. Where Roslyn fits

I would divide the implementation into three pieces.

#### A. Roslyn analyzer

This is where most of the interesting work happens.

Roslyn provides two useful representations:

- SyntaxNode: the syntactic structure of a C# expression.
- IOperation: a semantic representation with resolved operators, types, and method calls.

I would favor IOperation for translating C# expressions into Lean terms.

Consider:

```csharp
[Verified]
public static Nat Double(Nat n)
{
    return n + n;
}
```

Roslyn can tell you that the expression n + n is an addition operation over two values of type Nat.

Your translator could convert that into something conceptually equivalent to:

```lean
def Double (n : Nat) : Nat :=
  n + n
```

You could support a carefully chosen subset of C# initially:

| C# construct | Lean representation |
|---|---|
| Local variables | let expressions |
| Method parameters | Lambda binders |
| Method calls | Function application |
| if expressions | ite |
| Arithmetic | Nat/Int operations |
| Pattern matching | Match expressions |
| Generic types | Polymorphic expressions |
| Recursive methods | Recursive definitions with termination proofs |

Roslyn gives you type resolution and syntax analysis for free.

What it doesn't give you is Lean's dependent type elaboration.

That remains your responsibility.

#### B. Incremental source generator

I would use an IIncrementalGenerator to generate supporting code.

For example, given:

```csharp
[Verified]
public static partial Nat Factorial(Nat n);
```

The generator might produce the runtime implementation, wrappers, and proof metadata.

It could also generate a strongly typed API for imported Mathlib declarations.

However, source generators have an important limitation: they cannot rewrite existing user code. Microsoft's Roslyn documentation explicitly describes them as additive, rather than general-purpose language transformations. _[cited: GitHub]_

This means I would use the analyzer to understand existing methods and the generator to create new ones.

For the initial implementation, I would avoid trying to generate verified runtime code. Start with theorem checking, then add compilation.

#### C. Standalone verification engine

This would be a separate .NET library:

```text
LeanSharp.Kernel
LeanSharp.Elaboration
LeanSharp.Tactics
LeanSharp.Roslyn
LeanSharp.Generator
```

I would keep the kernel completely independent of Roslyn.

That would let you use the same kernel from:

- A Roslyn analyzer
- A command-line theorem checker
- An interactive REPL
- A language server
- Unit tests

It would also make differential testing against Lean and Ansatz easier.

### 4. The interesting alternative: embedded DSL versus compiler extension

There is another approach I think deserves serious consideration.

Use C# expression trees to represent propositions and proof expressions.

For example:

```csharp
Expression<Func<Nat, bool>> theorem =
    n => n + 0 == n;
```

The expression tree gives you a structured representation without writing a Roslyn parser.

You could translate that expression tree into Lean's expression representation.

The advantage is that your theorem API would work as an ordinary .NET library, without requiring a source generator for basic functionality.

The disadvantages are substantial, however:

- Expression trees support only a subset of C#.
- They don't represent arbitrary method bodies.
- They don't support dependent types directly.
- They have restrictions involving newer C# syntax.
- They cannot represent Lean's universe hierarchy naturally.

Consequently, I would use expression trees for a prototype, but Roslyn for the eventual implementation.

In particular, Roslyn's semantic model provides much more information about the source program.

### 5. The biggest challenge isn't the kernel

The biggest challenge will be the difference between C#'s type system and Lean's dependent type system.

Consider:

```lean
def Vector (α : Type) (n : Nat) : Type
```

A vector's length is part of its type.

In Lean, you can write:

```lean
def append
    (xs : Vector α n)
    (ys : Vector α m) :
    Vector α (n + m)
```

There is no direct equivalent in C#'s generic type system.

You could approximate this with:

```csharp
Vector<T, N>
```

But N must be a type argument, not a runtime natural-number value.

You could encode Peano naturals as types, but that becomes awkward quickly.

My preference would be to keep the C# type system responsible for ordinary programming and let the Lean elaborator manage dependent types internally.

For example, you might define:

```csharp
[LeanDefinition]
public static Vec<T> Append<T>(
    Vec<T> xs,
    Vec<T> ys);
```

Then provide additional specifications describing the relationship between input and output lengths.

The Roslyn analyzer would check those specifications using Lean's richer type system.

This would effectively give you two layers of typing:

- C# typing for ordinary .NET compilation.
- Lean typing for mathematical correctness.

That is not unlike how refinement-type systems operate.

### 6. An important question: What exactly are you proving?

There is a subtle but critical issue with the approach I've described.

Suppose you write:

```csharp
[Verified]
public static int Increment(int x)
{
    return x + 1;
}
```

And prove:

```csharp
[Theorem]
public static Prop IncrementCorrect(int x)
    => Increment(x) > x;
```

There are at least two problems.

First, C# int is a bounded 32-bit integer, whereas Lean's Int is unbounded. The theorem is false for ordinary unchecked C# arithmetic when x == int.MaxValue.

Second, the Lean kernel verifies the translated mathematical representation, not necessarily the behavior of the compiled .NET method.

You must establish that the translation preserves the relevant semantics.

This is particularly important when dealing with:

- Integer overflow
- Null references
- Exceptions
- Mutable state
- Aliasing
- Concurrency
- Nontermination

Ansatz recognizes a related problem. Its documentation describes differential checking between compiled JVM functions and kernel evaluation to detect translation discrepancies. _[cited: GitHub]_

For C#, I would initially restrict verified methods to pure, total functions over explicitly modeled mathematical types.

You could later expand to mutable state using Hoare logic or weakest-precondition verification.

That would move the project closer to Dafny or Verus.

### 7. Would I modify Roslyn itself?

No—not initially.

I would use the existing extension mechanisms.

| Approach | Recommendation |
|---|---|
| Roslyn analyzer | Essential |
| Incremental source generator | Recommended |
| Expression trees | Useful for prototyping |
| Roslyn code fixes | Excellent developer experience |
| C# compiler fork | Avoid initially |
| Custom C# preprocessor | Only if dependent-type syntax becomes essential |
| Custom MSBuild verification task | Recommended for reliable build enforcement |

I would also separate interactive verification from build verification.

An analyzer can provide immediate feedback in the editor, but an MSBuild verification step should be authoritative and fail the build when required proofs cannot be checked.

That avoids depending on IDE analyzer execution for your correctness guarantees.

### 8. What I would build first

I'd suggest a small proof of concept with three capabilities.

First: Theorem declarations

```csharp
[Theorem]
public static Proof ZeroAdd(Nat n) =>
    Prove.That(Eq(0 + n, n))
         .By(Induction(n), AllGoals(Simp()));
```

Second: Imported Mathlib theorems

```csharp
[Theorem]
public static Proof AddComm(Nat a, Nat b) =>
    Prove.That(Eq(a + b, b + a))
         .By(Apply(Mathlib.Nat.AddComm));
```

This would demonstrate that your C# frontend can use existing Lean mathematics.

Third: Verification diagnostics

A failed proof should produce an ordinary C# compiler diagnostic, with the unresolved goal included in the message.

That would give you a genuinely useful theorem-proving environment before implementing any verified C# code generation.

#### One additional architectural suggestion

Given Ansatz's existing Java implementation, I wouldn't port the entire kernel immediately.

I would initially build:

```text
             C# Source
                 │
                 ▼
          Roslyn IOperation
                 │
                 ▼
          C# Elaborator
                 │
                 ▼
         Lean Expression IR
                 │
                 ▼
         Ansatz Java Kernel
                 │
                 ▼
          Proof Verification
                 │
                 ▼
         Roslyn Diagnostics
```

The bridge could use a persistent Java subprocess with a compact binary protocol. That is much simpler to debug than embedding a JVM in .NET.

Once the frontend works, you could port the Java kernel to C# without changing the elaborator.

Eventually, you could also use Ansatz's Lean exporter to have the original Lean kernel independently check your generated proofs.

### 9. One possibility I find particularly intriguing

C# has something that Clojure doesn't have in quite the same form: a rich, compiler-provided semantic model accessible through Roslyn.

Clojure macros make syntactic transformations remarkably convenient. But they don't automatically provide the static type and symbol information Roslyn offers.

This suggests a potentially powerful design:

Use Roslyn to elaborate ordinary C# expressions into Lean expressions, and let Lean verify properties of those expressions.

Rather than trying to reproduce Lean's syntax, you could create a verification system that feels native to C#.

For instance:

```csharp
[Verified]
public static Nat Sum(Nat a, Nat b)
    => a + b;

[Theorem]
public static Proof SumCommutative(Nat a, Nat b)
    => Prove.That(Eq(Sum(a, b), Sum(b, a)))
            .By(Simp(Mathlib.Nat.AddComm));
```

This is substantially more attractive to me than embedding Lean source strings inside C#.

It also has the advantage that Visual Studio, Rider, and other Roslyn-based tooling could understand the code without requiring a new language parser.

#### My recommendation

I would start with Roslyn + a C# theorem DSL + the Ansatz kernel, not a Roslyn compiler fork.

There is one architectural decision I'd make early, though:

Do you want to write mathematical proofs in C#, or do you want to prove the correctness of C# programs?

For the former, the architecture above is relatively straightforward.

For the latter, I would seriously consider introducing a verification intermediate representation and a weakest-precondition calculus from the beginning. That would make the project significantly more ambitious, but it could ultimately become something like Verus for C#, with Lean providing the trusted proof checker.

Given your interest in both Lean and formal verification, I suspect the second direction might be especially appealing.

## User

Does Ansatz actually translate the Clojure theorems into Lean, or does it lower them into some IR that the kernel uses?

## ChatGPT

Ansatz lowers Clojure expressions into an intermediate representation (IR) understood by its Java implementation of the Lean kernel. It does not ordinarily translate Clojure into Lean source code.

Specifically, that IR is the Calculus of Inductive Constructions (CIC) expression representation, essentially the same representation used internally by Lean 4.

According to the Ansatz architecture documentation, the pipeline looks like this:

```text
Clojure source
      │
      ▼
Clojure macro expansion
      │
      ▼
Ansatz elaborator
      │
      ▼
CIC expressions (Expr.java)
      │
      ▼
Tactic execution (if needed)
      │
      ▼
Proof term
      │
      ▼
Java kernel (TypeChecker.java)
      │
      ▼
Verified theorem
```

#### What does the IR look like?

Ansatz's Expr.java implements the same 11 expression-node types as Lean 4's kernel:

| Expression | Purpose |
|---|---|
| BVar | Bound variable (de Bruijn index) |
| FVar | Free variable |
| MVar | Metavariable |
| Sort | Universe or proposition |
| Const | Reference to a declaration |
| App | Function application |
| Lam | Lambda abstraction |
| ForallE | Dependent function type |
| LetE | Local definition |
| Lit | Literal value |
| MData | Metadata annotation |

The kernel also represents universe levels, declarations, inductive types, and their recursors.

The important point is that this is a language-independent representation.

For example, a Clojure theorem:

```clojure
(a/theorem add-comm [n :- Nat, m :- Nat]
  (= Nat (+ n m) (+ m n))
  (simp "Nat.add_comm"))
```

is elaborated into a proposition and proof term expressed using those CIC nodes.

The kernel checks the resulting proof term, not the original Clojure syntax.

#### What this means for C#

This actually simplifies your proposed architecture considerably.

You wouldn't need to translate C# into Lean syntax at all.

Instead:

```text
C# Source
    │
    ▼
Roslyn
    │
    ▼
C# → CIC Elaborator
    │
    ▼
CIC Expression IR
    │
    ▼
Ansatz Kernel (ported to C#)
    │
    ▼
Verified Proof
```

You could even define C# records corresponding directly to the kernel's expression types:

```csharp
public abstract record Expr;

public record BVar(int Index) : Expr;

public record Sort(Level Universe) : Expr;

public record Const(
    Name Name,
    IReadOnlyList<Level> Levels) : Expr;

public record App(
    Expr Function,
    Expr Argument) : Expr;

public record Lam(
    Name Name,
    Expr Type,
    Expr Body,
    BinderInfo BinderInfo) : Expr;

public record ForallE(
    Name Name,
    Expr Type,
    Expr Body,
    BinderInfo BinderInfo) : Expr;
```

These are illustrative C# definitions, not a transcription of Ansatz's Java classes.

You would then implement the remaining expression nodes, universe representation, and declaration environment.

#### There's another interesting capability

Ansatz also supports exporting its verified theorems into Lean 4 source code, allowing the original Lean kernel to independently check them.

That's a separate operation from its normal verification pipeline.

The Lean 4 for Clojurians documentation explicitly distinguishes these two capabilities.

For your C# implementation, I'd strongly recommend preserving that export capability.

It would give you two verification paths:

- C# → CIC → C# kernel.
- C# → CIC → Lean exporter → original Lean kernel.

This is particularly useful when developing and testing your kernel port.

One important observation: The kernel's IR is relatively small. The complicated part is elaboration—turning convenient source-language expressions into fully explicit, well-typed CIC expressions.

That makes me even more inclined to recommend Roslyn as your frontend, with a separate CIC elaborator. You wouldn't be extending C#'s type system so much as providing a second, more expressive type system alongside it.

## User

“Ansatz also supports exporting its verified theorems into Lean 4 source code, allowing the original Lean kernel to independently check them.”

This is especially important, to make sure that the kernel itself is working. And there are now multiple Lean kernels, so even more assurance that the C# version is working.

## ChatGPT

Exactly. And there's an important distinction between testing the correctness of the C# kernel and independently verifying the proofs it accepts.

I'd actually build three levels of verification into the project:

- Differential testing: Feed identical CIC expressions and declaration environments to the C# kernel, Lean 4's kernel, and other independent implementations. Compare whether they accept or reject each expression, and, where appropriate, compare inferred types and normalization results.
- Proof certificate verification: Export the C# system's elaborated proof terms and have Lean 4 independently check them. Ideally, export the actual proof terms rather than reconstructing proofs using tactics. Otherwise, you're testing whether Lean can find a proof, not whether the C# kernel accepted a valid proof certificate.
- Negative testing: Deliberately construct malformed terms, invalid universe constraints, incorrect de Bruijn indices, and unsound inductive declarations. All kernels should reject them. This is particularly important because agreement on valid proofs alone doesn't establish soundness.

There's also a fourth possibility that I think fits your interests particularly well: property-based testing of the kernel itself.

For example, generate well-typed CIC expressions and test properties such as:

- Substitution preserves typing under the appropriate conditions.
- Definitional equality is symmetric and transitive.
- Normalization preserves types.
- Alpha-equivalent expressions produce equivalent results.
- Universe instantiation preserves well-formedness.

You could use FsCheck for generating test cases and, eventually, Lean itself to specify or prove properties of the C# implementation.

#### One architectural consideration

I'd make the CIC representation serializable from the beginning, including declarations, universe levels, and environment dependencies.

That would let you construct a test harness like:

```text
                  CIC Test Corpus
                         │
           ┌─────────────┼─────────────┐
           ▼             ▼             ▼
       C# Kernel     Lean 4 Kernel   Kernel N
           │             │             │
           └─────────────┼─────────────┘
                         ▼
                  Compare Results
                         │
                         ▼
                Discrepancy Report
```

It would also allow you to preserve every discovered discrepancy as a regression test.

One caveat: Multiple kernels agreeing doesn't constitute a formal proof of correctness, particularly if they share implementation assumptions or bugs. But independently implemented kernels, especially in different languages, provide substantially stronger evidence than testing a single implementation.

And here's something I find particularly appealing about your idea: because the C# frontend and kernel would be separate components, you could eventually use the original Lean kernel as the authoritative verifier while developing the C# kernel.

That means you could start writing C# theorems before trusting your own kernel implementation.

I would make that a foundational design decision rather than adding independent verification later.

## User

If I were to do this, would it be possible to create theorems for just a portion of a function, say a function that had some checks and logic at the top, and if those were satisfied, pulled something from the database, and then performed some more checks and logic, and then saved it back. But I want to just prove the properties of the logic but assume that the database functions worked.

## ChatGPT

Yes. In fact, I think this would be one of the most useful applications of a Lean-backed C# verification system. What you're describing is modular verification, using contracts, assumptions, and Hoare logic.

You could verify selected portions of an otherwise ordinary C# function while treating database operations as trusted external functions with specified behavior.

For example, imagine:

```csharp
public async Task<Result> ProcessPayment(int paymentId)
{
    // Ordinary business logic
    if (paymentId <= 0)
        return Result.InvalidId;

    // External operation
    var payment = await db.GetPayment(paymentId);

    if (payment is null)
        return Result.NotFound;

    // Business logic we want to verify
    if (payment.Amount <= 0)
        return Result.InvalidAmount;

    if (payment.Status != PaymentStatus.Pending)
        return Result.InvalidStatus;

    payment.Status = PaymentStatus.Processed;

    // External operation
    await db.SavePayment(payment);

    return Result.Success;
}
```

You could verify properties of the logic before and after the database calls without proving anything about the database implementation.

### 1. The simplest approach: Extract pure functions

This would be my preferred starting point.

Move the business logic into pure functions:

```csharp
public static PaymentResult ValidatePayment(Payment payment)
{
    if (payment.Amount <= 0)
        return PaymentResult.InvalidAmount;

    if (payment.Status != PaymentStatus.Pending)
        return PaymentResult.InvalidStatus;

    return PaymentResult.Valid;
}
```

Then specify properties:

```csharp
[Theorem]
public static Proof ValidPaymentHasPositiveAmount(Payment p) =>
    Prove.That(
        Implies(
            Eq(ValidatePayment(p), PaymentResult.Valid),
            p.Amount > 0
        )
    ).By(Simp());
```

Your ordinary application can call this function without knowing anything about Lean.

The verification system translates the pure function into CIC and proves the property.

This gives you substantial benefits without requiring a complete formal semantics for C#.

There is one crucial requirement: the verifier must establish that the translated function accurately models the compiled C# function. Otherwise, you're proving a property of a mathematical model rather than necessarily of the executable code.

### 2. More interesting: Verify regions within a function

You could go further and introduce explicit verification boundaries.

For example, imagine a C# API like this:

```csharp
public async Task<Result> ProcessPayment(int paymentId)
{
    var payment = await db.GetPayment(paymentId);

    if (payment is null)
        return Result.NotFound;

    using (Verify.Region(
        requires: () => payment.Amount > 0,
        ensures: () =>
            payment.Status == PaymentStatus.Processed))
    {
        if (payment.Status != PaymentStatus.Pending)
            return Result.InvalidStatus;

        payment.Status = PaymentStatus.Processed;
    }

    await db.SavePayment(payment);

    return Result.Success;
}
```

This is conceptual syntax, not a working implementation.

It illustrates an important distinction: the postcondition above is not valid for every execution path. If the payment is not pending, the function returns early without setting its status to Processed.

The contract would need to describe that possibility, or the region would need an additional precondition that the status is Pending.

This is precisely the sort of problem a verification system should catch.

I would probably implement verification regions using Roslyn analyzers rather than trying to make Verify.Region perform verification at runtime.

Roslyn can identify the region's control-flow graph and translate the relevant operations into a verification representation.

For example:

```text
C# method
    │
    ▼
Roslyn control-flow graph
    │
    ├── Ordinary C# operations
    │
    ├── Verified region
    │       │
    │       ▼
    │   Verification conditions
    │       │
    │       ▼
    │   Lean proof terms
    │       │
    │       ▼
    │   Kernel verification
    │
    └── Ordinary C# operations
```

That architecture would support proving properties of selected code blocks without requiring every statement in a method to be formally verified.

### 3. Database calls become contracts

Suppose your application uses:

```csharp
var payment = await db.GetPayment(paymentId);
```

You could describe the database operation using an assumed contract:

```csharp
[External]
[Ensures("result == null || result.Id == paymentId")]
public Task<Payment?> GetPayment(int paymentId);
```

The verifier would assume that the returned payment either doesn't exist or has the requested ID.

You wouldn't need to verify the SQL query, database driver, or network protocol.

However, the assumption becomes part of your trusted computing base.

If the database method violates its contract, the proof of the calling code no longer guarantees the desired behavior.

This is normal in modular verification. The same principle is used in systems such as Dafny, where methods can have preconditions and postconditions without exposing their implementations.

### 4. I'd introduce Requires, Ensures, and Invariant

For a C# verification language, I would favor familiar design-by-contract terminology.

For example:

```csharp
[Verified]
[Requires("payment.Amount > 0")]
[Requires("payment.Status == Pending")]
[Ensures("payment.Status == Processed")]
public static void ProcessPayment(Payment payment)
{
    payment.Status = PaymentStatus.Processed;
}
```

The strings are placeholders for a possible API; I would prefer strongly typed expressions or Roslyn-recognized contract methods in a real implementation.

An alternative might look like:

```csharp
[Verified]
public static void ProcessPayment(Payment payment)
{
    Contract.Requires(payment.Amount > 0);
    Contract.Requires(payment.Status == PaymentStatus.Pending);

    payment.Status = PaymentStatus.Processed;

    Contract.Ensures(payment.Status == PaymentStatus.Processed);
}
```

This is much closer to the way C# developers already think about program correctness.

There is a complication, though: C# contracts that refer to mutable objects require a model of the heap and object identity. For a first implementation, immutable records and pure functions would make verification substantially easier.

### 5. How Lean would prove these properties

This is where the architecture gets especially interesting.

For a selected C# function, you could generate verification conditions using weakest preconditions.

Suppose you have:

```csharp
if (payment.Amount > 0)
{
    payment.Status = PaymentStatus.Processed;
}
```

And want to prove:

```text
payment.Status == Processed
```

The weakest precondition would be approximately:

```text
payment.Amount > 0
    AND
(payment.Status := Processed establishes the postcondition)
```

More precisely, if the amount is nonpositive, the status remains unchanged, so the weakest precondition is:

$$(\text{Amount} > 0) \lor (\text{Status} = \text{Processed})$$

That is the condition under which the final status is guaranteed to be Processed, assuming the assignment behaves as modeled.

You could express the resulting verification condition in Lean and prove it using tactics such as simp, omega, or grind.

The kernel would check the proof term generated by those tactics.

This is fundamentally different from attempting to execute C# code inside the Lean kernel.

### 6. The design I would recommend

Given your interest in both Lean and practical C# verification, I would build toward three verification modes:

| Mode | Purpose | Complexity |
|---|---|---|
| Pure functions | Verify business logic and mathematical properties | Low |
| Verified regions | Verify selected blocks within ordinary methods | Medium |
| Contract-based methods | Verify methods that interact with databases, APIs, and mutable state | High |

I'd start with pure functions, then introduce verified regions using a restricted subset of C#.

The key design principle would be:

Verification should be opt-in, compositional, and capable of treating external operations as explicitly declared assumptions.

That would let you gradually add formal verification to an existing enterprise C# application rather than requiring a rewrite into a specialized language.

#### One particularly useful feature

I would have the verification system generate an assumption report alongside each verified theorem.

For example:

```text
Theorem: ProcessPaymentCorrect
Status: VERIFIED

Assumptions:
  - GetPayment returns a payment matching the requested ID.
  - SavePayment persists the supplied payment.
  - No concurrent modification occurs between read and write.
  - Payment.Amount uses mathematical integer semantics.

Verified properties:
  - Invalid payments are not processed.
  - Successful processing requires a positive amount.
  - Successful processing changes status to Processed.
```

This would make the trust boundaries explicit.

In a real database application, concurrency assumptions are especially important. A proof about the logic between reading and writing a record doesn't automatically establish correctness if another transaction can modify that record in the meantime.

The really appealing possibility is that you could take an existing C# application, annotate just the business-critical sections, and gradually accumulate machine-checked correctness guarantees without changing the rest of the application.

That strikes me as a particularly practical direction for the system you're considering.

## User

I like these ideas on the representation. How does Ansatz import the Lean proofs? I am presuming there is some sort of way to import the Lean libraries as kernel IR instead of having a Lean compiler built in?

## ChatGPT

Yes, exactly! Ansatz uses lean4export to export Lean's declarations directly into a serialized representation of the kernel's IR. It doesn't need a Lean compiler or elaborator built into Ansatz to import Mathlib.

I checked the Ansatz repository, and the mechanism is quite straightforward.

### 1. How Ansatz imports Mathlib

The pipeline looks like this:

```text
            Lean 4 / Mathlib
                   │
                   ▼
             Lean Compiler
                   │
                   ▼
          Compiled .olean files
                   │
                   ▼
              lean4export
                   │
                   ▼
           NDJSON (~5 GB)
                   │
                   ▼
          Ansatz Importer
                   │
                   ▼
       Persistent Declaration Store
                   │
                   ▼
          Java CIC Kernel
```

The important distinction is that Lean compiles the libraries ahead of time, but Ansatz consumes the exported declarations without running the Lean compiler itself.

The repository documents these steps:

#### Step 1: Export Mathlib

```bash
cd mathlib4

lake env ../lean4export/.lake/build/bin/lean4export \
    --export-mdata Mathlib > mathlib.ndjson
```

This produces approximately 5 GB of newline-delimited JSON.

The export contains the declarations needed to reconstruct the kernel environment, including their types, definitions, proof terms, and inductive information.

#### Step 2: Import into Ansatz

Ansatz provides an importer:

```clojure
(require '[ansatz.export.storage :as s])

(def store (s/open-store "/path/to/store"))

(s/import-ndjson-streaming!
    store
    "mathlib.ndjson"
    "mathlib"
    :verbose? true)
```

The importer parses the serialized declarations and stores them in Ansatz's persistent declaration store.

#### Step 3: Load the environment

When running Ansatz:

```clojure
(require '[ansatz.core :as a])

(a/init! "mathlib")
```

Ansatz initializes its declaration environment using the imported store.

It can then reference Mathlib theorems without compiling Mathlib or executing Lean.

The repository reports approximately 648,000 imported Mathlib declarations, including more than 210,000 theorems. _[cited: GitHub]_

### 2. The interesting part: Proofs are already elaborated

This is particularly relevant to your C# idea.

Consider the Lean theorem:

```lean
theorem add_zero (n : Nat) : n + 0 = n := by
  simp
```

When exported, you don't get the original simp tactic.

Instead, you get the elaborated proof term.

Conceptually, it might resemble:

```text
Declaration:
    Name: add_zero

    Type:
        ∀ (n : Nat), n + 0 = n

    Value:
        <fully elaborated CIC proof term>
```

The actual serialization is more involved, but the essential point is that all the elaboration and tactic execution have already happened.

Your C# kernel doesn't need to understand simp, omega, grind, or any other Lean tactic to import these theorems.

It only needs to understand the kernel expression language and declaration environment.

This also means that you could implement a C# theorem prover incrementally:

- Import Lean declarations.
- Implement a kernel capable of checking them.
- Reference imported theorems from C#.
- Add your own elaboration and tactic capabilities.

You wouldn't need to implement Lean's tactics before using Mathlib.

### 3. You can independently verify the imported declarations

Ansatz includes a facility for checking imported declarations using its own kernel.

For example:

```clojure
(s/verify-from-store!
    store
    "mathlib"
    :verbose? true
    :timeout-ms 300000)
```

This checks the imported environment rather than merely trusting that the serialized data is valid.

The project's kernel validation documentation also describes comparing its Java kernel against an instrumented Lean 4 kernel.

For your C# implementation, this would be an excellent testing strategy.

You could start with a small Lean environment, then progressively work toward checking all of Mathlib.

### 4. What I would do differently for C#

I would make the imported declaration store independent of the theorem-proving frontend.

Something like:

```text
Lean4Export
    │
    ▼
LeanSharp.Importer
    │
    ▼
LeanSharp.Store
    │
    ├── LeanSharp.Kernel
    │
    ├── LeanSharp.Elaborator
    │
    ├── LeanSharp.Tactics
    │
    └── LeanSharp.Roslyn
```

The store could expose a simple interface:

```csharp
public interface IDeclarationStore
{
    Declaration? GetDeclaration(Name name);

    bool Contains(Name name);

    IEnumerable<Name> FindDeclarations(string prefix);
}
```

And the kernel could resolve imported declarations through that interface.

One advantage is that you could implement lazy loading. With hundreds of thousands of declarations, you wouldn't necessarily want to deserialize the entire environment into memory.

Ansatz already uses an immutable environment with on-demand loading from its persistent store.

#### An even simpler starting point

Ansatz includes a smaller export:

```text
test-data/init-medium.ndjson
```

It's approximately 10 MB and contains 2,997 declarations.

That would be an excellent starting corpus for your C# implementation.

You could build a kernel importer and verify those declarations before tackling Mathlib.

### 5. One architectural distinction worth preserving

I'd distinguish between importing a theorem and trusting a theorem.

Suppose your C# system imports:

```lean
Nat.add_comm
```

There are two ways to handle it:

Trusted import: Accept the declaration because Lean previously verified it.

Verified import: Recheck the declaration and its proof term using your C# kernel.

For an initial implementation, trusted imports would be convenient.

But given your interest in validating the C# kernel itself, I'd strongly recommend supporting verified imports from the beginning.

This gives you an unusually valuable test suite: thousands—or eventually hundreds of thousands—of real-world proofs already known to be accepted by Lean.

#### One final observation

You don't actually need to port Ansatz's storage implementation.

You could reuse its exported NDJSON files and implement a native C# importer.

That would let you concentrate on the kernel and Roslyn integration rather than building a Lean export mechanism.

In fact, I'd make importing and independently checking init-medium.ndjson the first milestone of the entire project. Once that works, you have a functioning C# implementation of a substantial part of Lean's trusted foundation, and you can start building the C# theorem language on top of it.

If you want, I can:

- Explain how to verify imported Lean proofs in C#
- Describe strategies for lazy loading large Lean declaration stores
- Suggest how to integrate Roslyn analyzers with imported Lean proofs
