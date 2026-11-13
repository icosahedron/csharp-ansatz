# Warrant Design

> Status: **draft, design phase** · Started 2026-10-31
> History: [ChatGPT conversation](history/2026-10-31-chatgpt-recommend-csharp-frontend.md) ·
> [Claude design session](history/2026-10-31-claude-design-session.md)

Warrant verifies properties of ordinary C# code with machine-checked proofs.
C# methods are translated into terms of the Calculus of Inductive Constructions
(CIC), the type theory of Lean 4. Proofs about those terms are checked by a
C# port of the Lean 4 kernel, and the existing Lean libraries (Init, Std,
Mathlib) are available as imported, already-elaborated declarations.

The project is inspired by [Ansatz](https://github.com/replikativ/ansatz), which
does the same for Clojure. Ansatz is a Lean 4 kernel in Java with an elaborator,
tactics, and a Clojure surface language. Warrant keeps Ansatz's foundations
(kernel, lean4export import, independent re-checking) but takes the opposite
direction at the surface: **it verifies existing C# rather than generating code
from verified definitions.** See §2.

---

## 0. Decision log

| # | Decision | Status |
|---|---|---|
| D1 | **Verify existing C# (direction B).** Translate C# into a CIC model and prove properties of the model. Do not generate C# from verified terms (direction A). | Decided |
| D2 | Verification runs in a **long-lived verification server**, not in the IDE's analyzer process. | Decided |
| D3 | Name **Warrant**: in logic, a warrant is what justifies a claim, and every proof comes with the assumptions it rests on. Replaces the working name LeanSharp, which named the project after Lean rather than what it does (§12 Q12). | Decided |
| D4 | License **Apache 2.0**, with NOTICE attribution to Lean 4 and Ansatz. | Decided |
| D5 | **Port the kernel** to C#. Don't bridge to Ansatz's JVM kernel. | Proposed, not objected to |
| D6 | Cross-check by **exporting lean4export NDJSON**, not by pretty-printing Lean source. | Proposed, not objected to |
| D7 | Map C# types to **faithful Lean models** (`int` → `Int32` with wrap-around, not unbounded `Int`). | Decided (M4 is built on it) |
| D8 | Target **net10.0** for the server and core libraries. Components loaded by Roslyn or MSBuild, and the user API package, target **netstandard2.0**, so projects on older frameworks can be verified. | Decided |
| D9 | External dependencies (databases, services) are **hypotheses in the theorem**, never global axioms. | Proposed |
| D10 | The C# semantic model is a **Lean 4 library written and proved in real Lean**, exported to NDJSON, and shipped with Warrant. | Decided (M4 is built on it) |
| D11 | Verification-condition generation is **proof-producing (a tactic)**, so it is outside the trusted base. | Proposed |
| D12 | Enums are **open by default**: modelled as their underlying integer, so proofs cover unnamed values. `[Closed]` opts in to modelling exactly the named values; that is an assumption, listed in the report, and the analyzer warns on integer casts to the type (§12 Q3). | Decided |
| D13 | `[Closed]` also applies to **closed-set classes**, recognised **by shape**: sealed, private constructors only, and static instances of the type itself, each an initialised get-only auto-property or `static readonly` field whose initialiser is a `new` of the class, created by code that cannot throw (constant arguments, constant initialisers, and constructors that only assign constants or parameters; [docs/m4/03](m4/03-extraction.md), #24). They translate to an `inductive` with one constructor per instance, and `==` compares a generated `$index` (not `DecidableEq`; see §6.1); a `[Closed]` class without that shape is error WRT0009. Instances created or static instances replaced without a constructor call where Warrant can see it (`MemberwiseClone`, `with`, `[UnsafeAccessor]`) are rejected too; reflection, serializers and code Warrant does not see are excluded by the `closed` assumption the report lists (#55). Adjust the shape rule if real code needs it (§12 Q16). | Decided |
| D14 | **Budgets** (§12 Q8): kernel fuel stays at 20M steps for builds and 100M for corpus runs, tactics get their own fuel (171,970 steps by default), and each theorem gets a 30-second wall-clock limit. All three are adjustable per project (MSBuild properties) and per theorem (`[Theorem]` arguments). Exhausting one fails the theorem. | Decided (M5a is built on it) |
| D15 | **CI trust** (§12 Q9): every build re-checks every proof with the kernel. M5a has no cache; trusting signed caches waits for M5b's cache. | Decided for M5a; replaced by D17 |
| D16 | **The CLI builds the compilation, not the MSBuild task** (§8.3): the task passes Csc's own arguments to `warrant verify`, which runs as a child process. M5b keeps the child: it compiles and extracts, and sends VIR to the server, which stays free of Roslyn (§3.2). | Decided (M5a and M5b are built on it) |
| D17 | **Cache trust** (§12 Q9): a cache hit is trusted locally. An entry is written only after the kernel admitted the unit's certificate, and carries a content hash and the toolchain identity, so accidental damage or another build of Warrant is a miss; a deliberate edit of `obj/warrant/` is outside what a local build defends against. `WarrantRecheck=true` makes the kernel re-check every cached proof against statements rebuilt from the current code, without tactics, and is recommended for CI. Chosen over kernel-checking every hit, which would make `WarrantRecheck` redundant, and over entries signed with a per-user key, which adds key management and stops CI agents sharing entries (§8.2). | Decided (M5b is built on it) |

---

## 1. Goals and non-goals

### Goals

1. **Opt-in, incremental verification of existing C#.** Annotate the
   business-critical parts of an existing application and leave the rest alone.
   There are three modes, in order of difficulty:
   - **Pure functions**: business logic and mathematical properties.
   - **Contract-based methods**: methods that call databases or services,
     specified with preconditions, postconditions and assumed contracts for the
     external calls.
   - **Verified regions**: selected blocks inside otherwise ordinary methods.
2. **A small, cross-checked trusted base.** A CIC kernel ported to C#, whose
   verdicts are compared against independent Lean kernels.
3. **Reuse of Lean's libraries** through lean4export NDJSON. No Lean toolchain
   is needed at verification time.
4. **Ordinary C# developer experience.** Specifications and proofs are valid C#
   that Roslyn binds and type-checks. Failures are compiler diagnostics that
   show the unsolved goal.
5. **Explicit trust.** Every result comes with an assumption report listing
   what was assumed rather than proved.

### Non-goals (for now)

- Generating executable C# from verified definitions (direction A).
- Forking Roslyn or adding new C# syntax.
- Concurrency, `unsafe`, reflection, `dynamic`, floating-point reasoning.
- Proving anything about SQL, drivers, or the database itself.
- Accepting Lean surface syntax or Lean tactic scripts as input.

---

## 2. Why direction B, and what it costs

In Ansatz, `a/defn` elaborates a Clojure form into a CIC term, the kernel
checks it, and the **executable Clojure function is compiled from the checked
term**. What runs is derived from what was proved.

Warrant inverts this. The developer's C# is the source of truth, it runs as
written, and Warrant proves properties of a **model** of it. Only this
direction covers the motivating example: an existing method that validates
input, reads from a database, applies more logic, and writes back, where we
want to prove the logic and assume the database behaves.

The cost is a **faithfulness gap**: a proof about the model is only as good as
the translation. Warrant addresses this in three ways:

1. **Honest models.** C# `int` is Lean `Int32` (two's-complement wrap-around),
   not mathematical `Int`. Under the faithful model, the classic false theorem
   `Increment(x) > x` fails to prove at `int.MaxValue`, instead of being
   proved about the wrong semantics. The same rule applies to null, exceptions,
   and UTF-16 strings (§6).
2. **A small, reviewable translator** with an explicit supported subset.
   Anything outside the subset is a diagnostic, never a silent approximation.
3. **Differential testing of the translation.** This is the counterpart of
   Ansatz's `check-verified!`. For each translated unit, FsCheck generates
   inputs, runs the compiled .NET method and the kernel's evaluation of the
   CIC model, and requires them to agree (§10).

---

## 3. Architecture

```text
 ┌──────────────────────── developer machine / CI ────────────────────────────┐
 │                                                                            │
 │  C# project                                                                │
 │     │                                                                      │
 │     ├──► Roslyn in the IDE (design-time builds) ──► Warrant.Analyzers      │
 │     │       extraction's own checks: unsupported constructs, malformed     │
 │     │       scripts, closed shapes; no I/O and no proof results            │
 │     │                                                                      │
 │     └──► MSBuild: Warrant.Build task (after CoreCompile)                   │
 │             │  writes Csc's arguments, runs the CLI as a child process     │
 │             ▼                                                              │
 │        warrant verify (CLI child, net10.0)                                 │
 │             │  rebuilds the CSharpCompilation from Csc's arguments         │
 │             │  Warrant.Extraction: IOperation ──► VIR units + span table   │
 │             │                                                              │
 │        JSON-RPC over a named pipe / Unix socket: canonical VIR bytes       │
 │             │   (no server: the same service runs inside the CLI)          │
 │  ┌──────────▼ warrant-server (net10.0, one per user and toolchain) ─┐      │
 │  │  Result cache (per project, obj/warrant/cache/: outcomes and     │      │
 │  │  per-unit proof certificates, keyed by closure hash)             │      │
 │  │      │ miss                                                      │      │
 │  │      ▼                                                           │      │
 │  │  Warrant.Semantics   VIR ──► CIC model and theorem statements    │      │
 │  │      ▼                                                           │      │
 │  │  Warrant.Meta / tactics   simp, omega, … ──► proof terms         │      │
 │  │                            (untrusted; theorems run in parallel) │      │
 │  │      ▼                                                           │      │
 │  │  Warrant.Kernel      type-checks every proof term   (trusted)    │      │
 │  │      ▲                                                           │      │
 │  │  the semantics bundle, loaded and checked once per server        │      │
 │  └──────────────────────────────────────────────────────────────────┘      │
 │             │  outcomes with VIR node IDs                                  │
 │             ▼                                                              │
 │   CLI: diagnostics at current lines (build errors with goals),             │
 │   assumption reports, exported NDJSON certificates ──► other kernels       │
 │   (Lean, Ansatz, arena)                                                    │
 │                                                                            │
 │  Warrant.Store (warrant import, check-store): Init, Std and Mathlib on     │
 │  disk, loaded lazily by name; the verification base from M6                │
 └────────────────────────────────────────────────────────────────────────────┘
```

### 3.1 Why a server

- **Analyzers must stay pure and fast.** They run in the IDE on every edit,
  must target `netstandard2.0`, and Roslyn's own analyzer rules (RS1035) ban
  file and network I/O in them. Loading a declaration store and running
  tactics there is the wrong fit: Ansatz needs 5–6 GB of heap for its hardest
  Mathlib declarations.
- **Large state should be loaded once.** The checked semantics bundle, the
  attribute sidecar, the simp sets and the cache's recent entries persist
  across builds. The precedent is Roslyn's own compiler server
  (`VBCSCompiler`), which the build starts on demand and reuses.
- **One engine, many clients.** The verification itself is one class,
  `VerificationService` in `Warrant.Engine`; the server hosts it, and the CLI
  hosts the same class in-process when no server can be used, so the two
  paths give byte-identical output (a parity test checks it). A later IDE
  extension or language server talks to the same server.
- The kernel and tactics can target modern .NET (net10.0: `Span`, vectorized
  hashing, `BigInteger` performance) instead of `netstandard2.0`.

### 3.2 Division of labour

| Component | Runs in | Target | Responsibility |
|---|---|---|---|
| `Warrant` (user API) | user app | netstandard2.0 | Attributes, `Spec.*`, `Prove`, `Tactic.*`. No runtime behaviour (§5). |
| `Warrant.Analyzers` | IDE (design-time builds) | netstandard2.0 | Extraction's own diagnostics as the developer types: supported subset, proof-script well-formedness, calling `[Theorem]` methods, unmodelled callees, closed shapes. One assembly that compiles in the Extraction and Vir sources. No I/O, never proof results, and removed from command-line builds, where the CLI reports each diagnostic once (M5b, [docs/m5b/06](m5b/06-analyzers.md)). |
| `Warrant.Extraction` | analyzer + CLI | netstandard2.0 | Roslyn `IOperation` tree → VIR, and the subset checks. Shared, so the analyzer and the build agree on what is supported. Compiled against Roslyn 4.8.0 so that older compilers can load it. M4 reads only the operation tree; the `ControlFlowGraph` may return for loops in M7. |
| `Warrant.Frontend` | CLI, tests | net10.0 | Builds the `CSharpCompilation` that extraction reads: references, language version, nullable analysis, overflow setting. In M4 it serves the CLI and the tests with fixed corpus settings; from M5a it takes them from the `Csc` inputs (§8.3). |
| `Warrant.Vir` | everywhere | netstandard2.0 and net10.0 | The **Verification IR**, its canonical serialization and its hashes. Its canonical bytes are what the CLI sends the server. The reader is built for net10.0 only. |
| `Warrant.Semantics` | server | net10.0 | VIR → CIC: types, definitions and theorem statements (§4.2). Trusted (§9). No Roslyn. |
| `Warrant.Engine` | server, CLI | net10.0 | The pipeline after VIR and the `VerificationService` both hosts run: admits translated declarations into a fork of the checked bundle, runs theorems in parallel, emits proofs, classifies outcomes, reads values back for messages, keeps the result cache, writes reports and NDJSON. Untrusted (§9). No Roslyn, so the server can host it unchanged. |
| `Warrant.Store` | CLI | net10.0 | Store v1: immutable, memory-mapped versions of imported Lean libraries, and the kernel's lazy constant source (§7.3). |
| `Warrant.Build` | MSBuild | netstandard2.0 | After `CoreCompile`: write Csc's arguments and run the CLI as a child process (D16), turn its records into diagnostics, delete the result cache on `Clean`. Authoritative for builds and CI. No Roslyn. |
| `warrant-server` | own process | net10.0 | Hosts the `VerificationService`: the checked bundle, the cache's recent entries, translation, tactics and kernel. Stays free of Roslyn: it only sees VIR. |
| `warrant` CLI | own process | net10.0 | The server's client and the build's child: compiles, extracts, sends VIR to the server (starting it when needed) or verifies in-process, and renders diagnostics and reports. Verbs: `check`, `stats`, `export`, `translate`, `verify`, `explain`, `server status\|cancel\|shutdown\|report`, `import`, `check-store`, `sample-store`. |

The line between client and server falls after extraction, not in the build
task as first drawn: M5a moved compiling and extracting into the CLI child,
because the task cannot load a Roslyn new enough for C# 14 (§8.3), and M5b
kept them there, so the server never loads Roslyn and each build pays one
short process start. Keeping Roslyn out of the server means the server's input
(VIR) is small, canonical, and hashable. That is what makes the cache (§8.2)
reliable.

---

## 4. The pipeline in detail

```text
C# method
  │  Roslyn: binding, overload resolution, types, nullable analysis   (free)
  ▼
IOperation tree + ControlFlowGraph
  │  Warrant.Extraction
  ▼
VIR unit   (typed, structured, explicit effects; one per method / region / theorem)
  │  Warrant.Semantics   (part of the trusted base: see §9)
  ▼
CIC definitions over the Warrant Lean library  +  goals (CIC Props)
  │  Warrant.Tactics: VC generation (mvcgen-style), simp, omega, …   (untrusted)
  ▼
Proof terms
  │  Warrant.Kernel   (trusted)
  ▼
Verdict + certificate (NDJSON) + assumption report
```

Warrant **never generates Lean source text**. Where this document says C# is
translated "to Lean" or into "Lean definitions", it means CIC terms: the core
language that Lean source is elaborated into and that the kernel checks.
Warrant builds those terms directly, as C# objects (`Warrant.Cic`), and checks
them with its own kernel. Lean the language and toolchain is needed only to
write and export the semantics library (D10), and to cross-check certificates
(§7.4). Neither is needed at verification time.

Roslyn has already resolved types, overloads, implicit conversions, operator
methods, and flow, so Warrant needs **much less elaboration than Ansatz**.
Ansatz must infer binder types and implicit arguments from untyped
s-expressions. For Warrant, translation is mostly a direct mapping. The
elaborator machinery (metavariables, unification, instance synthesis) exists
mainly to serve tactics.

### 4.1 Verification IR (VIR)

VIR is a small, language-level IR of the supported C# subset. It is not CIC.

- Expressions with C# types (`Int32`, `Boolean`, records, enums, …) as
  first-class, resolved symbols.
- Structured control flow after lowering: `if`/`switch`, early `return`,
  `throw`, loops with attached `Spec.Invariant`/`Spec.Decreases`, `await` of
  external calls.
- Explicit effects: reads and writes of locals; field reads and writes (heap
  mode only); calls, each classified as *verified*, *external* (has a
  contract) or *unsupported*.
- Specs attached as data: requires, ensures, invariants, assertions, and proof
  hints.
- Source spans for every node, so diagnostics point at C# code. They are kept in a side table keyed by node ID, outside the hash, so editing a comment does not change a unit's hash.
- Compilation facts that change semantics, for example whether
  `CheckForOverflowUnderflow` is on (it decides between wrap-around and
  `OverflowException` in unannotated code).

VIR has a canonical JSON encoding, written by hand rather than by a serializer, so the netstandard2.0 and net10.0 builds write the same bytes.
M5b's CLI sends these bytes to the server as they are; a binary encoding was not needed.

VIR grows additively.
It contains only the nodes the current milestone needs; a later milestone adds node kinds and fields but never changes the encoding of an existing one, and every unit records the VIR schema version, which is part of its hash.
Records, enums and closed types are units of their own, so each is translated once.
Every unit has two hashes: the **unit hash** of its own canonical encoding, and the **closure hash** of its unit hash followed by the closure hashes of the units it calls or mentions.
The closure hash is what the cache is keyed on (§8.2).
The M4 node set and encoding are in [docs/m4/04-vir.md](m4/04-vir.md).

### 4.2 Translation to CIC (Warrant.Semantics)

- **Pure units** (no heap writes, no external calls) become plain Lean
  definitions (CIC terms, not `.lean` source), a *shallow embedding*. `if` becomes `ite`/`dite`, locals become `let`, and direct self-recursion becomes well-founded
  recursion with a `Spec.Decreases` measure: `WellFounded.Nat.fix` over the
  measure clamped to `Nat`, with a decrease theorem per recursive call and a
  generated equation lemma ([docs/m5a/03](m5a/03-statements-and-recursion.md)).
  Structural recursion is not built: no M5a type can recurse structurally
  (`Int32` has no `brecOn`, and records and closed types cannot be recursive),
  so it waits for recursive types. A `switch` over a `[Closed]` enum becomes the type's recursor
  with a constant motive, and a `switch` over an integer or open enum becomes a
  chain of `ite` tests; translation generates no Lean-style named matchers. In
  M4, statements are translated in continuation-passing style, and fall-through
  shared by two branches becomes a `let`-bound join point, so a translated
  method stays linear in the size of its source ([docs/m4/05-translation.md](m4/05-translation.md)).
- **Effectful units** become programs in a Warrant monad defined in the Lean
  library (§6.2), with state for the heap, `Except` for exceptions, and
  external calls as specified operations. Their contracts become Hoare triples
  in the style of Lean's `Std.Do` framework.
- **Theorems** (`[Theorem]` methods) become CIC propositions universally
  quantified over the method's parameters.

The translator is deliberately simple and syntax-directed. Cleverness belongs
in the untrusted tactics.

---

## 5. The C# surface

> All code in this section is **target syntax for discussion**, not a settled API.

Everything is valid C#. Spec methods that return `void` are marked
`[Conditional("WARRANT_CONTRACTS")]`, so the compiler drops the calls from
emitted IL by default. They remain fully bound in Roslyn's semantic model and
`IOperation` tree, which is all Warrant needs. C# allows `[Conditional]` only
on `void` methods, so value-returning calls such as `Spec.Implies` and
`Prove.That` stay in the IL: `Spec.Implies` computes the implication and
`Prove.That` throws. In M4 both are valid only in theorem statements (WRT0004);
from M6, `Spec.Implies` is also valid inside `Spec.Requires` and `Spec.Ensures`
(#213).

C# attribute arguments must be compile-time constants, so
`[Ensures(r => r > 0)]` is impossible. String specs would be untyped. Warrant
therefore puts specs in **method-body calls** (the Code Contracts tradition)
and in **companion contract classes** for interfaces and external code.

### 5.1 Pure functions and theorems

```csharp
[Verified]
public static PaymentResult Validate(Payment p)
{
    if (p.Amount <= 0) return PaymentResult.InvalidAmount;
    if (p.Status != PaymentStatus.Pending) return PaymentResult.InvalidStatus;
    return PaymentResult.Valid;
}

[Theorem]
static Proof ValidImpliesPositive(Payment p) =>
    Prove.That(Spec.Implies(Validate(p) == PaymentResult.Valid, p.Amount > 0))
         .By(Tactic.Unfold(nameof(Validate)), Tactic.Simp());
```

- In a statement position, a `bool` expression is read as a proposition:
  `&&` → `∧`, `||` → `∨`, `!` → `¬`, and `==` on integers, `bool` and open
  enums → `Eq`. `==` on a record is `R.$eq r s = true`, where `$eq` is a
  generated field-by-field comparison, because C# `==` on a record is whatever
  the generated `Equals` computes. `==` on a closed type compares generated
  `$index` values. Neither uses `DecidableEq`.
  This avoids ChatGPT's suggested `Prop` type with overloaded operators and
  `Eq(a, b)` helpers. Roslyn has already bound the C# operators; the
  translator reinterprets them.
- `Spec.ForAll<T>(x => …)`, `Spec.Exists<T>(x => …)` and `Spec.Implies(a, b)`
  provide quantifiers and implication.
- Proof scripts are C# expressions: `Tactic.Simp(...)`, `Tactic.Omega()`,
  `Tactic.Induction(x)`, `Tactic.AllGoals(t)`, `Tactic.Try(t)`. Lemmas are
  referenced with `nameof(...)` for C# theorems and with `Lean.Const("Nat.add_comm")`
  for imported ones. Strongly typed handles (`Mathlib.Nat.AddComm`), produced by
  a source generator from a store catalogue, come later.
- `[Theorem]` methods are never executed. The analyzer reports any call to one.

### 5.2 Contracts and external dependencies

```csharp
public sealed record Payment(int Id, decimal Amount, PaymentStatus Status);

public interface IPaymentStore
{
    Task<Payment?> GetPayment(int id);
    Task SavePayment(Payment p);
}

// Assumed behaviour of the external dependency. Nothing here is verified;
// everything here is reported as an assumption.
[ContractFor(typeof(IPaymentStore))]
file abstract class PaymentStoreContract : IPaymentStore
{
    public Task<Payment?> GetPayment(int id)
    {
        Spec.Ensures<Payment?>(r => r is null || r.Id == id);
        return default!;
    }

    public Task SavePayment(Payment p) => default!;   // no guarantees assumed
}

[Verified]
public async Task<Result> ProcessPayment(int paymentId)
{
    Spec.Ensures<Result>(r => r != Result.Success || paymentId > 0);

    if (paymentId <= 0) return Result.InvalidId;

    var payment = await store.GetPayment(paymentId);
    if (payment is null) return Result.NotFound;

    if (Validate(payment) != PaymentResult.Valid) return Result.Invalid;

    await store.SavePayment(payment with { Status = PaymentStatus.Processed });
    return Result.Success;
}
```

Contracts are discharged automatically by a default tactic pipeline
(VC generation, then `simp`, then `omega`, later `grind`), as Dafny does. When
that fails, `Spec.Assert(cond, Tactic...)` and companion `[ProofFor(nameof(M))]`
methods supply hints.

A contract is total about implicit exceptions (overflow, a zero divisor, a
null read) and allows an explicit `throw` and an exception from a dependency,
which the assumption report lists. `Spec.NoThrow()`, after the `Spec.Requires`,
opts a method into proving that none of its explicit throws is reachable under
its `Requires`, so a reachable one fails the build at the `throw`; a dependency's
exception is still allowed (decided in M6, #182;
[docs/m6/06](m6/06-contract-obligations.md)).

### 5.3 Verified regions (later)

A region is a block inside an unverified method that is treated as an
anonymous verified unit. Its inputs are the variables live on entry, and its
outputs are the variables live on exit plus every exit path (fall-through,
`return`, `throw`). The syntax is open (§12). The ChatGPT draft also showed
the main pitfall: a postcondition that holds only on the fall-through path. A
region's contract must say what holds on each exit, and the verifier must
reject contracts that ignore early exits.

The M7 target is the payment example as it is commonly written, without
restructuring into records: a mutable class, a loop with an invariant, and a
region with an early return. The region syntax below is a placeholder (§12 Q4).

```csharp
public sealed class Payment
{
    public int Id { get; init; }
    public decimal Amount { get; set; }
    public PaymentStatus Status { get; set; }
}

public void PayInInstallments(Payment p, int count, decimal installment)   // not verified
{
    using (Verify.Region(ensures: () => p.Amount >= 0))
    {
        for (int i = 0; i < count; i++)
        {
            Spec.Invariant(p.Amount >= 0);
            Spec.Decreases(count - i);
            if (p.Amount < installment) return;   // early exit: the contract must cover it
            p.Amount -= installment;
        }
    }
    p.Status = PaymentStatus.Processed;
}
```

---

## 6. Semantics: modelling C# honestly

### 6.1 Type mapping

| C# | Lean model | Notes |
|---|---|---|
| `bool` | `Bool` (Prop in statement positions) | |
| `sbyte` `short` `int` `long` | `Int8` `Int16` `Int32` `Int64` | Core Lean types (`Init/Data/SInt`), two's complement. Wrap-around in `unchecked` code. One rule for overflow wherever Warrant proves something (owner decision 2026-11-12): `+ - *` and unary `-` on `int` and `long` in C#'s default context must not overflow, and a possible overflow fails the proof at the operation; built for `Spec.Requires`/`Spec.Ensures` (GitHub #183), theorem statements (#236), `Spec.Assert` conditions (#235) and verified method bodies (#244), where the value stays the wrapped one and the proof shows the wrap never happens ([docs/m6/06](m6/06-contract-obligations.md)). Explicit `unchecked(...)` or `unchecked { }` wraps on purpose with no obligation; `checked` raises. Casts and `decimal` are unaffected. |
| `byte` `ushort` `uint` `ulong` | `UInt8` … `UInt64` | |
| `checked(...)` arithmetic | a `ClrM` program that raises `ClrExn.overflow` | Also the default when the project enables `CheckForOverflowUnderflow`. Checked `+ - *`, unary `-` and narrowing on `int` and `long` (M6, [docs/m6/02](m6/02-effect-monad-and-models.md)). |
| `/` and `%` on `int` and `long` | `Warrant.Int32.div`/`rem` (and `Int64`) in `ClrM`: `divideByZero`, then `overflow` for `MinValue / -1` and `MinValue % -1`, then Lean's truncating operation | M6. By a literal other than 0 and -1 they cannot throw and stay pure. |
| `Math.Min`, `Math.Max`, `Math.Abs` on `int`, `long`, `decimal` | Warrant library definitions; `Abs` on `int` and `long` raises `overflow` for `MinValue` | M6 (KTD23 of the M6 plan). Other BCL members are not modelled. |
| `System.Numerics.BigInteger` | `Int` | Not built (GitHub #160). Specs keep `int` and `long`, and their arithmetic must not overflow (GitHub #183, docs/m6/06). |
| `Warrant.Nat` / `Warrant.Integer` | `Nat` / `Int` | Runtime structs for code written mathematically. Not built. |
| `decimal` | `Warrant.Decimal`: sign, 96-bit mantissa, scale 0 to 28 | M6 ([docs/m6/03](m6/03-decimal.md)): literals, comparisons and `==` by value (`1.0m == 1.00m`), `+` and `-` (raising `overflow` in every context), unary `-`. `*`, `/`, `%` and rounding: M7 (§12 Q1). |
| `float` `double` | not supported | Lean's `Float` is opaque to the kernel. |
| `string` `char` | Warrant model over UTF-16 code units | Lean's `String` is a sequence of Unicode scalar values, so `Length` would differ for surrogate pairs. |
| `T?` (reference, nullable) / `Nullable<T>` | `Option T` | M6 for `int?`, `long?`, `bool?`, `decimal?` and nullable references to records and closed classes. `Value` raises `invalidOperation` on null; a `T?` used where a `T` is required is a checked unwrap that raises `nullReference`. Non-nullable reference annotations are assumptions, listed in the report, not facts (§12 Q11). Lifted arithmetic and comparisons are rejected. |
| `record` / `readonly record struct` | single-constructor `inductive`, read by primitive projection | `with` becomes a constructor application. `==` is a generated field-by-field `$eq : R → R → Bool`, not `DecidableEq`, so it can follow the generated `Equals` where that differs from structural equality: a `decimal` field compares by value (M6). A nullable field does not translate yet (GitHub #218). M4 accepts sealed positional record classes with compiler-generated equality and no other instance state. |
| `enum` | underlying integer + named constants | C# enums are open (any value can be cast), so they aren't modelled as closed inductive types unless marked `[Closed]` (D12). An open enum is an `abbrev` of its underlying type. A `[Closed]` enum is an `inductive` with one constructor per member; its members must have distinct values. |
| `[Closed]` sealed class with static instances | `inductive` with one constructor per instance | The "smart enum" pattern, recognised by shape (D13). `==` compares a generated `$index`, the constructor's position. Instances may be get-only auto-properties or `static readonly` fields. |
| Generics | universe-polymorphic parameters | Constraints become type-class instances later. |
| `IReadOnlyList<T>`, `ImmutableArray<T>` | `List T` / `Array T` models | |
| Exceptions | the `ClrExn` branch of `ClrM σ α := ExceptT ClrExn (StateM σ) α` | M6: `overflow`, `divideByZero`, `nullReference`, `invalidOperation`, `assertFailed`, `thrown` (an explicit `throw new T(...)`, by `T`'s key) and `external` (from a dependency). `try`/`catch` is not modelled and is rejected. |
| An interface with a `[ContractFor]` class, through a `readonly` field or a never-assigned primary-constructor parameter | one operation `args → ClrM σ R` per member called, a parameter of the obligation, with the member's contract as a hypothesis (§6.3) | M6. The world `σ` is opaque, so two calls are related only by their contracts. Other field access: M7. |
| Mutable classes and fields | heap model (§6.2) | Not in the first effectful milestone. |
| `async`/`await` | sequencing in the monad: `Task<T>`, `ValueTask<T>` to `ClrM σ T`; `Task`, `ValueTask`, `void` to `ClrM σ Unit` | M6, only when awaiting external or verified calls, with every task-returning call the direct operand of `await`. A `CancellationToken` parameter is not accepted yet (GitHub #215). |

### 6.2 The Warrant Lean library (D10)

The semantic model is **written in Lean 4 and proved in Lean 4**, in
`lean/Warrant/` inside this repository:

- models for C# numeric operations, conversions, `decimal`, UTF-16 strings,
  `Option` and `Except` helpers
- the effect monad: heap, exceptions, and a trace of external calls
- Hoare-triple / weakest-precondition rules for that monad, building on
  Lean's `Std.Do` framework (the library behind the `mvcgen` tactic)
- lemmas the tactics need (for example, bridging `Int32` facts to `Int` with
  range side conditions so `omega` can work, as Lean's `bv_omega` does)

It is built with the real Lean toolchain at **development time**, exported with
lean4export, and shipped as an NDJSON bundle alongside Init. At verification
time no Lean is needed. Because the lemmas are proved in Lean and re-checked by
our kernel, only the *definitions* (the claim that "this models C#") are
trusted. The proofs are not.

### 6.3 External calls are hypotheses, not axioms (D9)

A contract for `GetPayment` is **not** added as a global axiom. Axioms can make
the environment inconsistent, and they leak into every proof. Instead, the
theorem generated for `ProcessPayment` is parameterized over every external
operation it calls:

```text
∀ (getPayment : Int32 → M (Option Payment)) (savePayment : Payment → M Unit),
  (∀ id, ⦃⊤⦄ getPayment id ⦃r, r = none ∨ r.id = id⦄) →
  ⦃⊤⦄ processPayment getPayment savePayment paymentId ⦃r, r ≠ .success ∨ paymentId > 0⦄
```

That is: *for every implementation of the store that satisfies its contract,
`ProcessPayment` satisfies its contract.* The assumption report (§8.4) is a
rendering of these hypotheses plus the global trust assumptions.

---

## 7. Kernel, store, import and export

### 7.1 Warrant.Kernel

The kernel is a port of the Lean 4 kernel, using Ansatz's Java kernel as a
second reference. Ansatz's version is about 11k lines: `TypeChecker` 3.2k,
`Reducer` 1.9k, `Level` 620, and about 2.5k for inductive types, recursors and
nested inductives.

- **Expressions:** 12 kinds, `BVar`, `FVar`, `Sort`, `Const`, `App`, `Lam`,
  `Forall`, `Let`, `NatLit`, `StrLit`, `MData`, `Proj`, that the kernel
  accepts. (ChatGPT's list wrongly included `MVar` and omitted `Proj`.) Since
  M5a the shared `Warrant.Cic.Expr` also has a 13th kind, `MVar`, and levels a
  `Level.MVar`, for `Warrant.Meta`; the kernel never accepts either (below).
- Each expression caches its hash and flags at construction (loose bound
  variable range, has free variables, has universe parameters), as Lean does.
  Hash-consing is optional, and caches use reference equality.
- Universe levels: `Zero`, `Succ`, `Max`, `IMax`, `Param`, with Lean's
  normalization and `leq`.
- Supported features:
  - type inference
  - weak-head normalization
  - definitional equality with lazy delta reduction and reducibility hints
  - proof irrelevance
  - eta for functions and structures, and unit-like eta
  - quotients
  - inductive admission (bundles, recursor generation, nested inductive types)
  - Nat literal acceleration using `BigInteger` for the kernel's built-in `Nat`
    operations
  - String literal expansion
- **Fuel and cancellation.** The Lean kernel has no fuel limit; Ansatz adds
  one, and so do we. Running out of fuel means rejection, never acceptance.
  The default is about 20M steps for interactive use and 100M for corpus
  verification. Since M5a an optional wall-clock deadline, checked every
  1,024 steps, rejects the same way.
- **Tracing** in the same NDJSON format as Ansatz's `checkConstantTraced`
  (`{s, d, l, r, res, by}`), so that definitional-equality traces can be
  diffed against Ansatz and Ansatz's instrumented Lean kernel.
- The kernel depends only on `Warrant.Cic`: no I/O, no Roslyn, no store.
- Status and the exact list of deliberate differences from Lean: [kernel.md](kernel.md).
- **Metavariables** (decided in M5a): `Warrant.Meta` adds its holes to the
  shared `Warrant.Cic.Expr` and `Level`, as Lean does, rather than keeping its
  own representation, so substitution and traversal are not duplicated. Every
  term caches `HasExprMVar` and `HasLevelMVar`, and the kernel rejects a
  declaration whose type or value has an expression or universe metavariable
  before it type-checks anything ("declaration has metavariables"), as Lean's
  C++ kernel does; the type checker also throws on one. Ansatz's kernel misses
  universe metavariables; Warrant's tests cover that case
  ([docs/m5a/02](m5a/02-metavariables-and-meta.md)).

### 7.2 Import (lean4export NDJSON)

- lean4export format 3.x. Each line defines an indexed name (`in`), level
  (`il`) or expression (`ie`), and declarations refer to those indices. It is
  read with a streaming `System.Text.Json` reader.
- Two modes:
  - **Trusted import:** accept declarations that Lean already checked. This is
    fast, and suitable for development.
  - **Verified import:** re-check every declaration with our kernel. The
    semantics bundle is always loaded this way: `warrant verify` checks it on
    every in-process run, and the server once when it starts. It is also the
    main kernel test.
  Both modes are `warrant import`'s, which writes a store (§7.3): `--verified`
  stores what the kernel admitted, and the default stores the declarations as
  read.
- The bundle shipped with Warrant is `warrant-semantics`
  (`tests/data/warrant-semantics.ndjson.gz`): the Warrant semantics library and
  every Init constant the translator emits, with their whole dependency closure
  (4,109 constants at Lean 4.35.0 with M6's `Std.Do`, division, effect-core, nullable, `Math`, `decimal`, monadic-translation and VC-walker roots; 2,835 in M5b), exported by `scripts/export-semantics.sh`.
  The kernel and corpus tests also use Ansatz's `init-medium` subset of Lean
  4.33.1's Init (5,118 constants in 4,631 declaration records, 3.3 MB gzipped),
  but it is not shipped: it has no `Int32` or `Int64`.
  Mathlib (712,205 declarations at v4.35.0) is optional and downloaded.

### 7.3 Store

Built in M5b as store v1 ([docs/m5b/05](m5b/05-store.md)), laid out against
the Mathlib run's figure: 12.6 GB peak with every constant in memory. We don't
port Ansatz's datahike/konserve store. Instead, a versioned on-disk binary
format in `Warrant.Store`:

- A store is a directory of immutable version directories (`v1-<hash12>/`)
  and a `current` file naming the active one. `warrant import` writes a new
  version and replaces `current` atomically; readers keep the version they
  opened, so a store is never rewritten in place (Windows will not overwrite a
  mapped file).
- Each version holds `decls.bin`, one self-contained record per declaration
  (its own name, level and expression tables), stored once per content hash
  and read by offset; `names.idx`, a sorted name index that is memory-mapped
  for lazy loading; and `manifest.json`, which records the format, the Lean
  and lean4export versions, each source file's SHA-256 (the bundle's among
  them, so the attribute sidecar's binding holds), the import mode, the
  toolchain identity that verified it, whether quotients are initialized, and
  the counts. Every file starts with a magic number, a format version and its
  length, checked before anything is read.
- The kernel reads it through `IConstantSource` (look up a constant by name,
  a count, the quotient flag), which `KernelEnvironment.Find` consults after
  its own constants. The store's adapter materializes a constant the first
  time it is asked for. The kernel sets the quotient flag only when the source
  holds the quotient constants exactly as `Quotient.ExpectedConstants`
  defines them.
- `warrant import <files>... --store <dir> [--verified]` and
  `warrant check-store <dir>` write and re-check it. The Init + semantics
  store (57,944 declarations, 59,374 constants) passes `check-store`.

In M5b the verification environment stays the shipped bundle, loaded and
checked when the server starts; the store serves the CLI verbs and the
lazy-loading tests. When a store becomes the verification base (M6, for Std),
its record decoder becomes trusted code and joins the toolchain identity.
Measured on Mathlib (§11): a trusted import of all 712,205 declarations takes
139 s and makes a 1.45 GB store; opening it and looking up 1,000 random
constants leaves a 21 MB managed heap and an 88 MB working set.

### 7.4 Export (D6)

Verified declarations, including our generated models, statements and proof
terms, together with the closure of their dependencies, are written back out
as **lean4export NDJSON**. Any kernel that reads the format can then
re-check our exact terms: Lean's own kernel, Ansatz, and the other kernels in
the Lean kernel arena. Exporting `.lean` source would make Lean re-elaborate,
which tests a round trip rather than our kernel's verdicts. A human-readable
Lean rendering is still useful, but as a separate debugging feature.

---

## 8. The verification server

### 8.1 Process and protocol

Built in M5b ([docs/m5b/01](m5b/01-server-and-protocol.md)).

- `warrant-server` is a net10.0 process, one per user, elevation and
  toolchain. The `warrant` CLI child that the build runs starts it on demand,
  detached so that a cancelled build cannot kill it, from a per-user copy of
  its files, so it never locks the package folder or a repository's `bin/`. It
  loads and checks the semantics bundle before it serves, and exits 10 minutes
  after its last connection closes and no work runs.
- Transport: JSON-RPC (StreamJsonRpc, System.Text.Json) over a named pipe
  opened with `CurrentUserOnly` on Windows, or a Unix domain socket in a 0700
  per-user directory elsewhere. The endpoint's name hashes the user, the
  elevation, the server's directory and the toolchain identity, so a rebuilt
  or upgraded Warrant gets its own server. The protocol is versioned: a client
  with another version makes the server drain and exit, and the next client
  starts a matching one.
- Methods: `hello(protocol)`, `verify(request)`, `cancel(id)`, `status()`,
  `explain(request)` (one unit's tactic trace, with the goals before and after
  each step), `export(request)` (the certificate file), `report(project)` (the
  JSON assumption report of the project's last verify) and `shutdown()`.
  `warrant server status | cancel | shutdown | report` drive them.
- Scheduling: a request's theorems run in parallel on a pool of
  `min(processors − 1, 8)` large-stack workers, each in its own fork of the
  frozen environment; every unit has its fuel and wall-clock budget, timed
  from when a worker starts it. A request is cancelled by `cancel(id)`, by
  `$/cancelRequest` or by its client disconnecting, and the cancellation
  reaches the kernel and Meta, which poll it every 1,024 steps. A request
  carries a priority, so that IDE requests can take priority over builds; it
  is unused until an IDE client exists.
- When the server cannot be started, reached or trusted, or fails a request,
  the CLI verifies in-process with the same service and logs the reason as a
  message, not a warning. CI builds (`ContinuousIntegrationBuild=true`) do not
  use the server by default (`WarrantUseServer=false`).
- The server isolates users, not elevation levels: an elevated build's server
  runs from a copy that the same user's non-elevated processes can write to.
  On a machine where non-elevated code is not trusted, build elevated with
  `WarrantUseServer=false` and `WarrantRecheck=true` (or `WarrantUseCache=false`),
  since the cache under `obj/` is just as writable; Warrant itself loads from
  the user's NuGet package folder, so full separation also needs a package
  folder non-elevated code cannot write (GitHub issue #43).

### 8.2 Content-addressed cache

Built in M5b ([docs/m5b/04](m5b/04-cache-and-recheck.md)).

- **Key:** a SHA-256 over the cache format version, the **toolchain
  identity** (a hash of the module version IDs of Warrant's verification
  assemblies, so any change to their code invalidates every entry), the
  semantics bundle's and the attribute sidecar's SHA-256, the unit's closure
  hash (§4.1), and the display names of the units in its closure. The closure
  hash covers the unit's own canonical VIR, its compilation facts, and the
  closure hashes of every unit it calls or mentions. Hashing only the
  *statements* of dependencies is not enough under a shallow embedding: a
  theorem proved by computation depends on its callees' bodies, so editing a
  callee's body can turn a proved theorem false without changing the
  theorem's text. Budgets are not in the key: a proved entry hits when the
  current budgets are at least what its proof used, and an outcome that
  depends on the budgets (false, not proved, out of fuel) hits only with the
  same budgets.
- **Value:** one JSON file per entry: the outcome with the unit's
  assumptions, the budgets, the unit's **proof certificate** (the lean4export
  NDJSON of the declarations it admitted) and a SHA-256 of the body. Outcomes
  refer to VIR node IDs, not source positions; the CLI maps them to spans
  through the span table of the current extraction, so a cached result never
  points at stale lines. Proved, false, not-proved and out-of-fuel outcomes of
  theorems and recursive definitions are cached; time-outs, internal errors and
  cancellations are not.
- Stored on disk per project, in `$(WarrantCacheDir)` (by default
  `$(BaseIntermediateOutputPath)warrant/cache/`, which `dotnet clean`
  deletes), with the 4,096 most recent entries in the server's memory. A
  per-user cache shared across projects is deferred.
- **Trust (D17):** a hit is trusted locally and runs nothing for its unit.
  A unit that misses has its closure admitted from cached terms, each checked
  by the kernel as it is admitted, so only the misses run tactics.
- **Proof replay:** with `WarrantRecheck=true` (`--recheck`), every cached
  proof is checked by the kernel against a theorem statement that
  `Warrant.Semantics` builds afresh from today's VIR, without running tactics.
  A rejected certificate is WRT0010 and its entry is deleted. CI can run with
  it and then trusts only the kernel, not the cache contents.

### 8.3 Build integration

`Warrant.Build` runs after `CoreCompile`. It sets `ProvideCommandLineArgs`, so
Csc reports its full argument list, writes the list to
`obj/…/warrant.csc.args`, and runs `warrant verify --csc-args` as a child
process. The CLI, not the task, recreates the `CSharpCompilation` from the
same inputs Csc received (sources, references, defines, `LangVersion`,
overflow-checking setting) with Roslyn's `CSharpCommandLineParser`, extracts
VIR and proves (D16). This changed in M5a for two reasons: extraction is
built against Roslyn 4.8, which cannot parse the C# 14 that SDK 10 defaults
to, and loading Roslyn into Visual Studio's .NET Framework MSBuild depends on
fragile assembly binding. The task is a netstandard2.0 `ToolTask` with no
Roslyn reference. Generated sources are not in Csc's arguments, so the CLI
runs the project's source generators itself; a generator that cannot load or
throws is error WRT0012 ([docs/m5a/07](m5a/07-verify-and-build.md)).

M5b keeps the child process and makes it the server's client
([docs/m5b/02](m5b/02-client-and-build.md)): after extracting, it sends the
units' VIR to the server (starting it when needed), or verifies in-process
when the server cannot be used, and it renders the outcomes itself, because
only it has the compilation and the source text. The targets add three
properties and pass them to the CLI:

| Property | Default | Effect |
|---|---|---|
| `WarrantUseServer` | `true`; `false` when `ContinuousIntegrationBuild` is `true` | `--server auto`, or `--server off` to always verify in-process. |
| `WarrantRecheck` | `false` | `--recheck`: the kernel re-checks every cached proof (§8.2). |
| `WarrantCacheDir` | `$(BaseIntermediateOutputPath)warrant/cache/` | `--cache-dir`; `dotnet clean` deletes it. `WarrantUseCache=false` verifies without a cache. |

The summary line says how many results came from the cache and, when the
server was asked for, which path was taken:
`Warrant: 20 verified units, 7 theorems proved (10 from cache), 0 not proved. [server]`.
The target still has no `Inputs` and `Outputs`: every build runs the CLI,
and the cache decides what is re-run. The task emits errors such as this one
from M5a:

```text
Increments.cs(13,52,13,66): error WRT0001: Theorem 'Increments.AlwaysLarger(int)' could not be proved: omega could not prove the goal. Counterexample: x = 2147483647.
```

followed by `omega`'s constraints and the goal. With contracts (M6) they will
look like this:

```text
Payments.cs(42,5): error WRT0001: Postcondition of 'ProcessPayment' could not be verified.
  Path: paymentId > 0, GetPayment returned some p, Validate(p) = Valid
  Unsolved goal:
    ⊢ r ≠ Result.Success ∨ paymentId > 0
```

The task is **authoritative**: if required proofs fail, the build fails. Live
IDE feedback through a language server or an editor extension is a later
milestone (§11, §12). The analyzer never reports verification results, because
that would require I/O and break its determinism.

### 8.4 Assumption report

The report is produced for every verified unit, as Markdown and JSON alongside
the build output:

```text
ProcessPayment            VERIFIED   (kernel: Warrant 0.1, cert 3f9a…)
  Assumed (contracts):
    - IPaymentStore.GetPayment returns null or a payment with the requested Id
  Assumed (global):
    - No concurrent modification between GetPayment and SavePayment
    - Non-nullable reference annotations on Payment hold
    - Semantics bundle warrant-semantics 0.1 models C# 12 faithfully
  Proved:
    - Result.Success implies paymentId > 0
```

---

## 9. Trusted computing base

The trusted base is drawn by assembly.

| Trusted | Why | Mitigation |
|---|---|---|
| `Warrant.Kernel` | Accepts or rejects proof terms. | Arena negatives, init/Mathlib corpus, cross-kernel export, property tests, trace diffs (§10). |
| `Warrant.Semantics` (VIR → CIC) | The faithfulness gap. It builds every declaration whole, including each theorem's name and *statement*, because a wrong statement proves the wrong claim. | Small and syntax-directed; differential testing against compiled .NET, and CLR-agreement tests for every operation it emits. |
| `Warrant.Extraction` (C# → VIR) | Same gap, one layer earlier. | Same differential tests, end to end. |
| `Warrant.Frontend`'s compilation options | They decide what the C# means (language version, references, overflow checking). | The build task takes them from `Csc`'s own inputs (§8.3). |
| A referenced project's source record (#32) | A `[Closed]` class from that project is checked from the source the record names. | The record's file hashes are checked again before use, and every unit using the class lists the `referenced-source` assumption ([docs/m5a/07](m5a/07-verify-and-build.md#types-from-referenced-projects)). |
| `Warrant.Vir` (model, writer and reader) | Translation sees only what VIR carries. | Round-trip, golden-file and cross-framework encoding tests. |
| Semantic-model *definitions* in `lean/Warrant`, and the Init definitions it reuses | The claim that "this models C#". | Reviewed; tested against .NET behaviour (for example exhaustively for 8- and 16-bit types, sampled for 32/64-bit). |
| Declared contracts and global assumptions | By design. | Listed in every assumption report. |
| Trusted-mode imports | Lean already checked them. | Verified import mode removes this. |

**Not trusted:** `Warrant.Engine` (proof emission, outcome classification,
read-back of values for messages, reports and NDJSON export), the elaborator,
tactics, VC generation (D11), the server, the cache (with recheck), the
importer in verified mode, and the Roslyn analyzer. The engine fills only the
proof slot of a declaration that `Warrant.Semantics` built, and a theorem
counts as proved only when the kernel admits that exact declaration, so a bug
in the engine can make a true claim fail but never a false one pass.

---

## 10. Assurance and testing strategy

1. **Kernel corpus.** In order: `Nat.add_succ.ndjson` → arena cases
   (positive, and negative such as `002_badDef`, `141_falseFromUnsafe`) →
   init-medium (5,118 constants) → full Init (57,919 declarations, 59,349 constants at Lean 4.35.0) → Mathlib (712,205 declarations, 729,263 constants at v4.35.0,
   all accepted by Warrant in 26 minutes; Ansatz checks 707,508 at v4.33.1 in
   about 80 minutes on 4 workers). Every discrepancy
   becomes a regression test.
2. **Cross-kernel harness.** Export our certificates (§7.4) and check them
   with Lean's kernel, Ansatz and arena kernels. Compare verdicts on a shared
   corpus.
3. **Property-based kernel tests (FsCheck).** Substitution and instantiation
   preserve typing; definitional equality is reflexive, symmetric and
   transitive on generated terms; normalization preserves types;
   alpha-equivalent terms behave identically; universe instantiation preserves
   well-formedness.
4. **Trace diffing** against Ansatz and Ansatz's instrumented Lean kernel when
   a declaration times out or diverges.
5. **Translation differential testing.** For each translated pure unit, compare
   generated inputs → compiled .NET result against kernel evaluation of the
   CIC model. Effectful units are tested the same way, with mocked externals
   that satisfy their contracts.
6. **Semantics-library tests.** Lean-side proofs, plus .NET-side checks that
   every modelled operation agrees with the CLR.

---

## 11. Milestones

| # | Milestone | Exit criterion |
|---|---|---|
| M0 | Repository, license, design doc, history | This document merged. ✅ |
| M1 | `Warrant.Cic` (Name, Level, Expr, ConstantInfo, Env), the NDJSON reader (formats 3.0.0 and 3.1.0) and writer (3.1.0) | `Nat.add_succ`, init-medium and the arena files import; import → export → import yields identical constants; export is idempotent. ✅ |
| M2 | `Warrant.Kernel` | All 5,118 init-medium constants pass; arena negatives are rejected; then full Init. ✅ full Init (57,977 declarations), init-medium and arena (see [kernel.md](kernel.md)) |
| M3 | Exporter, cross-kernel harness, FsCheck property tests | Certificates check in at least one external kernel. Mathlib is a stretch goal. ✅ Lean's kernel re-checks everything Warrant admits, including full Init and C#-built types (see [kernel.md](kernel.md)); the store moved to M5b |
| M4 | VIR, extraction of the pure subset (`int`/`long`/`bool`, enums, records, `if`/`switch`; theorems are parameterless `[Theorem]` methods returning `Prove.That(bool)`; recursion is rejected until M5a, and `/`, `%` and checked arithmetic are rejected with a diagnostic until M6, and non-null record parameters are recorded as assumptions), semantics library v0 with CLR-agreement tests (§10.6), translation, differential testing | A fixed corpus (`tests/corpus/m4/`) translates, including a `Validate`-shaped method over records and enums (`int` in place of `decimal`), and every rejected construct has a corpus method that is rejected with the diagnostic. Differential tests pass; null-record inputs check that .NET throws and that the non-null assumption is recorded. CLR-agreement tests pass for every modelled operation. Theorems without free parameters are closed by `rfl`/`decide` proof terms the translator emits. The translated corpus, exported with its Init + semantics closure, passes a new translated-output step in `scripts/cross-check.sh`. |
| M5a | `Warrant.Meta` and tactics v1 (`intro`, `exact`, `apply`, `cases`, `induction`, `unfold`, `simp`, `omega`, `all_goals`, `try`), quantified theorems and `Prove.That(...).By(...)`, well-founded recursion with `Spec.Decreases` (structural recursion is unreachable for M5a's types, §4.2), translator-generated equation lemmas for recursive definitions, a development-time export of simp, instance and reducibility attributes for Init and the semantics library next to the NDJSON bundle (untrusted tactic input; Std is added in M6), `Int32`/`Int64` → `Int` bridging lemmas and an omega-prep simp set (§6.2), in-process `warrant verify` (§3.2), a thin MSBuild task that runs `warrant verify` as a child process (the net10.0 engine cannot load in .NET Framework MSBuild) | First end-to-end result: `Increment(x) > x` fails the build with its goal and the counterexample `x = 2147483647` shown under `dotnet build`, Visual Studio 2026's MSBuild and Visual Studio 2022's MSBuild; `ValidImpliesPositive` (`int`) passes with `Unfold` then `Simp`; a well-founded method whose decrease needs `omega`, and a quantified theorem over a translated `int` method closed by `simp` then `omega`, pass. Differential tests pass for a well-founded unit, both by kernel evaluation and by rewriting with its equation lemma. The certificate of a verified C# theorem passes the translated-output step of `scripts/cross-check.sh`. ✅ as described in [docs/m5a/](m5a/README.md); how Visual Studio's Error List shows a multi-line goal is still to be checked by hand |
| M5b | Server, content-addressed cache, store v1 (trusted and verified import), CLI verbs, analyzers | The M5a result through the server. A second build is served from the cache without running tactics, `WarrantRecheck=true` re-checks cached certificates with the kernel alone, and the Init + semantics store passes `warrant check-store` in verified mode. `cancel` aborts a running verify, a unit over its fuel or wall-clock budget reports a timeout, and analyzer output is identical across runs. Baseline per-unit verification latency and server memory are recorded for M9. Store v1 is laid out against the Mathlib run's figure: 12.6 GB peak with every constant in memory. ✅ as described in [docs/m5b/](m5b/README.md): each item is a test in `M5bExitTests` (9 of 9 pass, the Init + semantics store with `WARRANT_INIT_EXPORT`; analyzer determinism is `Warrant.Analyzers.Tests`' 20 concurrent runs), and the build matrix (`dotnet build`, Visual Studio 2026's and 2022's MSBuild) adds a second build from the cache, a recheck build and `dotnet clean`. Baselines on a 32-core Windows 11 workstation (.NET SDK 10.0.403, 2026-11-07; [docs/m5b/08](m5b/08-testing-and-baselines.md#baselines-for-m9)), for the M5a accepted sample's 20 units: starting the server, which loads and checks the bundle, and connecting take 2.9 s; a warm request 630 ms (46 ms per unit on average, 176 ms at most); a second request served from the cache 39 ms; a recheck 239 ms; in-process, the request takes 548 ms of a 4.4 s run that also loads the bundle. The server holds a 37 MB managed heap (110 MB working set) after start and 65 MB (150 MB) after the corpus. A trusted Mathlib store imports in 139 s into 1.45 GB, opens in 69 ms and serves 1,000 random lookups in 114 ms with a 21 MB managed heap and an 88 MB working set. |
| M6 | Contracts: `Spec.Requires`/`Ensures`, contract classes, effect monad (exceptions, null, overflow, `/` and `%`), VC generation with `@[spec]` lemmas in the attribute sidecar, assumption reports, a minimal `decimal` model (96-bit mantissa and scale, comparisons, add/subtract without overflow; `==` is numeric equality, so `1.0m == 1.00m`, also inside records). Readonly fields whose type has a contract become theorem parameters (other field access waits for M7). First step: the Std closure the library imports is kernel-checked and cross-checked | Pure parts of the payment example verified, and `ProcessPayment` verified with the store as a hypothesis. Differential tests with contract-satisfying mocked externals pass, every new model operation (including the minimal `decimal`) passes CLR-agreement tests, generators include zero divisors, `MinValue / -1` and equal `decimal`s with different scales, and `ProcessPayment`'s certificate passes `scripts/cross-check.sh`. ✅ as described in [docs/m6/](m6/README.md) (plan [2026-11-08-1445](plans/2026-11-08-1445-feat-m6-contracts-effects-plan.md), branch `feat/m6` at c54de2e): `dotnet test --filter M6Exit` runs one fact per criterion, 4 of 4 pass (`M6ExitTests` in `Warrant.Cli.Tests`, `Warrant.Engine.Tests` and `Warrant.Semantics.Tests`; [docs/m6/08](m6/08-reports-and-testing.md#the-exit-criterion-as-tests)). `ProcessPayment` (`tests/corpus/m6/accepted/Payments.cs`) is proved by the default procedure with no script, and its report block is `tests/corpus/m6/ProcessPayment.report.txt`. `scripts/cross-check.sh` ends with "all verdicts agree" with its five M6 rows, Lean's kernel accepting the accepted corpus's certificate with `ProcessPayment`'s contract theorem and the bundle's `Std.Do` closure, and both kernels rejecting a tampered copy (Windows, Git Bash, 2026-11-11). The M6 corpus (145 members in five compilations, `refuted-dependencies` among them) gets its expected outcome in the engine, extraction, analyzer and CLI tests; the build matrix (`dotnet build`, Visual Studio 2026's and 2022's MSBuild) passes 65 of 65 with a contract-bearing project and its refuted twin. Server start with the full M6 bundle (4,112 constants) is 4,053 ms median on the reference workstation against M5b's 2,807 ms in the same session, under the plan's threshold (5 s when measured, 10 s since the owner raised it on 2026-11-11, #178), so the bundle stays a verified load (`tests/data/README.md`). The plan's private-codebase criterion is a hand check outside this repository and is not part of this evidence. Known gaps, none of which lets a false claim pass: GitHub #215 to #218, #226 and #227 (#220 and #225 were fixed after the milestone). The owner decisions open at exit (#180 to #183, #213, #219, #221, #224) were settled on 2026-11-11 and 2026-11-12: among them `Spec.NoThrow` (#182, [docs/m6/06](m6/06-contract-obligations.md)) and one overflow rule for specs, theorem statements, `Spec.Assert` and method bodies, with `unchecked(...)` the explicit wrap (#183, #235, #236, #244; [docs/m6/README.md](m6/README.md)). |
| M7 | Regions, loops with invariants, heap model for mutable objects, full `decimal` arithmetic and rounding, strings | The payment example verified without restructuring into records (the target code in §5.3). CLR-agreement tests pass for the `decimal`, string and heap models. |
| M8 | `grind`, typed Mathlib handles (after the Mathlib run) | Not defined yet (§12 Q15). Define one before starting. |
| M9 | Live IDE feedback (language server / extension), performance work | Not defined yet (§12 Q15). Define one before starting. |

Work deferred from M2/M3 (the Mathlib run with memory measurement, Ansatz and
arena cross-checks, trace diffing, and the §10.3 property tests not yet
covered) is tracked on its own tickets. The Ansatz/arena cross-checks and the
property tests were done in M5a, and the Mathlib run at the start of M5b
([kernel.md](kernel.md#mathlib)): Warrant and Lean's kernel accept all of it,
and checking it peaks at 12.6 GB. Trace diffing is still open. From M5b, an
open item about the server's security on a shared account is GitHub issue #43
(§8.1).

Porting sources: the **Lean 4 sources are authoritative** (`src/kernel/` for
the kernel, `src/Lean/Meta/` for tactics). **Ansatz is the second reference**
and is the closest prior art for a non-C++ port. Port with attribution (NOTICE).

---

## 12. Open questions

1. **`decimal`.** What precision and rounding model should we use? The first
   operations (comparisons and add/subtract without overflow) are scheduled
   in M6, because the payment example needs them; full arithmetic and
   rounding come in M7. *Decided for M6 (M6 KTD7):* the CLR's own
   representation, a sign, a 96-bit mantissa and a scale from 0 to 28.
   Equality and order compare values. `+` and `-` compute the exact sum,
   round it once, half to even, at the largest scale whose mantissa fits in
   96 bits, and raise `overflow` only when even scale 0's does not fit, in
   every context. The definitions are trusted and tested against the CLR by
   representation; the lemmas are proved ([docs/m6/03](m6/03-decimal.md)).
   Multiplication, division and explicit rounding are still M7.
2. **Strings.** Is a full UTF-16 model needed early, or can strings be opaque
   (equality only) at first?
3. **Enums.** *Decided (D12):* open by default (integer-backed), with an
   opt-in `[Closed]`.
4. **Region syntax.** `using (Verify.Region(...)) { }`, a local function with
   `[Verified]`, or something else? How are exit paths specified? Decide
   before M7 starts.
5. **Specifications about external effects.** For example, "`SavePayment` was
   called exactly once with a processed payment." This needs a trace of
   external calls in the monad and a spec vocabulary over it. *Not in M6:*
   M6's monad threads an opaque world, not a trace, and a dependency's
   contract speaks about one call; its exit criterion needs no call count.
   Revisit when a real contract needs one.
6. **Heap model** for mutable classes: dynamic frames, separation logic, or
   ownership (records only until M7)? Decide before M7 starts.
7. **IDE feedback.** A language server, a VS Code / Rider / Visual Studio
   extension, or an analyzer that reads a results file? The last one conflicts
   with analyzer determinism.
8. **Automation defaults.** Which tactic pipeline, and what fuel and time
   budgets per unit? *Budgets decided (D14):* kernel fuel 20M steps for builds
   and 100M for corpus runs, tactic fuel 171,970 steps (ten times the largest
   use in the M5a corpus), and 30 seconds of wall clock per theorem, set per
   project with `WarrantKernelFuel`, `WarrantTacticFuel` and
   `WarrantTimeoutSeconds` and per theorem with `[Theorem(KernelFuel = …,
   TacticFuel = …, TimeoutSeconds = …)]`. Since M5b every unit runs under
   them, definitions, equation lemmas and decrease proofs included, through
   the server and in-process alike, and the counterexample search is bounded
   by fuel alone, so it finds the same values under any load. *Pipeline for
   contracts decided in M6 (M6 KTD13, KTD14):* a structural VC walker over the
   program shapes the translator emits, then a VC simp set kept apart from
   `Tactic.Simp()`'s default set, then `omega`, under the same budgets; the
   vacuity check of a `Spec.Requires` gets 200,000 steps of tactic fuel. A
   `[ProofFor]` script replaces it for one method
   ([docs/m6/07](m6/07-vc-generation.md)). `grind` joins it in M8. A
   theorem without `.By` is still proved only by `rfl` or `decide`; no default
   pipeline runs there.
9. **CI trust policy.** Always recheck certificates, or trust signed caches?
   *Decided for M5a (D15):* every build re-checks every proof with the
   kernel, so the MSBuild task has no `Inputs`/`Outputs` and M5a has no cache.
   *Decided for M5b (D17):* cache hits are trusted locally, and
   `WarrantRecheck=true` makes the kernel re-check every cached proof against
   statements rebuilt from the current code, without running tactics; the
   docs recommend it for CI. Entries are not signed: a per-user key adds key
   management and stops CI agents sharing entries, and kernel-checking every
   hit would make `WarrantRecheck` redundant. An entry is written only after
   the kernel accepted its certificate and carries a content hash, so
   accidental damage is a miss; a deliberate edit of `obj/warrant/` is outside
   what a local build defends against, and recheck is the defence where that
   matters.
10. **Lean version pin.** Pinned to Lean v4.35.0 and lean4export `5a9a355`
    (`scripts/lib/lean-toolchain.sh`). The kernel was ported against v4.33.1
    and re-diffed against v4.35.0: the only kernel change in between removes
    native reduction (`Lean.reduceBool`/`reduceNat`), which Warrant never
    supported. Each later upgrade means re-diffing `src/kernel/` and re-running
    `scripts/cross-check.sh` with a fresh Init export.
11. **Nullable annotations.** Treat them as assumptions (current proposal) or
    verify them? *Decided for M6 (M6 KTD20):* non-nullable reference
    annotations remain assumptions, listed in the report, including that each
    dependency and each non-nullable reference a dependency returns is not
    null. A value declared `T?` is not an assumption: where it is used as a
    `T`, the proof must show it is not null, whatever the compiler's flow
    analysis says (M6 KTD5).
12. **Name.** *Decided (D3):* Warrant, chosen before M4 publishes the user API
    package, since a rename later breaks every user's attributes and namespaces.
13. **Target framework.** *Decided (D8):* net10.0 for the server and core,
    netstandard2.0 for the user API package and anything Roslyn or MSBuild loads.
14. **Collections, generics and other integer types.** §6.1 maps
    `IReadOnlyList<T>`/`ImmutableArray<T>`, generics, and unsigned and small
    integers, but no milestone schedules them. Schedule them (M6 already
    extends the semantics library) or record them as non-goals? Without them
    most existing business code stays outside the subset. Decide before M6
    starts. *Still open after M6:* M6 scheduled none of them, and the owner
    has not decided; it is the M6 plan's first open question and has no
    ticket yet. Generic types and members, and integer types other than `int`
    and `long`, are still rejected.
15. **M8 and M9 exit criteria.** M8 is `grind` and typed Mathlib handles; M9
    is live IDE feedback and performance work, split from M8 on 2026-11-10.
    What latency and memory budget makes live IDE feedback good enough? M5b's
    recorded baselines are the starting point
    ([docs/m5b/08](m5b/08-testing-and-baselines.md#baselines-for-m9)). What
    must `grind` and the typed handles prove for M8 to be done? Define each
    before its milestone starts.

Questions 16 to 20 came from rewriting ten functions of a production C#
codebase (the claims modules of an insurance platform) in the §5 surface, one
or two per milestone from M4 to M7.

16. **Closed-set classes.** Many codebases use the "smart enum" pattern instead
    of C# `enum`: a sealed class with a private constructor and static
    instances, compared by reference (for example
    `AssignmentOutcome.Matched`, backed by a `StringClosedSetBase<T>`). §6.1 has no row for it, so
    every method that touches one is outside the M4 subset. Proposal: Q3's
    `[Closed]` also applies to such classes, recognised by shape (sealed,
    private constructors, static get-only instances of the type itself); they
    translate to an `inductive` with `DecidableEq`, and the analyzer rejects a
    `[Closed]` class that doesn't have that shape. *Decided (D13):* as proposed,
    in M4; revisit the shape rule if real code doesn't fit it. As built in M4,
    a `[Closed]` class without the shape is error **WRT0009**, which names the
    step of the shape check that failed; instances may also be `static
    readonly` fields; and `==` compares a generated `$index` rather than
    using `DecidableEq`. Reading an instance field or property of a closed
    class in verified code is WRT0002, because the model keeps only which
    instance a value is.
17. **Specs on expression-bodied members.** `Spec.Ensures` is a statement, so
    it needs a block body. Most small pure methods and properties are
    expression-bodied (`=> a && b`), so specifying them means rewriting the
    body. Options: accept the rewrite (a code fix can do it); let a companion
    `[ProofFor(nameof(M))]` method carry the contract; or read a leading
    `Spec.Ensures` from a `Spec.Contract(() => ...)` wrapper. Decide before M6
    adds `Spec.Ensures`. *Decided for M6 (M6 KTD8):* block bodies only. A
    `Spec` call in an expression-bodied member is WRT0002 saying to use a
    block body; the code fix that rewrites it is deferred. A `[ProofFor]`
    method supplies a script, not a contract.
18. **Collections and case-insensitive strings come before contracts in
    practice.** The most valuable specs in the reviewed code (queue matching,
    adjuster eligibility) call `IReadOnlyList<T>.Contains`, LINQ `Any`/`Where`,
    and `string.Equals(..., OrdinalIgnoreCase)`. Without Q14 (collections) and
    at least opaque strings with equality and a case-insensitive comparison
    (Q2), M6 can verify `ProcessPayment` but not the code that motivated this
    review. This argues for scheduling Q14 and a minimal string model in M6.
    *M6 did not:* its exit criterion needs neither, so it added no collections
    and no strings. The point stands and is recorded for M7 planning, which
    has strings in its row (§11) and, until Q14 is decided, no collections.
19. **A source dependency for specifications.** The §5 surface needs the
    `Warrant` package referenced by the code being verified. Teams that
    can't take that dependency yet (one existing in-house translator chose
    `//@` comments for exactly this reason) need a route that doesn't touch the
    project file: a spec sidecar file keyed by method signature, holding the
    same C# expressions. Decide whether sidecars are supported, and in which
    milestone, before M6. *Still open after M6:* M6 puts contracts in source
    only, and the owner has not decided whether sidecars come in a named
    milestone; it is the M6 plan's second open question and has no ticket
    yet.
20. **Smaller gaps found in the same review.**
    - `Guid` (and `Guid?`) has no model. An opaque type with decidable equality
      is enough for every use seen.
    - `Math.Abs` on `decimal` is missing from M6's minimal `decimal` list.
    - M5a's tactics have no `decide` over finite domains and no `split` for
      `if`/ternaries. A theorem quantified over several `bool` or closed-set
      parameters then needs a nested `cases` per parameter.
    - Most dependencies arrive through primary-constructor parameters, which
      are not `readonly` fields, so M6's rule "readonly fields whose type has a
      contract become theorem parameters" doesn't cover them. Extend the rule
      to captured parameters that are never assigned (the analyzer can check
      this).
    - Logging calls (`LogDebug($"...")`) in verified methods drag in string
      interpolation. They need a standard contract that says "no effect on
      verified state", listed in the assumption report.
    - A `static readonly` array used as a constant table is a heap object.
      Treat it as a constant when nothing writes to it, or require
      `ImmutableArray<T>`.
    - Vocabulary §5 doesn't have yet: where exceptions may come from
      (`Spec.ThrowsOnlyFrom`), how often an external was called (Q5),
      frame conditions (`Spec.Modifies`), and a ghost iteration counter for
      `foreach` invariants (§5.3 shows only `for`).

    *What M6 did with these:* never-assigned primary-constructor parameters
    count as dependencies, as proposed (M6 KTD9), and `Math.Abs` on `decimal`
    is modelled. `Guid`, a standard logging contract (it needs string
    interpolation, M7), `decide` and `split` tactics, a `static readonly`
    array as a constant table, `Spec.ThrowsOnlyFrom`, `Spec.Modifies` and a
    call count are not built and not scheduled; logging calls and `Guid`
    values in a verified method are still rejected.

---

## Appendix A. Facts checked against Ansatz

Checked on 2026-10-31 against `replikativ/ansatz` at commit
`662ac21e687083829ecd04968dd47cbec3541a7a`, to correct details in the ChatGPT
conversation:

| Claim | Finding |
|---|---|
| Kernel IR has 11 node types including `MVar` | 12 kinds including `Proj` and split Nat/String literals; no `MVar` (`doc/kernel.md`). |
| `test-data/init-medium.ndjson`, ~10 MB | `resources/ansatz/init-medium.ndjson.gz`, 3.3 MB gzipped. Ansatz's docs call it 2,997 declarations; Warrant's reader counts 5,118 constants in 4,631 declaration records (cross-checked with an independent script), so Ansatz evidently counts a different unit. |
| ~648k Mathlib declarations, 210k theorems | 707,508 declarations (504,824 theorems) at Mathlib v4.33.1, **all verified** by the Java kernel (`doc/kernel-validation.md`). |
| Import via lean4export NDJSON | Correct; lean4export format 3.0/3.1. |
| Exports proofs to Lean 4 | Correct (Lean 4 syntax export). |
| Kernel is small relative to the rest | Correct: about 11k lines of Java kernel versus about 21k lines of Clojure tactics and about 20k of elaboration, surface and store code. |
| (not mentioned) | Ansatz compiles runtime code *from the checked kernel term* (following Lean's LCNF compiler), with exact Lean integer semantics. |
| (not mentioned) | Ansatz adds kernel fuel (Lean has none); the default is 20M interactive and 100M corpus. |
