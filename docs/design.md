# LeanSharp Design

> Status: **draft, design phase** · Started 2026-10-31
> History: [ChatGPT conversation](history/2026-10-31-chatgpt-recommend-csharp-frontend.md) ·
> [Claude design session](history/2026-10-31-claude-design-session.md)

LeanSharp verifies properties of ordinary C# code with machine-checked proofs.
C# methods are translated into terms of the Calculus of Inductive Constructions
(CIC), the type theory of Lean 4. Proofs about those terms are checked by a
C# port of the Lean 4 kernel, and the existing Lean libraries (Init, Std,
Mathlib) are available as imported, already-elaborated declarations.

The project is inspired by [Ansatz](https://github.com/replikativ/ansatz), which
does the same for Clojure. Ansatz is a Lean 4 kernel in Java with an elaborator,
tactics, and a Clojure surface language. LeanSharp keeps Ansatz's foundations
(kernel, lean4export import, independent re-checking) but takes the opposite
direction at the surface: **it verifies existing C# rather than generating code
from verified definitions.** See §2.

---

## 0. Decision log

| # | Decision | Status |
|---|---|---|
| D1 | **Verify existing C# (direction B).** Translate C# into a CIC model and prove properties of the model. Do not generate C# from verified terms (direction A). | Decided |
| D2 | Verification runs in a **long-lived verification server**, not in the IDE's analyzer process. | Decided |
| D3 | Working name **LeanSharp** (to be revisited). | Decided |
| D4 | License **Apache 2.0**, with NOTICE attribution to Lean 4 and Ansatz. | Decided |
| D5 | **Port the kernel** to C#. Don't bridge to Ansatz's JVM kernel. | Proposed, not objected to |
| D6 | Cross-check by **exporting lean4export NDJSON**, not by pretty-printing Lean source. | Proposed, not objected to |
| D7 | Map C# types to **faithful Lean models** (`int` → `Int32` with wrap-around, not unbounded `Int`). | Proposed, not objected to |
| D8 | Target **net10.0** for the server and core libraries. Components loaded by Roslyn or MSBuild target **netstandard2.0**. | Default, unconfirmed |
| D9 | External dependencies (databases, services) are **hypotheses in the theorem**, never global axioms. | Proposed |
| D10 | The C# semantic model is a **Lean 4 library written and proved in real Lean**, exported to NDJSON, and shipped with LeanSharp. | Proposed |
| D11 | Verification-condition generation is **proof-producing (a tactic)**, so it is outside the trusted base. | Proposed |

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

LeanSharp inverts this. The developer's C# is the source of truth, it runs as
written, and LeanSharp proves properties of a **model** of it. Only this
direction covers the motivating example: an existing method that validates
input, reads from a database, applies more logic, and writes back, where we
want to prove the logic and assume the database behaves.

The cost is a **faithfulness gap**: a proof about the model is only as good as
the translation. LeanSharp addresses this in three ways:

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
 │     ├──► Roslyn compiler ──► LeanSharp.Analyzers   (pure, fast checks:     │
 │     │                         unsupported constructs, malformed specs)     │
 │     │                                                                      │
 │     └──► MSBuild: LeanSharp.Build task (after CoreCompile)                 │
 │             │  builds a CSharpCompilation from the Csc inputs              │
 │             │  LeanSharp.Extraction: IOperation / CFG ──► VIR units        │
 │             ▼                                                              │
 │        JSON-RPC over named pipe / Unix socket                              │
 │             │                                                              │
 │  ┌──────────▼──────────── leansharp-server (net10.0) ──────────────────┐   │
 │  │  Result cache (content-addressed: verdicts + proof certificates)    │   │
 │  │      │ miss                                                         │   │
 │  │      ▼                                                              │   │
 │  │  LeanSharp.Semantics   VIR ──► CIC model (over the LeanSharp Lean   │   │
 │  │                        library) + goals                             │   │
 │  │      ▼                                                              │   │
 │  │  LeanSharp.Meta / Tactics   VC generation, simp, omega, … ──►       │   │
 │  │                             proof terms   (untrusted)               │   │
 │  │      ▼                                                              │   │
 │  │  LeanSharp.Kernel      type-checks every proof term   (trusted)     │   │
 │  │      ▲                                                              │   │
 │  │  LeanSharp.Store       Init / Std / Mathlib / LeanSharp semantics,  │   │
 │  │                        lazily loaded, from lean4export NDJSON       │   │
 │  └─────────────────────────────────────────────────────────────────────┘   │
 │             │                                                              │
 │             ▼                                                              │
 │   diagnostics (build errors with goals) + assumption reports +             │
 │   exported NDJSON certificates ──► other kernels (Lean, Ansatz, arena)     │
 └────────────────────────────────────────────────────────────────────────────┘
```

### 3.1 Why a server

- **Analyzers must stay pure and fast.** They run in the IDE on every edit,
  must target `netstandard2.0`, and Roslyn's own analyzer rules (RS1035) ban
  file and network I/O in them. Loading a declaration store and running
  tactics there is the wrong fit: Ansatz needs 5–6 GB of heap for its hardest
  Mathlib declarations.
- **Large state should be loaded once.** The store, the elaborated environment
  and the caches persist across builds. The precedent is Roslyn's own compiler
  server (`VBCSCompiler`), which the build starts on demand and reuses.
- **One engine, many clients.** The MSBuild task, the CLI, and a later IDE
  extension or language server all talk to the same server, so their results
  agree.
- The kernel and tactics can target modern .NET (net10.0: `Span`, vectorized
  hashing, `BigInteger` performance) instead of `netstandard2.0`.

### 3.2 Division of labour

| Component | Runs in | Target | Responsibility |
|---|---|---|---|
| `LeanSharp` (user API) | user app | netstandard2.0 | Attributes, `Spec.*`, `Prove`, `Tactic.*`. No runtime behaviour (§5). |
| `LeanSharp.Analyzers` | compiler / IDE | netstandard2.0 | Deterministic checks only: supported subset, spec well-formedness, calling `[Theorem]` methods, missing contracts on externals. No I/O. |
| `LeanSharp.Extraction` | analyzer + build task | netstandard2.0 | Roslyn `IOperation` / `ControlFlowGraph` → VIR. Shared, so the analyzer and the build agree on what is supported. |
| `LeanSharp.Vir` | everywhere | netstandard2.0 | The **Verification IR** and its canonical serialization. This is the wire protocol between extraction and the server. |
| `LeanSharp.Build` | MSBuild | netstandard2.0 | After `CoreCompile`: extract, send to the server (starting it if needed), report diagnostics, write reports. Authoritative for builds and CI. |
| `leansharp-server` | own process | net10.0 | Cache, translation, tactics, kernel, store. Stays free of Roslyn: it only sees VIR. |
| `leansharp` CLI | own process | net10.0 | `verify`, `check-store`, `import`, `export`, `explain`; runs the engine in-process for CI without a daemon. |

Keeping Roslyn out of the server means the server's input (VIR) is small,
canonical, and hashable. That is what makes the cache (§8.2) reliable.

---

## 4. The pipeline in detail

```text
C# method
  │  Roslyn: binding, overload resolution, types, nullable analysis   (free)
  ▼
IOperation tree + ControlFlowGraph
  │  LeanSharp.Extraction
  ▼
VIR unit   (typed, structured, explicit effects; one per method / region / theorem)
  │  LeanSharp.Semantics   (part of the trusted base: see §9)
  ▼
CIC definitions over the LeanSharp Lean library  +  goals (CIC Props)
  │  LeanSharp.Tactics: VC generation (mvcgen-style), simp, omega, …   (untrusted)
  ▼
Proof terms
  │  LeanSharp.Kernel   (trusted)
  ▼
Verdict + certificate (NDJSON) + assumption report
```

Roslyn has already resolved types, overloads, implicit conversions, operator
methods, and flow, so LeanSharp needs **much less elaboration than Ansatz**.
Ansatz must infer binder types and implicit arguments from untyped
s-expressions. For LeanSharp, translation is mostly a direct mapping. The
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
- Source spans for every node, so diagnostics point at C# code.
- Compilation facts that change semantics, for example whether
  `CheckForOverflowUnderflow` is on (it decides between wrap-around and
  `OverflowException` in unannotated code).

VIR has a canonical binary and JSON encoding, and every unit has a content hash.

### 4.2 Translation to CIC (LeanSharp.Semantics)

- **Pure units** (no heap writes, no external calls) become plain Lean
  definitions, a *shallow embedding*. `if` becomes `ite`/`dite`, `switch`
  becomes a match, locals become `let`, and recursion becomes well-founded
  recursion with a `Spec.Decreases` measure (or structural recursion when
  detectable).
- **Effectful units** become programs in a LeanSharp monad defined in the Lean
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

Everything is valid C#. Spec methods are marked
`[Conditional("LEANSHARP_CONTRACTS")]`, so the compiler drops the calls from
emitted IL by default. They remain fully bound in Roslyn's semantic model and
`IOperation` tree, which is all LeanSharp needs.

C# attribute arguments must be compile-time constants, so
`[Ensures(r => r > 0)]` is impossible. String specs would be untyped. LeanSharp
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
  `&&` → `∧`, `||` → `∨`, `!` → `¬`, and `==` on supported types → `Eq`.
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
| `sbyte` `short` `int` `long` | `Int8` `Int16` `Int32` `Int64` | Core Lean types (`Init/Data/SInt`), two's complement. Wrap-around in `unchecked` code. |
| `byte` `ushort` `uint` `ulong` | `UInt8` … `UInt64` | |
| `checked(...)` arithmetic | `Except OverflowException` | Also the default when the project enables `CheckForOverflowUnderflow`. |
| `System.Numerics.BigInteger` | `Int` | |
| `LeanSharp.Nat` / `LeanSharp.Integer` | `Nat` / `Int` | Runtime structs for code written mathematically. |
| `decimal` | LeanSharp model (96-bit mantissa, scale) | **Open question.** Central for business code (§12). |
| `float` `double` | not supported | Lean's `Float` is opaque to the kernel. |
| `string` `char` | LeanSharp model over UTF-16 code units | Lean's `String` is a sequence of Unicode scalar values, so `Length` would differ for surrogate pairs. |
| `T?` (reference, nullable) / `Nullable<T>` | `Option T` | Non-nullable reference annotations are assumptions, listed in the report, not facts. |
| `record` / `readonly record struct` | Lean `structure` | `with` becomes structure update. Value equality is generated. |
| `enum` | underlying integer + named constants | C# enums are open (any value can be cast), so they aren't modelled as closed inductive types unless marked `[Closed]`. |
| Generics | universe-polymorphic parameters | Constraints become type-class instances later. |
| `IReadOnlyList<T>`, `ImmutableArray<T>` | `List T` / `Array T` models | |
| Exceptions | `Except` branch of the monad | |
| Mutable classes and fields | heap model (§6.2) | Not in the first effectful milestone. |
| `async`/`await` | sequencing in the monad | Supported only when awaiting external or verified calls. |

### 6.2 The LeanSharp Lean library (D10)

The semantic model is **written in Lean 4 and proved in Lean 4**, in
`lean/LeanSharp/` inside this repository:

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

### 7.1 LeanSharp.Kernel

The kernel is a port of the Lean 4 kernel, using Ansatz's Java kernel as a
second reference. Ansatz's version is about 11k lines: `TypeChecker` 3.2k,
`Reducer` 1.9k, `Level` 620, and about 2.5k for inductive types, recursors and
nested inductives.

- **Expressions:** 12 kinds, `BVar`, `FVar`, `Sort`, `Const`, `App`, `Lam`,
  `Forall`, `Let`, `NatLit`, `StrLit`, `MData`, `Proj`. **There is no `MVar` in
  the kernel**; metavariables live in `LeanSharp.Meta`. (ChatGPT's list
  wrongly included `MVar` and omitted `Proj`.)
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
  verification.
- **Tracing** in the same NDJSON format as Ansatz's `checkConstantTraced`
  (`{s, d, l, r, res, by}`), so that definitional-equality traces can be
  diffed against Ansatz and Ansatz's instrumented Lean kernel.
- The kernel depends only on `LeanSharp.Cic`: no I/O, no Roslyn, no store.
- Status and the exact list of deliberate differences from Lean: [kernel.md](kernel.md).
- `LeanSharp.Cic.Expr` has no metavariable kind today. Whether `LeanSharp.Meta`
  adds one to the shared type (as Lean does, with the kernel rejecting it) or
  keeps its own representation is decided at M4.

### 7.2 Import (lean4export NDJSON)

- lean4export format 3.x. Each line defines an indexed name (`in`), level
  (`il`) or expression (`ie`), and declarations refer to those indices. It is
  read with a streaming `System.Text.Json` reader.
- Two modes:
  - **Trusted import:** accept declarations that Lean already checked. This is
    fast, and suitable for development.
  - **Verified import:** re-check every declaration with our kernel. This is
    the default for CI on the semantics bundle, and is the main kernel test.
- Bundles shipped with LeanSharp: Init (Ansatz ships an `init-medium` subset
  of Lean 4.33.1's Init: 5,118 constants in 4,631 declaration records, 3.3 MB
  gzipped) and the LeanSharp semantics library.
  Mathlib (707,508 declarations at v4.33.1) is optional and downloaded.

### 7.3 Store

> Scheduled with the verification server (M5b): the store's layout depends on how the server
> caches checked environments, and at Init scale loading NDJSON is not a bottleneck.

We don't port Ansatz's datahike/konserve store. Instead, a versioned on-disk
binary format:

- content-addressed expression and declaration blobs
- a name index for lazy loading
- memory-mapped reads
- a manifest that records the Lean version, the lean4export format version,
  and the bundle hashes

The interface is roughly `IDeclarationStore { TryGet(Name), Contains(Name),
Find(prefix) }`.

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

- `leansharp-server` is a net10.0 process, one per user and machine, with
  per-solution sessions. The build task starts it on demand, and it shuts down
  after an idle timeout.
- Transport: JSON-RPC (StreamJsonRpc) over a named pipe on Windows or a Unix
  domain socket elsewhere. The protocol is versioned, and a mismatch causes a
  restart.
- Core methods: `verify(units[], priority)`, `cancel(id)`, `status`,
  `explain(unitId)` (goals, context, tactic trace), `export(unitIds)`,
  `report(project)`.
- Scheduling: units are verified in parallel, with per-unit fuel and
  wall-clock limits. IDE requests take priority over builds, and work is
  cancelled when the source changes.

### 8.2 Content-addressed cache

- **Key:** a hash of the canonical VIR of the unit, the *statements* (not the
  proofs) of the units and contracts it depends on, the semantics-bundle hash,
  the environment and store hashes, and the kernel version.
- **Value:** the verdict, the **proof certificate** (proof terms as NDJSON),
  diagnostics, and the assumption report.
- Stored on disk per project (`obj/leansharp/`) and in a per-user shared cache.
- **Proof replay:** a cached certificate can be re-checked by the kernel alone,
  without re-running tactics. That is cheap compared with proof search, so CI
  can run with `LeanSharpRecheck=true`. CI then trusts only the kernel, not the
  cache contents.

### 8.3 Build integration

`LeanSharp.Build` runs after `CoreCompile`. It recreates the
`CSharpCompilation` from the same inputs Csc received (sources, references,
defines, `LangVersion`, overflow-checking setting), extracts VIR, calls the
server, and emits errors such as:

```text
Payments.cs(42,5): error LSV0001: Postcondition of 'ProcessPayment' could not be verified.
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
ProcessPayment            VERIFIED   (kernel: LeanSharp 0.1, cert 3f9a…)
  Assumed (contracts):
    - IPaymentStore.GetPayment returns null or a payment with the requested Id
  Assumed (global):
    - No concurrent modification between GetPayment and SavePayment
    - Non-nullable reference annotations on Payment hold
    - Semantics bundle leansharp-semantics 0.1 models C# 12 faithfully
  Proved:
    - Result.Success implies paymentId > 0
```

---

## 9. Trusted computing base

| Trusted | Why | Mitigation |
|---|---|---|
| `LeanSharp.Kernel` | Accepts or rejects proof terms. | Arena negatives, init/Mathlib corpus, cross-kernel export, property tests, trace diffs (§10). |
| `LeanSharp.Semantics` (VIR → CIC) | The faithfulness gap. | Small and syntax-directed; differential testing against compiled .NET. |
| `LeanSharp.Extraction` (C# → VIR) | Same gap, one layer earlier. | Same differential tests, end to end. |
| Semantic-model *definitions* in `lean/LeanSharp` | The claim that "this models C#". | Reviewed; tested against .NET behaviour (for example exhaustively for 8- and 16-bit types, sampled for 32/64-bit). |
| Declared contracts and global assumptions | By design. | Listed in every assumption report. |
| Trusted-mode imports | Lean already checked them. | Verified import mode removes this. |

**Not trusted:** the elaborator, tactics, VC generation (D11), the server, the
cache (with recheck), the importer in verified mode, and the Roslyn analyzer.

---

## 10. Assurance and testing strategy

1. **Kernel corpus.** In order: `Nat.add_succ.ndjson` → arena cases
   (positive, and negative such as `002_badDef`, `141_falseFromUnsafe`) →
   init-medium (5,118 constants) → full Init (57,977 declarations, 59,433 constants) → Mathlib v4.33.1 (707,508; Ansatz
   checks all of them in about 80 minutes on 4 workers). Every discrepancy
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
| M1 | `LeanSharp.Cic` (Name, Level, Expr, ConstantInfo, Env), the NDJSON reader (formats 3.0.0 and 3.1.0) and writer (3.1.0) | `Nat.add_succ`, init-medium and the arena files import; import → export → import yields identical constants; export is idempotent. ✅ |
| M2 | `LeanSharp.Kernel` | All 5,118 init-medium constants pass; arena negatives are rejected; then full Init. ✅ full Init (57,977 declarations), init-medium and arena (see [kernel.md](kernel.md)) |
| M3 | Exporter, cross-kernel harness, FsCheck property tests | Certificates check in at least one external kernel. Mathlib is a stretch goal. ✅ Lean's kernel re-checks everything LeanSharp admits, including full Init and C#-built types (see [kernel.md](kernel.md)); the store moved to M5b |
| M4 | VIR, extraction of the pure subset (`int`/`long`/`bool`, enums, records, `if`/`switch`; theorems are parameterless `[Theorem]` methods returning `Prove.That(bool)`; recursion is rejected until M5a, and `/`, `%` and checked arithmetic are rejected with a diagnostic until M6, and non-null record parameters are recorded as assumptions), semantics library v0 with CLR-agreement tests (§10.6), translation, differential testing | A fixed corpus (`tests/corpus/m4/`) translates, including a `Validate`-shaped method over records and enums (`int` in place of `decimal`), and every rejected construct has a corpus method that is rejected with the diagnostic. Differential tests pass; null-record inputs check that .NET throws and that the non-null assumption is recorded. CLR-agreement tests pass for every modelled operation. Theorems without free parameters are closed by `rfl`/`decide` proof terms the translator emits. The translated corpus, exported with its Init + semantics closure, passes a new translated-output step in `scripts/cross-check.sh`. |
| M5a | `LeanSharp.Meta` and tactics v1 (`intro`, `exact`, `apply`, `cases`, `induction`, `simp`, `omega`), quantified theorems and `Prove.That(...).By(...)`, structural recursion and well-founded recursion with `Spec.Decreases`, translator-generated equation lemmas for recursive definitions, a development-time export of simp, instance and reducibility attributes for Init and the semantics library next to the NDJSON bundle (untrusted tactic input; Std is added in M6), `Int32`/`Int64` → `Int` bridging lemmas and an omega-prep simp set (§6.2), in-process `leansharp verify` (§3.2), a thin MSBuild task that runs `leansharp verify` as a child process (the net10.0 engine cannot load in .NET Framework MSBuild) | First end-to-end result: `Increment(x) > x` fails the build with its goal shown under `dotnet build` and Visual Studio's MSBuild; `ValidImpliesPositive` (`int`), a well-founded method whose decrease needs `omega`, and a quantified theorem over a translated `int` method closed by `simp` then `omega` pass. Differential tests pass for a well-founded unit, evaluated with its equation lemmas. The certificate of a verified C# theorem passes the translated-output step of `scripts/cross-check.sh`. |
| M5b | Server, content-addressed cache, store v1 (trusted and verified import), CLI verbs, analyzers | The M5a result through the server. A second build is served from the cache without running tactics, `LeanSharpRecheck=true` re-checks cached certificates with the kernel alone, and the Init + semantics store passes `leansharp check-store` in verified mode. `cancel` aborts a running verify, a unit over its fuel or wall-clock budget reports a timeout, and analyzer output is identical across runs. Baseline per-unit verification latency and server memory are recorded for M8. Store v1 waits for the Mathlib run's memory figure. |
| M6 | Contracts: `Spec.Requires`/`Ensures`, contract classes, effect monad (exceptions, null, overflow, `/` and `%`), VC generation with `@[spec]` lemmas in the attribute sidecar, assumption reports, a minimal `decimal` model (96-bit mantissa and scale, comparisons, add/subtract without overflow; `==` is numeric equality, so `1.0m == 1.00m`, also inside records). Readonly fields whose type has a contract become theorem parameters (other field access waits for M7). First step: the Std closure the library imports is kernel-checked and cross-checked | Pure parts of the payment example verified, and `ProcessPayment` verified with the store as a hypothesis. Differential tests with contract-satisfying mocked externals pass, every new model operation (including the minimal `decimal`) passes CLR-agreement tests, generators include zero divisors, `MinValue / -1` and equal `decimal`s with different scales, and `ProcessPayment`'s certificate passes `scripts/cross-check.sh`. |
| M7 | Regions, loops with invariants, heap model for mutable objects, full `decimal` arithmetic and rounding, strings | The payment example verified without restructuring into records (the target code in §5.3). CLR-agreement tests pass for the `decimal`, string and heap models. |
| M8 | Live IDE feedback (language server / extension), `grind`, typed Mathlib handles (after the Mathlib run), performance work | Not defined yet (§12 Q15). Define one before starting. |

Work deferred from M2/M3 (the Mathlib run with memory measurement, Ansatz and
arena cross-checks, trace diffing, and the §10.3 property tests not yet
covered) is tracked on its own tickets. The Ansatz/arena cross-checks and the
property tests must be done before M5a closes. The Mathlib run must finish
before M5b's store v1 work and M8's typed handles.

Porting sources: the **Lean 4 sources are authoritative** (`src/kernel/` for
the kernel, `src/Lean/Meta/` for tactics). **Ansatz is the second reference**
and is the closest prior art for a non-C++ port. Port with attribution (NOTICE).

---

## 12. Open questions

1. **`decimal`.** What precision and rounding model should we use? The first
   operations (comparisons and add/subtract without overflow) are scheduled
   in M6, because the payment example needs them; full arithmetic and
   rounding come in M7.
2. **Strings.** Is a full UTF-16 model needed early, or can strings be opaque
   (equality only) at first?
3. **Enums.** Should they be open by default (integer-backed), with an opt-in
   `[Closed]`? Decide in M4, which adds enums.
4. **Region syntax.** `using (Verify.Region(...)) { }`, a local function with
   `[Verified]`, or something else? How are exit paths specified? Decide
   before M7 starts.
5. **Specifications about external effects.** For example, "`SavePayment` was
   called exactly once with a processed payment." This needs a trace of
   external calls in the monad and a spec vocabulary over it.
6. **Heap model** for mutable classes: dynamic frames, separation logic, or
   ownership (records only until M7)? Decide before M7 starts.
7. **IDE feedback.** A language server, a VS Code / Rider / Visual Studio
   extension, or an analyzer that reads a results file? The last one conflicts
   with analyzer determinism.
8. **Automation defaults.** Which tactic pipeline, and what fuel and time
   budgets per unit? Decide the budgets when M5a starts (in-process
   `leansharp verify` enforces them until M5b's server does); the pipeline can
   wait for M6.
9. **CI trust policy.** Always recheck certificates, or trust signed caches?
   Decide when M5a starts: its MSBuild task is authoritative for CI.
10. **Lean version pin.** Pinned for now to Lean v4.33.1 and lean4export
    `15f6055` (`scripts/lib/lean-toolchain.sh`), the version the kernel was
    ported against. Changing it means re-diffing the kernel port.
11. **Nullable annotations.** Treat them as assumptions (current proposal) or
    verify them?
12. **Name.** LeanSharp is provisional. Decide before M4 publishes the user API
    package, since a rename later breaks every user's attributes and namespaces.
13. **Target framework.** Confirm net10.0 for the server and core (D8) before
    M4 starts.
14. **Collections, generics and other integer types.** §6.1 maps
    `IReadOnlyList<T>`/`ImmutableArray<T>`, generics, and unsigned and small
    integers, but no milestone schedules them. Schedule them (M6 already
    extends the semantics library) or record them as non-goals? Without them
    most existing business code stays outside the subset. Decide before M6
    starts.
15. **M8 exit criterion.** What latency and memory budget makes live IDE
    feedback good enough, and should M8's four items (IDE, `grind`, typed
    handles, performance) be separate tickets? M5b's recorded baselines are the
    starting point. Define it before M8 starts.

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
    `[Closed]` class that doesn't have that shape. Decide with Q3, in M4.
17. **Specs on expression-bodied members.** `Spec.Ensures` is a statement, so
    it needs a block body. Most small pure methods and properties are
    expression-bodied (`=> a && b`), so specifying them means rewriting the
    body. Options: accept the rewrite (a code fix can do it); let a companion
    `[ProofFor(nameof(M))]` method carry the contract; or read a leading
    `Spec.Ensures` from a `Spec.Contract(() => ...)` wrapper. Decide before M6
    adds `Spec.Ensures`.
18. **Collections and case-insensitive strings come before contracts in
    practice.** The most valuable specs in the reviewed code (queue matching,
    adjuster eligibility) call `IReadOnlyList<T>.Contains`, LINQ `Any`/`Where`,
    and `string.Equals(..., OrdinalIgnoreCase)`. Without Q14 (collections) and
    at least opaque strings with equality and a case-insensitive comparison
    (Q2), M6 can verify `ProcessPayment` but not the code that motivated this
    review. This argues for scheduling Q14 and a minimal string model in M6.
19. **A source dependency for specifications.** The §5 surface needs the
    `LeanSharp` package referenced by the code being verified. Teams that
    can't take that dependency yet (one existing in-house translator chose
    `//@` comments for exactly this reason) need a route that doesn't touch the
    project file: a spec sidecar file keyed by method signature, holding the
    same C# expressions. Decide whether sidecars are supported, and in which
    milestone, before M6.
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

---

## Appendix A. Facts checked against Ansatz

Checked on 2026-10-31 against `replikativ/ansatz` at commit
`662ac21e687083829ecd04968dd47cbec3541a7a`, to correct details in the ChatGPT
conversation:

| Claim | Finding |
|---|---|
| Kernel IR has 11 node types including `MVar` | 12 kinds including `Proj` and split Nat/String literals; no `MVar` (`doc/kernel.md`). |
| `test-data/init-medium.ndjson`, ~10 MB | `resources/ansatz/init-medium.ndjson.gz`, 3.3 MB gzipped. Ansatz's docs call it 2,997 declarations; LeanSharp's reader counts 5,118 constants in 4,631 declaration records (cross-checked with an independent script), so Ansatz evidently counts a different unit. |
| ~648k Mathlib declarations, 210k theorems | 707,508 declarations (504,824 theorems) at Mathlib v4.33.1, **all verified** by the Java kernel (`doc/kernel-validation.md`). |
| Import via lean4export NDJSON | Correct; lean4export format 3.0/3.1. |
| Exports proofs to Lean 4 | Correct (Lean 4 syntax export). |
| Kernel is small relative to the rest | Correct: about 11k lines of Java kernel versus about 21k lines of Clojure tactics and about 20k of elaboration, surface and store code. |
| (not mentioned) | Ansatz compiles runtime code *from the checked kernel term* (following Lean's LCNF compiler), with exact Lean integer semantics. |
| (not mentioned) | Ansatz adds kernel fuel (Lean has none); the default is 20M interactive and 100M corpus. |
