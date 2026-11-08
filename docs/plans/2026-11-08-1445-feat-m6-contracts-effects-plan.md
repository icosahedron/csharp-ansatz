---
title: M6 Contracts and Effects - Plan
type: feat
date: 2026-11-08
artifact_contract: ce-unified-plan/v1
product_contract_source: ce-plan-bootstrap
execution: code
---

# M6 Contracts and Effects - Plan

The design will be explained chapter by chapter, literate-programming style, in `docs/m6/` (written by U15).
This plan owns the decisions (KTD1 to KTD24) and the work units (U1 to U15); the chapters will explain them and cite them by ID.
Ticket: git-bug `9002a2c` (GitHub #13). Related: #41 (in scope, U2), #47 and #48 (deferred, see Scope Boundaries).

---

## Goal Capsule

- **Objective:** A developer can verify C# business code that throws, divides, uses `int?` and `decimal`, and calls a database or service through an interface whose members take and return types Warrant models (`int`, `long`, `bool`, `decimal`, their nullable forms, records, enums and closed sets). They state what a method promises with `Spec.Requires`/`Spec.Ensures`, write down what each dependency is assumed to do in a contract class, and `dotnet build` either proves the method for every implementation of its dependencies that keeps those contracts, or fails at the line whose obligation could not be proved. The assumption report lists every contract the proof relied on.
- **Means:** the effectful code becomes a program in a C# effect monad defined over Lean's `Std.Do` (KTD4, KTD5). Contracts become `Std.Do` triples whose external operations are bound hypotheses (KTD9). An untrusted C# VC generator proves them with simp and omega (KTD13).
- **Authority:** this plan's Requirements win on behaviour and its KTDs on mechanism. The `docs/m6/` chapters explain and never override. `docs/design.md` governs anything this plan does not decide, except where U15 amends it (§11, §12 Q1, Q5, Q8, Q11, Q17, Q19, Q20). The M4, M5a and M5b plans' KTDs still hold unless a KTD here replaces one by name.
- **Stop conditions:** stop and ask if:
  - the measured start time crosses KTD3's threshold, at U1 or again at U14 with the full M6 bundle;
  - U3's checkpoint obligation can't be closed by Warrant's simp and omega;
  - `Std.Do`'s `ULift Prop` assertions defeat the kernel or omega in a way the VC simp set cannot clear (KTD13; Alternative C becomes the fallback);
  - a trusted-code change (U6 to U10) cannot be made without changing what an existing accepted corpus member means;
  - the payment example needs a construct this plan defers (Scope Boundaries);
  - a unit needs one of the owner's uncommitted files (see Dependencies).
- **Execution profile:** units in the Unit Index's phase order. Phase A puts the Lean models in the bundle, proves them against the CLR, and ends with one hand-built contract obligation proved by Warrant's own simp and omega, which is the checkpoint for KTD13 and KTD14 (U3). Phase B (surface, VIR, extraction) may run in parallel with A. Phase C translates and proves, and starts only after both. Phase D closes the milestone.
- **Finishing:** an implementer (`ce-work` or a person) builds the units; the repository owner reviews and merges, one pull request per phase.

---

## Product Contract

### Summary

Build milestone M6 as `docs/design.md` §11 and ticket `9002a2c` define it:
- method contracts (`Spec.Requires`, `Spec.Ensures`, `Spec.Assert`) and companion contract classes (`[ContractFor]`);
- an effect monad in the Warrant Lean library for exceptions, null, checked overflow, `/` and `%`, and `async` sequencing;
- VC generation with `Std.Do` triples, run by default as VC generation, then simp, then omega;
- contract assumptions in the assumption report;
- a minimal `decimal` model.

The milestone ends when the design's payment example verifies, with its store as a hypothesis, and its certificate passes Lean's kernel.

### Problem Frame

After M5b, Warrant verifies pure methods over `int`, `long`, `bool`, records, enums and closed sets. Almost no business method is pure in that sense.
The methods worth verifying throw on bad input, divide, read nullable values, use `decimal`, and call a repository or service.
Today each of those is WRT0002 or WRT0005 (`src/Warrant.Extraction/Walker.cs`), and there is no way to say what a method promises beyond a separate `[Theorem]`.
A private production codebase surveyed during M5a shows the cost. Its candidate methods need `throw`, `%`, `int?` and `Math.Min`/`Math.Max`, and its most valuable code calls injected services.

Design D9 already fixes how dependencies are treated: an external call is a hypothesis about every implementation that keeps its contract, never an axiom.
What is missing is the effect model, the contract surface, the statement shape, and a proof procedure that discharges contract obligations without a hand-written script.

### Requirements

**Effects and models**

- R1. A `[Verified]` method may `throw`, use checked arithmetic (in a `checked` block or a `CheckForOverflowUnderflow` project), divide and take remainders of `int` and `long`, and read nullable values, with each operation behaving as the CLR does, exception included.
- R2. `int?` and `long?` are accepted with `null`, `is null`, `is not null`, `HasValue`, `Value`, `??` and `GetValueOrDefault()`.
- R3. `decimal` is accepted with literals, comparisons, numeric equality (`1.0m == 1.00m`, also inside records), `+` and `-` (throwing `OverflowException` on overflow), unary `-`, and `Math.Abs`.
- R4. `Math.Min`, `Math.Max` and `Math.Abs` on `int`, `long` and `decimal` are accepted as modelled members, with `Math.Abs(int.MinValue)` throwing as the CLR does.
- R5. Every new model operation agrees with the CLR on boundary and random inputs, including zero divisors, `MinValue / -1` and equal decimals with different scales.

**Contracts**

- R6. `Spec.Requires(bool)` and `Spec.Ensures(...)` at the start of a verified method's block body state what it assumes and promises. Each is proved for the method, and assumed at every verified call site after the caller proves the callee's precondition.
- R7. A `[ContractFor(typeof(I))]` class states what the members of interface `I` are assumed to do, with the same `Spec` calls. Nothing in it is verified.
- R8. A verified instance method may call members of a contracted interface through a `readonly` field or a never-assigned primary-constructor parameter. The proof then holds for every implementation of those members that satisfies their contracts.
- R9. `async` methods returning `Task`, `Task<T>` or `ValueTask<T>` are accepted when every `await` awaits an external call or a verified method.
- R10. `Spec.Assert(bool, params Tactic[])` adds an intermediate fact to prove, optionally with a script. A `[ProofFor(nameof(M))]` method supplies a script for `M`'s contract obligation when the default procedure fails.

**Proving and reporting**

- R11. A contract obligation without a script is proved by the default procedure (VC generation, then simp, then omega) under the D14 budgets. A failure is WRT0001 at the source line of the obligation that failed, with its goal.
- R12. The assumption report lists, for each verified method, every external contract and every callee contract its proof used, each nullable-reference assumption, and each place it may throw.
- R13. Every certificate Warrant admits for an M6 unit, the Std closure included, is accepted by Lean's kernel through `scripts/cross-check.sh`.

**Compatibility**

- R14. Every accepted M4 and M5a corpus member translates to the same declarations and proves as before, and every rejected member is still rejected, except the members whose construct this milestone now supports. Their new outcomes are listed in the M6 corpus README.

### Success Criteria

- The pure parts of the payment example verify (design §5.2).
- `ProcessPayment` verifies with `IPaymentStore` as a hypothesis, and its certificate passes `scripts/cross-check.sh`.
- Differential tests with contract-satisfying mocked externals pass: CLR runs and model evaluation agree on results and on exceptions.
- CLR-agreement tests pass for every new model operation, with generators that include zero divisors, `MinValue / -1` and equal decimals with different scales.
- The private codebase's blocked candidates that need only R1 to R4 translate, and at least one of them verifies with a stated `Spec.Ensures` under the default procedure. This is checked by hand in the private repository and reported without naming its code.

### Scope Boundaries

**Out of M6 (later milestones, per design §11)**

- Heap model and field access beyond contract-typed dependencies, verified regions, loops with invariants, full `decimal` arithmetic and rounding, strings: M7.
- Live IDE feedback, `grind`, typed Mathlib handles: M8.

**Considered and not built**

- Porting `mvcgen`: it is deprecated in Lean 4.35 (`Std/Tactic/Do/Syntax.lean:440`), and its successor `vcgen` needs `Lean.Meta.Sym` and `grind` (about 42k lines). KTD13's generator is smaller and stays untrusted. Revisit if Lean stabilises `Std.WP` and Warrant ports `grind` (M8).
- A trace of external calls in the monad (design Q5, "`SavePayment` was called exactly once"): the exit criterion needs only per-call contracts. Revisit when a real contract needs a call count.
- `try`/`catch`: no requirement or exit criterion needs catching, and matching a catch against modelled, thrown and external exceptions needs the CLR exception hierarchy in the trusted translator. `try` stays WRT0002. Revisit when a surveyed method or contract needs to handle an exception.
- Spec sidecar files (design Q19): the contract surface lands in source first. Contracts put `Spec` calls in method bodies, so a team that can't reference `Warrant` pays that cost; see Open Questions.
- Lifted arithmetic on `int?` (`a + b` with nullable operands): not needed by the exit criterion or the surveyed methods. Revisit on the first real use.
- Collections, `Guid` and strings (design Q14, Q18, Q20): the payment example needs none. Q18's point that the most valuable real specs need them stands, and it is recorded for M7 planning.
- A standard contract for logging calls (Q20): needs string interpolation, M7.

#### Deferred to Follow-Up Work

- #47: model a `[Closed]` class's throwing construction in the effect monad. Today it is rejected as WRT0009. Modelling it means a throwing type initializer, which is separate from method effects.
- #48: check a closed class's own `Equals` against identity at verification time.
- #39, #40, #42: tactic improvements, independent of contracts.
- An analyzer code fix that rewrites an expression-bodied member to a block body so it can take a contract (Q17).

### Dependencies

- Lean toolchain v4.35.0 and lean4export `5a9a355`, as pinned in `scripts/lib/lean-toolchain.sh`. `Std` ships with the toolchain, so `lean/lake-manifest.json` needs no new package.
- `WARRANT_INIT_EXPORT` for the opt-in full-Init tests, as in M5b.
- The owner's uncommitted files are never staged: `.gitignore`, `compose.yaml`, `.claude/`, and mode-only changes under `scripts/`.

---

## Planning Contract

### Key Technical Decisions

**Lean library and bundle**

- KTD1. **`Std.Do` is the statement and proof vocabulary, not `Std.WP`.** `Std.Do`'s definitions and lemmas are stable in v4.35. Only their tactic is deprecated, and Warrant doesn't use it. `Std.WP` is marked experimental and changed in 4.35. The walker's structural rules (`Spec.bind`, `Spec.pure`, `Spec.throw_ExceptT`, the consequence rule) are named in one place in the walker, so a later move to `Std.WP` swaps names, not structure. Model-operation specs come from the sidecar (KTD15), not from that list.
- KTD2. **Std enters through bundle roots, not as a whole module.** `scripts/export-semantics.sh` exports roots plus closure, so only the `Std.Do` constants Warrant's models and generator mention are added. All of `Std.Do` would add 1,443 constants over Init, with no new axiom, `extern` or `implemented_by` (research: framework dossier §3). `SemanticsBundle.AxiomProblem` (#26) therefore holds unchanged. The pin file and sidecar are regenerated with the bundle, as their tests already require.
- KTD3. **The bundle stays a verified load unless the measured start time crosses 5 seconds.** M5b KTD19 deferred the choice between a verified load and a trusted store base to M6. U1 measures server start (2.9 s in the M5b baseline) with the Std closure, and U14 measures it again with the full M6 bundle. Above 5 s at either point, the work stops and asks, because a trusted base widens the trusted computing base (design §9).
- KTD4. **The effect monad is an abbreviation over Lean's transformers that threads an opaque world: `ClrM σ α := ExceptT ClrExn (StateM σ) α`, and every obligation quantifies over `σ : Type`.** `Std.Do`'s `WP`, `WPMonad` and `@[spec]` lemmas then apply with no instance proofs of Warrant's own (framework dossier §1). Model operations leave the state unchanged. External operations may read and change it, so two calls to the same dependency are unrelated unless a contract relates them. Without the world, a dependency would be a pure function of its arguments, and a proof could rely on two calls agreeing, which real stateful implementations break. `ClrExn` is an inductive with one constructor per exception the models raise (`overflow`, `divideByZero`, `nullReference`, `invalidOperation`), plus `thrown` carrying the thrown type's key, and `external` for an exception propagated from a dependency.
- KTD5. **Null is a value, not an effect.** `T?` is `Option T`. Reading `Value` of a null `int?`/`long?` raises `ClrExn.invalidOperation`, as `Nullable<T>.Value` does, and dereferencing a null reference raises `ClrExn.nullReference`. An `OptionT` layer would make null and "threw" one barrel in `Std.Do`'s postconditions.
- KTD6. **Division and remainder test their two throwing cases before calling Lean's operation.** C# `/` truncates, and Lean's `Int32.div` is `BitVec.sdiv`, which also truncates but returns 0 on a zero divisor and wraps `MinValue / -1`. The model raises `divideByZero` first and `overflow` for `MinValue / -1` and `MinValue % -1`, which the CLR throws even in unchecked code. Omega bridges state `toInt` of the result through `Int.tdiv`/`Int.tmod`.
- KTD7. **`decimal` is `sign × mantissa × 10^-scale` with a 96-bit natural mantissa and scale 0 to 28.** Equality and order compare the rational values, so `1.0m == 1.00m`. Addition and subtraction compute the exact result at the larger scale. When its mantissa needs more than 96 bits, they lower the scale and round half to even, as the CLR's decimal addition does, and raise `overflow` only when the result doesn't fit at scale 0. Multiplication, division and explicit rounding (M7) are not modelled. A VIR literal carries sign, mantissa and scale exactly. The model's definitions are trusted. Its lemmas are proved in Lean and re-checked by the kernel (design §6.2).

**Surface and extraction**

- KTD8. **`Spec.Requires`/`Ensures` are `[Conditional("WARRANT_CONTRACTS")]` calls that must lead a block body.** This follows `Spec.Decreases` (`src/Warrant/Spec.cs`, `Walker.Scripts.cs`), so they cost nothing at run time. An expression-bodied member takes no contract in M6 (design Q17). The analyzer says to use a block body, and the code fix is deferred.
- KTD9. **An external dependency is a theorem parameter, and its contract is a hypothesis (design D9).** For each contracted member a method uses, the obligation quantifies over an operation of the member's type in `ClrM`. It also takes the member's contract as a hypothesis triple. Dependencies come from `readonly` fields and never-assigned primary-constructor parameters of interface types that have a `[ContractFor]` class (design Q20 extends the readonly-field rule). Each dependency field or parameter a method uses gets a `NonNull` assumption, since calling through a null dependency would throw. Any other field read is still WRT0002 until M7's heap model.
- KTD10. **A contract class must be `file`/`internal`, `abstract`, implement exactly the interface it names, and contain only members of that interface.** Each member's body is either `Spec` calls followed by `return default!`, or the expression body `=> default!`, which assumes nothing about the result, as design §5.2's `SavePayment` does. Anything else is rejected with a named step, so a contract can't hide code that would run.
- KTD11. **A unit is translated into `ClrM` exactly when it can raise or calls something that can.** A unit can raise if it contains `throw`, checked arithmetic, `/` or `%` whose divisor isn't a constant other than 0 and -1, a nullable read, a modelled member that throws, an external call, or `await`. Every other unit keeps its M4 pure translation, so R14 holds by construction, and `year % 4` stays pure. The rule is computed over VIR in Semantics, per strongly connected component of the call graph, so extraction and translation can't disagree about it. Two cases are rejected in M6 with a named WRT0002:
  - a raising unit in a recursive component ("recursion with effects"), because its recursive call sits inside a `bind` and the decrease obligations (M5a) don't see through it;
  - a `[Theorem]` whose statement calls a raising unit, with a message that says to state the property as a `Spec.Ensures` on the method instead.

**Contracts and statements**

- KTD12. **A method's contract obligation is a `Std.Do` triple stated by the trusted translator.** Its precondition is the `Requires` conjunction. Its normal postcondition is the `Ensures` conjunction. Its exception postcondition allows only `ClrExn.thrown` (an explicit `throw`) and `ClrExn.external` (an exception propagated from a dependency). So the VCs must prove that no implicit runtime exception can happen: overflow, a zero divisor, a null dereference. For explicit throws and propagated exceptions this is partial correctness: `Ensures` holds on normal return, and a path that ends in such an exception satisfies it vacuously, so the report lists each such path (KTD20). The statement is the claim, so it lives in Semantics (trusted). Proving it is the engine's job (untrusted, design D11).
  - Every `[Verified]` unit gets an obligation if it has a contract, can raise (KTD11), or calls a unit that has a `Requires`. A missing `Requires` or `Ensures` defaults to `True`, so a contract-free method that divides still has to prove its divisor is never zero.
  - A pure unit's obligation is the triple over `pure (f params)`, so the walker and call sites use one shape.
  - A verified callee's proved triple is used at call sites as a lemma, and its precondition becomes a VC there.
- KTD13. **VC generation is a structural walker in C# (`Warrant.Engine`), not a port of `mvcgen`.** Warrant's translator emits a closed set of program shapes: `bind`, `pure`, `throw`, `ite`/`dite`, matchers on known VIR matchers, `let`, and calls to externals or verified units. The walker applies `Spec.bind`, `Spec.pure`, `Spec.throw_ExceptT` and the consequence rule along that structure, instantiating each external hypothesis at its call site with the current world. The kernel checks the resulting proof term, so the walker is untrusted. This copies the pattern of `PipelineScope.ProveDecrease`: Semantics builds the obligation, and the engine proves it.
- KTD14. **Leftover VCs go through a separate VC simp set, then omega.** The set is the `SPred` lemmas (`entails_nil`, `down_pure_nil` and others), `PredTrans.apply_*`, the model operations' equations and the M5a default set. It is kept apart from `Tactic.Simp()`'s default set, as omega-prep is (M5a KTD11, KTD13), so existing scripts don't change.
- KTD15. **`@[spec]` lemmas reach the engine through the sidecar, which is the only lookup for model-operation specs.** `tools/warrant-attrs/Main.lean` gains a `spec` kind (name, priority, triple or equation). `scripts/export-attributes.sh` imports `Std.Do`, and `src/Warrant.Meta/Attributes/Sidecar.cs` parses the kind. The sidecar format version goes to 2. The walker looks up model-operation specs by head constant. A DiscrTree is not needed, because the walker knows each node's head (KTD13).
- KTD16. **`Spec.Assert` splits the obligation at its position.** The fact is a VC proved by its script or by the default procedure, and it is assumed after that position. `[ProofFor(nameof(M))]` replaces the default procedure for `M`'s whole obligation with its script. The script starts at the triple, so `Tactic.VcGen()` is added for scripts that want the walker first.

**Engine, reports, testing**

- KTD17. **#41 is fixed before any division VC is attempted.** Every `MinValue / -1` guard mentions the folded `int.MinValue` literal, which omega currently treats as an opaque atom, so no division obligation would close.
- KTD18. **Contract failures name their source line through VIR node IDs.** This reuses M5b KTD7: each VC carries the node ID of the operation or `Spec` call that produced it, so a cached outcome renders at the current lines.
- KTD19. **VIR goes to version 3, additively.** New fields are optional, as in M5a's `statement`, `script` and `budget`. New node kinds and enum members are additive. Existing units hash and serialise exactly as before, and the schema version is in the closure hash, so caches invalidate themselves.
- KTD20. **New assumption kinds:** `ExternalContract` (a dependency member's contract), `CalleeContract` (a verified callee's proved triple), `MayThrow` (an explicit `throw` or propagated external exception the triple allows), each with report text. The existing `NonNull` kind covers nullable-reference annotations and each dependency field or parameter a method calls through (KTD9). Design Q11 is decided: annotations remain assumptions in M6.
- KTD21. **Differential tests run contract-satisfying mocks on both sides.** For each external member, a generator produces an implementation that satisfies its `Ensures`: a C# class on the CLR side, a lambda argument on the model side. Both runs must agree on the result or on the exception kind. This extends `tests/Warrant.Engine.Tests/Differential/` (design §10.5).
- KTD22. **Async is sequencing.** `Task<T>` maps to `ClrM T`. `await` of an external call or a verified method is `bind`. Any other `await`, `ConfigureAwait` or `Task` combinator is WRT0002. Cancellation tokens are opaque parameters with no model.
- KTD23. **Modelled BCL members are a table in Extraction, mapped to Warrant library definitions in Semantics.** The table holds `Math.Min`, `Math.Max` and `Math.Abs` for `int`, `long` and `decimal`. It fills the WRT0005 branch whose message already says "verified or modelled members" (`Walker.cs`). Adding a member means a table row, a library definition, a CLR-agreement row and a corpus entry.
- KTD24. **The M6 corpus is the exit criterion, as in M5a.** `tests/corpus/m6/` has `accepted/`, `refuted/` and `rejected/` with `expected.json`, including the payment example. `M6ExitTests` has one test per Success Criterion except the private-codebase one, which is checked by hand and reported in the pull request without naming its code. `scripts/cross-check.sh` gains an M6 row.

### High-Level Technical Design

Where contracts flow, with the trusted base boxed:

```mermaid
flowchart TB
  subgraph Source[C# source]
    M[Verified method with Spec.Requires and Spec.Ensures]
    C[ContractFor class]
    P[ProofFor method or Spec.Assert]
  end
  subgraph Trusted[Trusted: Frontend, Extraction, Vir, Semantics, Kernel]
    X[Extraction: effects, contracts, dependencies] --> V[VIR v3 units]
    V --> S[Semantics: effect inference KTD11, ClrM translation, triple obligation KTD12]
    S --> K[Kernel admits definitions and proofs]
  end
  subgraph Untrusted[Untrusted: Engine, Meta]
    G[VC walker KTD13] --> Q[VC simp set and omega KTD14]
  end
  L[Bundle: Init, Std.Do roots, Warrant models KTD2 KTD4 KTD7]
  M --> X
  C --> X
  P --> X
  S -- obligation --> G
  Q -- proof term --> K
  L --> S
  L --> K
  K --> R[Assumption report KTD20]
```

The obligation for a method `f` with one dependency member `get`, in the D9 shape. This is directional, not exact syntax:

```text
∀ (σ : Type) (get : Int32 → ClrM σ (Option Payment)) (id : Int32),
  (∀ x, ⦃fun _ => ⌜True⌝⦄ get x ⦃post⟨fun r _ => ⌜r = none ∨ r.id = x⌝, allowed⟩⦄) →   -- ExternalContract, every world
  ⦃fun _ => ⌜Requires f id⌝⦄ f get id ⦃post⟨fun r _ => ⌜Ensures f id r⌝, allowed⟩⦄        -- KTD12
where allowed e := e is ClrExn.thrown _ ∨ e is ClrExn.external _
```

The walker's case split over program shapes:

| Shape at the head of `wp⟦e⟧` | Rule applied | New goals |
|---|---|---|
| `pure v` | `Spec.pure` | postcondition at `v` |
| `bind x k` | `Spec.bind` | triple for `x` with intermediate postcondition from `k` |
| `throw e` | `Spec.throw_ExceptT` | exception postcondition at `e` (closes for `thrown`, fails for implicit) |
| `ite c t f` / `dite` | congruence | one goal per branch with `c` or `¬c` |
| known matcher | matcher congruence | one goal per alternative |
| external `op args` | instantiate its hypothesis at the current world, consequence rule | precondition VC, postcondition entailment |
| verified callee | its proved triple, consequence rule | callee `Requires` VC |
| model operation | its `@[spec]` lemma from the sidecar | side conditions (divisor ≠ 0) |
| anything else | stop | leftover VC to simp and omega |

### Output Structure

```text
lean/Warrant/
  Effect.lean          ClrExn, ClrM, throw helpers, spec lemmas (U3)
  Checked.lean         checked Int32/Int64 ops, div/rem with their throws, omega bridges (U2, U3)
  Nullable.lean        Option helpers for int?/long? (U3)
  Decimal.lean         the decimal model and its lemmas (U4)
  Math.lean            Math.Min/Max/Abs models (U3, U4)
src/Warrant/
  Spec.cs              Requires, Ensures, Assert (U5)
  Contracts.cs         ContractFor, ProofFor (U5)
src/Warrant.Engine/Contracts/
  VcWalker.cs          KTD13 (U11)
  VcSimpSet.cs         KTD14 (U11)
tests/corpus/m6/       accepted, refuted, rejected, expected.json, README.md (U14)
docs/m6/               chapters 01-08 and README (U15)
```

### Alternative Approaches Considered

- **Port `mvcgen` (about 4.8k lines of Lean meta code, plus `SPred` proof mode and matcher splitting).** Rejected: it is deprecated upstream, and Warrant's translator already knows every program shape it emits (KTD13).
- **Simp-only pipeline over `Std.Do`'s `@[simp]` `wp` equations (framework dossier option A).** It works for straight-line code, but simp can't apply an external hypothesis triple at a call site. KTD13 is that missing step, and simp stays for the leftovers.
- **Warrant's own `wp` calculus with plain `Prop`s, no `Std.Do` (option C).** It has the smallest trusted closure, but every library lemma would have to be re-proved, and the statements wouldn't read as standard Lean triples. It is the fallback if `ULift Prop` defeats omega (stop condition).
- **Monadic translation for every unit.** Rejected: it would change every M4 and M5a declaration and break R14 for no gain (KTD11).

### Risks

| Risk | Mitigation |
|---|---|
| `Std.Do`'s universe-polymorphic `SVal`/`SPred` recursion is new kernel work for the port | U1 admits the closure with the verified load and cross-checks it before anything depends on it |
| `ULift Prop` assertions leave VCs omega can't read | KTD14's `SPred` simp lemmas first; the stop condition and Alternative C if they fail |
| The decimal model disagrees with the CLR on scale after add/subtract | U4's agreement rows include equal values with different scales and every scale boundary |
| Effect inference makes a pure unit monadic and changes its declarations | KTD11 plus R14's corpus check: accepted M4 and M5a members must translate byte for byte, and rejected members change only as the M6 corpus README lists |
| `Warrant.Meta`'s `Apply` has never unified universe-polymorphic `PostCond`/`Assertion` terms | U3's checkpoint obligation exercises `Spec.bind`, `Spec.pure` and the consequence rule through `Apply` before Phase C |
| `MinValue % -1` throwing is pinned on one runtime and architecture | The C# spec ties it to `x / y` throwing; the agreement rows pin it, and another platform that differs shows as a failing row there |
| Trusted extraction grows by several constructs at once | One construct family per unit (U7, U8), each with rejected-corpus members and analyzer parity |
| The walker builds an ill-typed term on an unexpected shape | Anything unrecognised becomes a leftover VC, never a guessed rule; the kernel rejects a bad term as WRT0010 |
| Server start time grows past the baseline | KTD3's threshold and U14's baseline measurement |

### Open Questions

Deferred, not blocking. Each is the owner's call:
- Design Q14: which milestone takes collections, or whether they become a non-goal. Design §11's M7 row lists strings but not collections, and Q14 asks for a decision before M6. U15 records the owner's decision.
- Design Q19: whether spec sidecars come in a named milestone. An in-house translator already chose comments to avoid the `Warrant` dependency.

### Assumptions

Agent bets this plan was written under, not confirmed by the owner:
- Contracts are total about implicit runtime exceptions and partial about explicit `throw` and propagated external exceptions (KTD12). A method that throws explicitly on every path verifies against any `Ensures`, and the report lists each throwing path. Making explicit throws fail instead would reject ordinary argument validation.
- Design Q5 (an external-call trace) is out of M6. Q11 is decided as "nullable annotations remain assumptions". Q17 is decided as "block bodies only, code fix later". Q19 (sidecars) is out of M6.
- Collections, strings and `Guid` stay out of M6 despite Q18, because the exit criterion doesn't need them.
- Lifted nullable arithmetic is out of M6.
- 5 seconds of server start is the line between a verified load and a trusted Std base (KTD3).
- The real-code success criterion counts only candidates whose blockers are R1 to R4.

---

## Implementation Units

| U-ID | Phase | Title | Files touched (primary) | Depends on |
|---|---|---|---|---|
| U1 | A | Std.Do in the bundle, sidecar and pins | `lean/`, `scripts/export-*.sh`, `tools/warrant-attrs/Main.lean`, `src/Warrant.Meta/Attributes/Sidecar.cs`, `src/Warrant.Engine/PinnedDeclarations.ndjson.gz` | none |
| U2 | A | Omega and truncating division (#41) | `src/Warrant.Meta/Tactic/Omega/`, `lean/Warrant/Checked.lean` | U1 |
| U3 | A | Effect monad and CLR models | `lean/Warrant/Effect.lean`, `Nullable.lean`, `Math.lean`, `tests/Warrant.Semantics.Tests/ClrAgreementTests.cs` | U1, U2 |
| U4 | A | Decimal model | `lean/Warrant/Decimal.lean`, `tests/Warrant.TestSupport/Generators.cs` | U3 |
| U5 | B | Contract surface in `Warrant` | `src/Warrant/Spec.cs`, `src/Warrant/Contracts.cs`, `src/Warrant/Tactic.cs` | none |
| U6 | B | VIR version 3 | `src/Warrant.Vir/` | none |
| U7 | B | Extraction: effects and models | `src/Warrant.Extraction/Walker.cs`, `TypeChecks.cs` | U6 |
| U8 | B | Extraction: contracts and dependencies | `src/Warrant.Extraction/`, `src/Warrant.Analyzers/` | U5, U6 |
| U9 | C | Monadic translation | `src/Warrant.Semantics/` | U3, U4, U7 |
| U10 | C | Contract obligations | `src/Warrant.Semantics/`, `src/Warrant.Engine/PipelineScope.cs` | U8, U9 |
| U11 | C | VC walker and default procedure | `src/Warrant.Engine/Contracts/`, `src/Warrant.Engine/TacticRunner.cs` | U1, U10 |
| U12 | C | Contract assumptions in the report | `src/Warrant.Engine/Reports/` | U10 |
| U13 | D | Differential tests for effects and mocks | `tests/Warrant.Engine.Tests/Differential/` | U9, U11 |
| U14 | D | M6 corpus, cross-check and exit tests | `tests/corpus/m6/`, `scripts/cross-check.sh`, `tests/Warrant.Cli.Tests/M6ExitTests.cs` | U11, U12, U13 |
| U15 | D | Documentation | `docs/design.md`, `docs/m6/`, `docs/proving/` | U14 |

Phase A builds and proves the Lean side. B is independent of A and of itself, except that U8 needs U5. C needs both A and B. D closes the milestone.

```mermaid
flowchart TB
  U1 --> U2 --> U3 --> U4
  U5 --> U8
  U6 --> U7
  U6 --> U8
  U3 & U4 & U7 --> U9
  U8 & U9 --> U10
  U1 & U10 --> U11
  U10 --> U12
  U9 & U11 --> U13
  U11 & U12 & U13 --> U14 --> U15
```

### U1. Std.Do in the bundle, sidecar and pins

- **Goal:** the bundle contains the `Std.Do` constants M6 needs, admitted by the verified load, cross-checked, with their `@[spec]` attributes in the sidecar.
- **Requirements:** R13 (KTD1, KTD2, KTD3, KTD15).
- **Dependencies:** none.
- **Files:**
  - `lean/Warrant.lean`, `lean/Warrant/Effect.lean` (stub importing `Std.Do.Triple.Basic`, `Std.Do.WP.Monad`, `Std.Do.WP.SimpLemmas` and the spec lemmas used)
  - `lean/bundle-roots.txt` (a `Std.Do` section naming its KTD)
  - `scripts/export-attributes.sh` (module list adds `Std.Do`), `tools/warrant-attrs/Main.lean` (`spec` kind)
  - `src/Warrant.Meta/Attributes/Sidecar.cs` (format 2, `spec` entries)
  - `tests/data/warrant-semantics.ndjson.gz`, `tests/data/warrant-attributes.ndjson.gz`, `tests/data/README.md`, `src/Warrant.Engine/PinnedDeclarations.ndjson.gz` (regenerated)
  - `tests/Warrant.Engine.Tests/SemanticsBundleTests.cs`, `tests/Warrant.Meta.Tests/` (sidecar), `tests/Warrant.Lean4Export.Tests/ReaderCorpusTests.cs` (counts)
- **Approach:**
  1. Add the imports and roots. Run `scripts/export-semantics.sh`, then `scripts/pin-kernel-declarations.cs`, then the attributes export.
  2. Measure the added constants, bundle load time and server start with `scripts/measure-m5b.sh`. Record them in `tests/data/README.md`. Apply KTD3's threshold.
  3. Run the existing cross-check bundle step so Lean's kernel replays the new bundle.
- **Patterns to follow:** the M5a omega and simp root sections in `lean/bundle-roots.txt`. The sidecar's existing kinds and `getModuleEntries` loop in `tools/warrant-attrs/Main.lean`.
- **Test scenarios:**
  - `SemanticsBundle.Load` admits the new bundle, and `AxiomProblem` finds only the three standard axioms.
  - The embedded pin file equals `PinnedClosure` of the new bundle.
  - The sidecar parses with `spec` entries, each naming a bundle constant. A format-1 sidecar is rejected with a message naming the version.
  - Every root in `bundle-roots.txt` is in the bundle (`BundleTests.EveryRootIsInTheBundle`).
  - All M4 and M5a corpus tests pass unchanged.
- **Verification:** the bundle's constant count, load time and start time are recorded, start time is under KTD3's threshold, and `scripts/cross-check.sh` agrees.

### U2. Omega and truncating division (#41)

- **Goal:** omega sees through the folded `int.MinValue` literal, and `toInt` of `Int32`/`Int64` division and remainder reaches omega through `Int.tdiv`/`Int.tmod`.
- **Requirements:** R1, R11 (KTD6, KTD17).
- **Dependencies:** U1.
- **Files:**
  - `src/Warrant.Meta/Tactic/Omega/` (literal atom handling for #41)
  - `lean/Warrant/Checked.lean` (bridging lemmas), `lean/bundle-roots.txt` (omega-prep section)
  - `tests/Warrant.Meta.Tests/` (omega), `tests/corpus/m5a/` (an #41 regression member if one fits)
- **Approach:**
  1. Reproduce #41's goal and fix the literal so omega normalises it like any other numeral.
  2. Prove in Lean the bridges for `Int32.div`, `Int32.mod`, `Int64.div` and `Int64.mod` under the KTD6 side conditions, and add them to the omega-prep set.
- **Patterns to follow:** M5a's `Int32`/`Int64` → `Int` bridging set and its root section.
- **Test scenarios:**
  - #41's original goal closes with omega.
  - `x / 2 <= x` for nonnegative `int x`, stated over the model, closes with simp then omega.
  - `x % 3` is in `-2..2` closes.
  - A goal that needs `MinValue / -1` to be excluded fails without the side condition and closes with it.
- **Verification:** #41's repro closes, and the M5a corpus proves as before.

### U3. Effect monad and CLR models

- **Goal:** `ClrM`, `ClrExn` and the models of checked arithmetic, division, remainder, nullable reads and `Math.*` on `int`/`long` exist in the library, with spec lemmas, and agree with the CLR.
- **Requirements:** R1, R2, R4, R5 (KTD4, KTD5, KTD6, KTD23).
- **Dependencies:** U1, U2.
- **Files:**
  - `lean/Warrant/Effect.lean`, `lean/Warrant/Checked.lean`, `lean/Warrant/Nullable.lean`, `lean/Warrant/Math.lean`, `lean/bundle-roots.txt`
  - `src/Warrant.Semantics/Init.cs` (new constants)
  - `tests/Warrant.Semantics.Tests/ClrAgreementTests.cs`, `tests/Warrant.TestSupport/Generators.cs`
- **Approach:**
  1. Define `ClrExn` and `ClrM`, and prove `@[spec]` lemmas for each model operation, stating when it throws and what it returns otherwise.
  2. Add agreement rows whose expected result is a value or an exception kind. A CLR throw maps to `Except.error` with the matching `ClrExn`.
  3. Checkpoint for KTD13 and KTD14: write U11's `Ratio` obligation by hand as a `Std.Do` triple, apply `Spec.bind`, `Spec.pure` and the consequence rule through `Warrant.Meta`'s `Apply`, close the leftovers with Warrant's simp (KTD14's lemma list) and omega, and admit the term with the C# kernel. If this fails, stop (Goal Capsule) before Phase C.
- **Patterns to follow:** `ArithmeticRow` and `ComparisonRow` in `ClrAgreementTests.cs`. The `Warrant.Clr.*` files in `lean/Warrant/`.
- **Test scenarios:**
  - Checked `int` add, subtract, multiply and negate agree on every boundary pair, including `MaxValue + 1` throwing `overflow`.
  - `/` and `%` agree on every boundary pair: `x / 0` raises `divideByZero`, and `MinValue / -1` and `MinValue % -1` raise `overflow`.
  - Truncation agrees on negative operands: `-7 / 2 == -3`, `-7 % 2 == -1`.
  - `Math.Abs(int.MinValue)` raises `overflow`, and `Math.Min`/`Max` agree on random pairs.
  - `int?` `Value` on null raises `invalidOperation`, and `??` and `GetValueOrDefault` agree.
  - 150 random cases per row with the pinned seed.
  - The checkpoint obligation is admitted by the C# kernel.
- **Verification:** every row passes under the kernel, `BundleTests` finds each new constant in the roots, and the checkpoint obligation is proved.

### U4. Decimal model

- **Goal:** the minimal `decimal` model exists and agrees with the CLR (Q1 decided for M6).
- **Requirements:** R3, R4, R5 (KTD7, KTD23).
- **Dependencies:** U3.
- **Files:**
  - `lean/Warrant/Decimal.lean`, `lean/Warrant/Math.lean` (`Math.Abs`, `Min`, `Max` on decimal), `lean/bundle-roots.txt`
  - `src/Warrant.Semantics/Init.cs`
  - `tests/Warrant.Semantics.Tests/ClrAgreementTests.cs`, `tests/Warrant.TestSupport/Generators.cs` (decimal generator)
- **Approach:**
  1. Define the representation, a literal constructor from sign, mantissa and scale, equality and order by value, and add and subtract with rescaling and the 96-bit overflow check.
  2. Prove that equality is an equivalence, that order is total, and the lemmas the VC simp set needs (for example, `a - b < a` when `b > 0` and no overflow).
  3. Add a generator that biases toward scale boundaries, `decimal.MaxValue`, `MinValue`, zero with different scales, and pairs equal by value with different scales.
- **Patterns to follow:** U3's rows. The literal encoder tests for `int`/`long`.
- **Test scenarios:**
  - `1.0m == 1.00m` is true in the model and on the CLR.
  - `decimal.MaxValue + 1m` raises `overflow`.
  - `9m + 0.0000000000000000000000000001m` and `decimal.MaxValue - 0.5m` round as the CLR does, with no exception.
  - `0.1m + 0.2m == 0.3m`, and the result's scale matches the CLR's.
  - Comparisons agree on random pairs, including negative values and zeros with different scales.
  - `Math.Abs` agrees on random values.
  - A literal round-trips through the encoder for every scale 0 to 28.
- **Verification:** every decimal row passes, and the model's lemmas are kernel-checked in the bundle.

### U5. Contract surface in `Warrant`

- **Goal:** the user API has `Spec.Requires`, `Spec.Ensures`, `Spec.Assert`, `[ContractFor]`, `[ProofFor]` and `Tactic.VcGen()`.
- **Requirements:** R6, R7, R10 (KTD8, KTD16).
- **Dependencies:** none.
- **Files:**
  - `src/Warrant/Spec.cs`, `src/Warrant/Contracts.cs`, `src/Warrant/Tactic.cs`
  - `tests/Warrant.Analyzers.Tests/` (API surface on Roslyn 4.8 too)
- **Approach:**
  1. Add the void members as `[Conditional("WARRANT_CONTRACTS")]`. `Ensures<T>(Func<T, bool>)` handles value returns, and `Ensures(Func<bool>)` handles `void` and `Task` returns.
  2. Add the attributes with XML docs that say which milestone runs them.
- **Patterns to follow:** `Spec.Decreases` and `[Theorem]`.
- **Test scenarios:**
  - A build without `WARRANT_CONTRACTS` emits no call to the `Spec` members (IL check).
  - The package still targets netstandard2.0 and builds under Roslyn 4.8.
- **Verification:** the API builds with warnings as errors, and the analyzer tests pass on both Roslyn versions.

### U6. VIR version 3

- **Goal:** VIR can carry M6's types, operations, effects and contracts, additively.
- **Requirements:** R1 to R10 (KTD19).
- **Dependencies:** none.
- **Files:**
  - `src/Warrant.Vir/` (types: decimal, nullable, task; operators: `Div`, `Rem`, checked allowed; nodes: `throw`, null literal and null tests, `await`, external call, modelled-member call, `requires`, `ensures`, `assert`; a contract unit kind; the KTD20 assumption kinds; decimal literals)
  - `src/Warrant.Vir/VirWriter.cs`, the reader, `VirHash.cs`
  - `tests/Warrant.Vir.Tests/`
- **Approach:**
  1. Add each form with optional fields, so a version-2 unit writes byte-identically.
  2. Bump `VirUnit.CurrentVersion` to 3.
  3. Extend the round-trip samples with one unit per new form.
- **Patterns to follow:** M5a's optional `statement`, `script` and `budget` fields. M5b's `ReferencedSource` assumption kind.
- **Test scenarios:**
  - Every new node round-trips through writer and reader.
  - Every M4 and M5a corpus unit hashes the same apart from the version, and serialises byte-identically.
  - A decimal literal with 28 digits of scale round-trips exactly.
  - A version-4 unit is rejected with a message naming the version.
- **Verification:** the VIR tests pass, and no M4 or M5a expectation changes.

### U7. Extraction: effects and models

- **Goal:** extraction accepts `throw`, checked arithmetic, `/`, `%`, nullable values, `decimal` and the modelled `Math` members, and still rejects the rest with a named construct.
- **Requirements:** R1 to R4, R14 (KTD5, KTD6, KTD7, KTD23).
- **Dependencies:** U6.
- **Files:**
  - `src/Warrant.Extraction/Walker.cs`, `src/Warrant.Extraction/TypeChecks.cs`, `src/Warrant.Extraction/ExtractionResult.cs` (diagnostic texts)
  - `src/Warrant.Extraction/ModelledMembers.cs` (KTD23 table)
  - `tests/Warrant.Extraction.Tests/`, `tests/Warrant.Analyzers.Tests/CorpusParityTests.cs`
- **Approach:**
  1. Replace each M6 rejection site that the research table lists (`Walker.cs` `MapType`, `Binary`, `Arithmetic`, the `throw` statement and expression sites, conversions) with the VIR form. Keep the rest rejected.
  2. `throw` takes only `new T(...)` of an exception type with constant or parameter arguments. The thrown type's key goes into the node for `ClrExn.thrown`. `try` stays rejected (Scope Boundaries).
- **Patterns to follow:** the M4 operator mapping in `Walker.Arithmetic`. The construct-string conventions in `ExtractionResult.cs`.
- **Test scenarios:**
  - Each newly accepted construct produces its VIR node: `checked(a + b)`, `a / b`, `a % b`, `throw new ArgumentException("x")`, `x ?? 0`, `x.Value`, `1.25m + d`, `Math.Max(a, b)`.
  - `try`/`catch`, `finally`, `throw;`, lifted `a + b` on `int?`, and `Math.Round` are still rejected with their names.
  - A `CheckForOverflowUnderflow` project's `+` is accepted as checked.
  - Every accepted M4 and M5a member extracts identically, and analyzer parity holds for the new members.
- **Verification:** extraction and analyzer parity tests pass, every accepted M4 and M5a member extracts unchanged, and rejected members change only as the M6 corpus README lists (R14).

### U8. Extraction: contracts and dependencies

- **Goal:** extraction reads `Spec.Requires`/`Ensures`/`Assert`, `[ContractFor]` classes, `[ProofFor]` methods, dependencies, `async` and instance methods whose only state is their dependencies.
- **Requirements:** R6 to R10 (KTD8, KTD9, KTD10, KTD16, KTD22).
- **Dependencies:** U5, U6.
- **Files:**
  - `src/Warrant.Extraction/Walker.Scripts.cs` (contract calls), `src/Warrant.Extraction/Extractor.cs` (contract units, dependency discovery), `src/Warrant.Extraction/TypeChecks.cs` (contract class shape)
  - `src/Warrant.Analyzers/` (same diagnostics as you type)
  - `tests/Warrant.Extraction.Tests/`, `tests/Warrant.Analyzers.Tests/`
- **Approach:**
  1. `Requires`/`Ensures` must be the leading statements of a block body, as `Decreases` is (`Extractor.cs` first-statement check). Anywhere else, or on an expression-bodied member, is a WRT0002 that says to use a block body.
  2. A `[ContractFor(typeof(I))]` class is checked against KTD10 and becomes one contract unit per interface member.
  3. In an instance method, `this.f.M(...)` is an external call when `f` is a `readonly` field or never-assigned primary-constructor parameter of a contracted interface type. The dependency becomes a unit parameter. Every other member access on `this` stays rejected.
  4. `await` follows KTD22. `[ProofFor(nameof(M))]` attaches its script to `M`'s obligation.
- **Patterns to follow:** `IsDecreases`/`DecreasesNotFirst` in `Walker.Scripts.cs`. `ForAllExpr` for the lambda in `Ensures<T>(r => ...)`. The closed-shape step reporting for KTD10.
- **Test scenarios:**
  - `ProcessPayment` from design §5.2 extracts with `store`'s two members as dependencies and the contract class's `Ensures` as their contracts.
  - `Spec.Ensures` after another statement is rejected with "must lead the body".
  - A contract class with a member body that isn't `Spec` calls plus `return default!` is rejected, naming the step.
  - A contract class that implements a second interface is rejected.
  - A mutable field of a contracted type is rejected. So is a primary-constructor parameter that is reassigned.
  - `await Task.Delay(1)` is rejected. `await store.GetPayment(id)` is accepted.
  - `[ProofFor(nameof(Missing))]` is rejected, naming the missing method.
- **Verification:** extraction and analyzer tests pass, and the payment example extracts with the expected units.

### U9. Monadic translation

- **Goal:** units that can raise translate to `ClrM` programs, and all other units translate exactly as before.
- **Requirements:** R1 to R4, R9, R14 (KTD4, KTD11, KTD22).
- **Dependencies:** U3, U4, U7.
- **Files:**
  - `src/Warrant.Semantics/BodyTranslator.cs`, `Statements.cs`, `Operators.cs`
  - `src/Warrant.Semantics/Effects.cs` (KTD11 inference), `src/Warrant.Semantics/MonadicStatements.cs`
  - `tests/Warrant.Semantics.Tests/`
- **Approach:**
  1. Compute raise-ability over VIR per strongly connected component of the call graph, and reject KTD11's two cases.
  2. For a raising unit, a second statement translator emits `bind`, `pure` and `throw`, keeping join points (docs/m4/05's note on M6). Eager logical operators keep both operands' effects in order, and short-circuit forms bind only the evaluated side.
  3. A pure value used in a monadic context is lifted with `pure`. A pure caller of a raising callee becomes raising itself.
- **Patterns to follow:** the CPS rules and placement in `Statements.cs`. `LocalContext` closing with `MkLambda`/`MkPi`.
- **Test scenarios:**
  - A method with only `int` arithmetic translates to the same declaration as in M5a.
  - `a / b` translates to the KTD6 operation in `ClrM`, and the kernel evaluates it to `Except.error divideByZero` for `b = 0`.
  - `x && F(y)` with a raising `F` doesn't evaluate `F` when `x` is false, and `x & F(y)` does.
  - A pure method calling a raising one becomes raising, and its declaration type is `ClrM`.
  - `throw new ArgumentException()` evaluates to `Except.error (thrown key)`.
  - `year % 4 == 0` stays a pure translation.
  - A recursive `Gcd(b, a % b)` is rejected as recursion with effects.
  - A `[Theorem]` whose statement calls a raising method is rejected, and the message points to `Spec.Ensures`.
  - A method calling an external dependency twice threads the world, and the kernel evaluates it with a mock that returns a different value on each call.
  - Every M4 and M5a translation is byte-identical.
- **Verification:** the Semantics tests and the M4 and M5a corpora pass unchanged.

### U10. Contract obligations

- **Goal:** each verified method with a contract gets a trusted triple obligation in the D9 shape, and verified callees' triples become lemmas at call sites.
- **Requirements:** R6 to R8, R10 (KTD9, KTD12, KTD16).
- **Dependencies:** U8, U9.
- **Files:**
  - `src/Warrant.Semantics/Contracts.cs` (statement construction), `src/Warrant.Semantics/LeanNames.cs` (`$contract`, `$contract_spec`)
  - `src/Warrant.Semantics/Translator.cs` (`TranslatedUnit` gains obligations)
  - `src/Warrant.Engine/PipelineScope.cs` (admission order and caching of obligations, like decrease proofs)
  - `tests/Warrant.Semantics.Tests/`, `tests/Warrant.Engine.Tests/`
- **Approach:**
  1. Build the triple from `Requires`, `Ensures` and the KTD12 exception postcondition, binding one operation and one hypothesis per dependency member (KTD9).
  2. Each `Spec.Assert` becomes its own obligation at its position, assumed afterwards (KTD16).
  3. Admit a proved obligation as the unit's spec lemma, which call sites use (KTD12). A unit whose obligation fails is not usable as a lemma, and its callers report "depends on an unproved contract".
- **Patterns to follow:** `DecreaseObligation` and `TheoremShell` in `Recursion.cs`. `ProveDecrease` admission and caching in `PipelineScope.cs`.
- **Test scenarios:**
  - `ProcessPayment`'s obligation has two operation binders, two hypotheses and the expected pre- and postcondition. This is compared with a hand-written statement in a test.
  - A method with `Requires` and no `Ensures` gets a triple with postcondition `True`, which still proves the absence of implicit exceptions.
  - A caller of a method with `Requires(x > 0)` gets a VC for `x > 0` at the call, even when the caller has no contract of its own.
  - A contract-free method with an unguarded `a / b` gets a `True`/`True` obligation that fails at the `/` line.
  - A pure method with `Ensures` gets a triple over `pure`, and a caller uses it as a lemma.
  - An obligation that fails makes its callers report the dependency, not a second goal.
- **Verification:** obligations are admitted and cached like decrease proofs, and a changed `Ensures` invalidates the cache entry.

### U11. VC walker and default procedure

- **Goal:** contract obligations without a script are proved by KTD13's walker, then the VC simp set, then omega, and failures report the source line of the failing VC.
- **Requirements:** R10, R11 (KTD13, KTD14, KTD15, KTD18).
- **Dependencies:** U1, U10.
- **Files:**
  - `src/Warrant.Engine/Contracts/VcWalker.cs`, `src/Warrant.Engine/Contracts/VcSimpSet.cs`, `src/Warrant.Engine/Contracts/SpecTable.cs` (lemma names by head, KTD1)
  - `src/Warrant.Engine/TacticRunner.cs` (`vcgen` handler), `src/Warrant.Engine/PipelineScope.cs` (default procedure)
  - `src/Warrant.Meta/Display/Notation.cs` (triples and `wp` in goal display)
  - `tests/Warrant.Engine.Tests/`
- **Approach:**
  1. Walk the program as the HLTD table lists, building the proof term with `Apply` and recording the node ID that produced each leftover VC.
  2. Run the VC simp set on each leftover, then omega. Budgets are the D14 ones per obligation.
  3. Report the first failing VC as WRT0001 at its node, with the goal printed through the notation.
- **Patterns to follow:** `ProveDecrease`. `TacticM.LiftMetaTactic` for the `vcgen` handler.
- **Test scenarios:**
  - `int Ratio(int a, int b) { Spec.Requires(b != 0 && b != -1); return a / b; }` proves. Without the `Requires` it fails at the `/` line with a goal that needs `b ≠ 0`.
  - `checked(a + b)` with `Requires(a < 1000 && b < 1000)` proves no overflow.
  - An external call's postcondition is used: `ProcessPayment`'s `payment.Id == paymentId` follows from `GetPayment`'s contract.
  - A division whose divisor may be zero proves when it is reached only if `Requires` is violated, and fails at its line otherwise.
  - An explicit `throw` reachable on any path proves, and the report lists it as `MayThrow`.
  - A `null` dereference of a nullable value guarded by `is not null` proves, and an unguarded one fails at its line.
  - A shape the walker doesn't know becomes a leftover VC, not an exception.
  - Running out of budget reports WRT0006.
- **Verification:** the payment example's obligation proves under the default procedure, and each failure scenario reports the right line.

### U12. Contract assumptions in the report

- **Goal:** the assumption report has design §8.4's contract sections, in Markdown and JSON.
- **Requirements:** R12 (KTD20).
- **Dependencies:** U10.
- **Files:**
  - `src/Warrant.Engine/Reports/AssumptionReport.cs`, `MarkdownReport.cs`, `JsonReport.cs`
  - `tests/Warrant.Engine.Tests/ReportTests.cs`
- **Approach:**
  1. Render each KTD20 kind with its text: the dependency member and its contract, the callee and its triple, and each allowed exception site.
  2. Widen the global `BundleModels` text to the M6 models.
- **Patterns to follow:** the existing kinds' text table at `AssumptionReport.cs` and the JSON round trip.
- **Test scenarios:**
  - `ProcessPayment`'s report lists `IPaymentStore.GetPayment`'s and `SavePayment`'s contracts under "Assumed (contracts)", and that `store` is not null.
  - A method that throws `ArgumentException` lists the throw site.
  - Every new kind round-trips through JSON.
- **Verification:** report tests pass, and the payment example's Markdown report matches a checked-in expected file.

### U13. Differential tests for effects and mocks

- **Goal:** every accepted M6 function agrees between the CLR and the model on results and exception kinds, with dependencies replaced by contract-satisfying mocks.
- **Requirements:** R1 to R5, R8 (KTD21).
- **Dependencies:** U9, U11.
- **Files:**
  - `tests/Warrant.Engine.Tests/Differential/` (exception mapping, mock generation), `tests/Warrant.Engine.Tests/Differential/README.md`
  - `tests/Warrant.TestSupport/Generators.cs`
- **Approach:**
  1. Map a CLR exception to its `ClrExn` constructor and compare kinds.
  2. For each external member, generate implementations that satisfy its `Ensures` (on the CLR, a class; in the model, a lambda), and run both sides with the same choices.
- **Patterns to follow:** `AgreesOnEveryBoundaryCombination`, `AgreesOnRandomInputs` and `ModelCheck`.
- **Test scenarios:**
  - Every accepted M6 corpus function agrees on every boundary combination.
  - `ProcessPayment` agrees for mocks that return `null`, a matching payment, and one whose status isn't pending.
  - A function that divides agrees on `divideByZero` for a zero argument.
  - 1,000 random inputs per function with the pinned seed.
- **Verification:** the differential suite passes, and its README's cost table includes the M6 corpus.

### U14. M6 corpus, cross-check and exit tests

- **Goal:** the M6 corpus, including the payment example, passes end to end, Lean's kernel accepts its certificates, and each Success Criterion is a test.
- **Requirements:** R11, R13, R14 and the Success Criteria (KTD3, KTD24).
- **Dependencies:** U11, U12, U13.
- **Files:**
  - `tests/corpus/m6/accepted/`, `refuted/`, `rejected/`, `expected.json`, `README.md`
  - `tests/Warrant.Extraction.Tests/CorpusTests.cs`, `tests/Warrant.Engine.Tests/CorpusTests.cs`, `tests/Warrant.Analyzers.Tests/CorpusParityTests.cs`, `tests/Warrant.TestSupport/CorpusCompilations.cs`
  - `scripts/cross-check.sh` (M6 row), `scripts/measure-m5b.sh` (start time and memory with the M6 bundle)
  - `tests/Warrant.Cli.Tests/M6ExitTests.cs`
- **Approach:**
  1. Write the corpus: the payment example and its pure parts in `accepted/`; contracts that are false in `refuted/`, with the failing line and goal in `expected.json`; and deferred constructs in `rejected/`. It includes:
     - refuted: a method that calls `GetPayment(id)` twice and ensures the results are equal; a contract-free method with an unguarded `/`; a caller that passes 0 to a method that requires a non-zero argument;
     - accepted: a method that throws on every path, with its expected `MayThrow` report; `year % 4` in a pure method;
     - rejected: `try`/`catch`, a `%`-based recursive `Gcd`, a `[Theorem]` that calls a raising method.
  2. Add the cross-check row, which verifies with `--out`, has Lean replay it, and tampers with a proof so both kernels reject it.
  3. Record start time and memory against the M5b baseline, and apply KTD3's threshold again with the full M6 bundle.
- **Patterns to follow:** `tests/corpus/m5a/` and `M5bExitTests`.
- **Test scenarios:**
  - One `M6ExitTests` fact per Success Criterion, except the private-codebase one (KTD24).
  - Each refuted member reports WRT0001 at the expected line with the expected goal.
  - Each rejected member reports its construct.
  - The cross-check row ends with "all verdicts agree".
- **Verification:** `dotnet test --filter M6Exit` and `scripts/cross-check.sh` pass, and the baselines are recorded.

### U15. Documentation

- **Goal:** the design, the M6 chapters and the proving guide describe what M6 built.
- **Requirements:** all (KTD1 to KTD24).
- **Dependencies:** U14.
- **Files:**
  - `docs/design.md` (§11 M6 row marked done with evidence; §12 Q1, Q5, Q8, Q11, Q14, Q17, Q18, Q19 and Q20 updated with what M6 decided or the owner decided; §6.1 type table)
  - `docs/m6/README.md` and chapters (Std closure and sidecar, effect monad and models, decimal, extraction, monadic translation, contract obligations, VC generation, reports and testing)
  - `docs/proving/reference.md`, `docs/proving/how-to.md` (M6 rows marked as running), `REPRODUCING.md`, `README.md` status line
- **Approach:** write each chapter from the code and KTDs, citing IDs, as the M5b chapters do.
- **Test expectation:** none, documentation only. The Definition of Done's agreement check covers it.
- **Verification:** every KTD is cited by a chapter, and the design's §11 row names the evidence.

---

## Verification Contract

| Gate | Command or check | Proves |
|---|---|---|
| Build | `dotnet build` | All projects build with warnings as errors, including netstandard2.0 `Warrant` and the analyzers. |
| Tests | `dotnet test` | U1 to U13's unit, model, extraction, translation, engine and report tests, with no Lean toolchain installed. |
| CLR agreement | `dotnet test --filter ClrAgreement` | R5 (U3, U4). |
| Differential | `dotnet test --filter Differential` | U13, with `WARRANT_PBT_SEED` pinned. |
| Exit | `dotnet test --filter M6Exit` | The Success Criteria (U14). |
| Init store | `WARRANT_INIT_EXPORT=<path> dotnet test --filter InitStore` | The full-Init tests still pass with the M6 bundle. |
| Build integration | `WARRANT_BUILD_INTEGRATION=1 dotnet test tests/Warrant.Build.Tests` | Contracts verify under `dotnet build`, VS 2026 and VS 2022 MSBuild. |
| Cross-check | `scripts/cross-check.sh` | R13: Lean's kernel accepts the M6 certificates and the bundle; ends with "all verdicts agree". |
| Bundle | `scripts/export-semantics.sh`, `scripts/pin-kernel-declarations.cs`, `scripts/export-attributes.sh` | The committed bundle, pins and sidecar are reproducible (U1). |
| Baselines | `scripts/measure-m5b.sh` | Start time and memory with the M6 bundle against KTD3's threshold. |

---

## Definition of Done

- Every unit's Verification holds, and every gate in the Verification Contract passes.
- Each Success Criterion holds, item by item. The private-codebase criterion is reported without naming its code.
- `docs/m6/`, the KTDs and the code agree, and design §11's M6 row is marked done with its evidence.
- Ticket `9002a2c` (#13) is updated with what was done and closed after the owner merges. #41 is closed by U2's merge.
- No server process is left running after the test suite.
- No experimental or abandoned code remains in the diff, and none of the owner's uncommitted changes (`.gitignore`, `compose.yaml`, `.claude/`, script mode bits) is committed.

---

## Appendix

### Sources and research

- Design: `docs/design.md` §4.1, §4.2, §5.2, §6.1–§6.3, §8.4, §9, §10.5, §11 and §12 Q1, Q5, Q8, Q11, Q14, Q17–Q20; the M4, M5a and M5b plans and chapters.
- Repository:
  - `src/Warrant/Spec.cs`: only `Implies`, `ForAll`, `Exists`, `Decreases`.
  - `src/Warrant.Vir/VirOperators.cs`: `VirOverflow.Checked` exists, unused.
  - `src/Warrant.Semantics/BodyTranslator.cs`: `RequireWrap` throws on checked, "needs exceptions (M6)".
  - `src/Warrant.Extraction/Walker.cs`: every M6 rejection site, and the WRT0005 branch already worded "verified or modelled members".
  - `src/Warrant.Engine/PipelineScope.cs` `ProveDecrease`: the obligation pattern KTD13 copies.
  - `src/Warrant.Engine/SemanticsBundle.cs` and `PinnedDeclarations.ndjson.gz` (#26).
  - `src/Warrant.Meta/Attributes/Sidecar.cs` and `tools/warrant-attrs/Main.lean`: seven attribute kinds, no `spec`.
  - `src/Warrant.Engine/Service/Cache/CacheKey.cs`: keys include the bundle and sidecar SHA-256, so U1 needs no cache change.
  - `lean/bundle-roots.txt`: 394 roots. `lean/Warrant/`: 115 lines.
  - `tests/Warrant.Semantics.Tests/ClrAgreementTests.cs`, `tests/Warrant.Engine.Tests/Differential/`, `tests/Warrant.Cli.Tests/M5bExitTests.cs`.
- Lean 4.35.0 toolchain sources:
  - `Std/Do/**`: `WP/Basic.lean` instances for `Id`, `StateT`, `ReaderT`, `ExceptT`, `OptionT`, `EStateM`; `Triple/SpecLemmas.lean`, 163 `@[spec]` lemmas; `WP/SimpLemmas.lean`.
  - `Lean/Elab/Tactic/Do/**`: `mvcgen`, 4,830 lines; `Attr.lean`, `specMap`.
  - `Std/Tactic/Do/Syntax.lean:440`: `mvcgen` deprecated since 2026-08-21.
  - `Lean/Elab/Tactic/VCGen/**`: `vcgen` on `Lean.Meta.Sym` and `grind`.
- Closure measured with `importModules`: Init 65,972 constants; `Std.Do` adds 1,443 (937 theorems); no new axioms; no `extern` or `implemented_by`.
- Lean release notes v4.22.0 (`Std.Do` introduced), v4.23.0 (universe-polymorphic assertions), v4.29.0 (local specs), v4.35.0 (`vcgen`, `mvcgen` deprecated): lean-lang.org/doc/reference.
