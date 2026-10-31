# Claude Code design session

- **Date:** 2026-10-31
- **Participants:** the project author and Claude (Claude Code)
- **Follows:** [ChatGPT conversation](2026-10-31-chatgpt-recommend-csharp-frontend.md)
- **Result:** [`../design.md`](../design.md)

> This is a **summary**, not a verbatim transcript. It records what was checked,
> what was proposed, and what the author decided.

## 1. Fact-checking ChatGPT against Ansatz

Before building on the ChatGPT conversation, Claude cloned
`replikativ/ansatz` (commit `662ac21e687083829ecd04968dd47cbec3541a7a`) and
checked ChatGPT's claims against the source and documentation. Findings
(recorded in full in design doc Appendix A):

- The kernel expression language has 12 kinds, including `Proj` and separate
  Nat/String literals. There is **no `MVar`** at kernel level. ChatGPT listed
  `MVar` and omitted `Proj`.
- `init-medium` ships as `resources/ansatz/init-medium.ndjson.gz` (3.3 MB
  gzipped, "2,997 declarations" per Ansatz's docs; LeanSharp later counted 5,118
  constants in 4,631 declaration records), not under `test-data/`. The full Init export
  has 54,335 declarations.
- Ansatz verifies **all 707,508** Mathlib v4.33.1 declarations (504,824
  theorems), in about 80 minutes on 4 workers. ChatGPT cited older or lower
  counts.
- Import is lean4export NDJSON, format 3.x: an indexed table of names, levels
  and expressions.
- `test-data/arena/` contains kernel-arena-style cases, including negative
  cases that a kernel must reject.
- Ansatz adds a fuel limit to the kernel (Lean has none).
- Ansatz compiles runtime code **from the checked kernel term**, so what runs
  is derived from what was proved.
- Size: the Java kernel is about 11k lines. Tactics are about 21k lines of
  Clojure, and elaboration, surface and store about 20k more.

## 2. Proposals made in the session

1. **The central fork is which way the arrow points.**
   - (A) verified source → CIC → generated code, as Ansatz does
   - (B) existing C# → CIC model → proofs about the model, as ChatGPT proposed

   B is the reason to do this in C# at all, and the only option that covers the
   author's database example. Everything below the elaborator is shared.
2. **Model C# honestly.** `int` → Lean `Int32` (wrap-around), `checked` →
   `Except`, `T?` → `Option`. A false theorem then fails to prove, instead of
   being proved about unbounded integers.
3. **Don't verify inside the analyzer.** Analyzers must be `netstandard2.0`,
   fast, deterministic and free of I/O. Use a long-lived **verification
   server** with a content-addressed cache, plus an authoritative **MSBuild
   task**.
4. **Port the kernel instead of bridging to the JVM kernel.** The kernel is the
   best-specified component, has a 707k-declaration oracle, and an independent
   kernel is the extra assurance the author wants.
5. **Export lean4export NDJSON for cross-checking**, not Lean source, so other
   kernels check our exact terms rather than a re-elaborated round trip.
6. **Attributes can't hold expressions** (their arguments must be compile-time
   constants). Put specs in body calls and companion contract classes.
7. **Milestones:** IR and importer → kernel (init-medium, arena) → exporter and
   cross-kernel harness → frontend → tactics, server and build integration.

## 3. Decisions by the author

| Decision | Outcome |
|---|---|
| Direction | **B**: verify existing C# |
| Verification server | **Yes**: "I love the idea of a verification server" |
| Name | **LeanSharp**, provisional "until we think of something better" |
| License | **Apache 2.0** |
| History | Commit the ChatGPT conversation and this summary to `docs/history/` |
| Target framework | Not yet answered; design assumes net10.0 (design doc D8) |

## 4. Additions made while writing the design document

These came after the decisions above and are open for review in
[`../design.md`](../design.md):

- **VIR** (Verification IR) as the hashable wire format between Roslyn
  extraction and a Roslyn-free server.
- The **C# semantic model as a Lean library** (`lean/LeanSharp/`), proved in
  real Lean, exported to NDJSON, building on Lean's `Std.Do` framework.
- **External calls as hypotheses**, not axioms. The theorem quantifies over
  every implementation that satisfies the contract.
- **VC generation as a proof-producing tactic**, which keeps it out of the
  trusted base.
- **Proof certificates in the cache**, so CI can re-check with the kernel alone.
- Spec calls marked `[Conditional]`, so they cost nothing at runtime but stay
  visible to Roslyn.
