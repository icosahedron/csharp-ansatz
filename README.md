# Warrant

**Machine-checked proofs about ordinary C# code.**

> Status: **milestones 0 to 5b of 8 are done.** `dotnet build` proves theorems about
> pure C# methods for every input and fails on a theorem it cannot prove, with the goal and
> a counterexample. A per-user verification server and a result cache make an unchanged
> rebuild run no tactics, and `WarrantRecheck=true` has the kernel re-check every cached
> proof. A C# port of the Lean 4 kernel checks every proof, Lean's entire Init library and
> all of Mathlib, and Lean's own kernel re-checks what it admits. Contracts for code that
> calls databases and services come next (M6). Start with the [design document](docs/design.md).

Warrant translates selected C# methods into the Calculus of Inductive
Constructions, the type theory of [Lean 4](https://lean-lang.org/). Proofs
about them are checked by a C# port of the Lean 4 kernel. Lean's libraries,
including Mathlib, are available as imported declarations, and no Lean
toolchain is needed at verification time.

The project is inspired by [Ansatz](https://github.com/replikativ/ansatz), which
brings Lean 4's kernel to Clojure. Warrant's focus is different: it verifies
**existing** C#, opt-in and incrementally:

- **Pure functions:** prove properties of business logic.
- **Contracts:** `Spec.Requires`/`Spec.Ensures` on methods that call
  databases or services, with those dependencies treated as explicit, reported
  assumptions.
- **Verified regions:** prove selected blocks inside otherwise ordinary methods.

Verification runs in a long-lived **verification server** with a
content-addressed cache of proof certificates, or in-process when there is no
server. An MSBuild task makes failed proofs ordinary build errors, an IDE
analyzer reports unsupported code as you type, and certificates can be
exported for independent re-checking by other Lean kernels.

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

*(This runs today, through M5a's tactics; see [design §5](docs/design.md#5-the-c-surface)
for the rest of the surface. A developer guide to writing proofs, which marks what
runs and what is planned, is in [docs/proving](docs/proving/README.md).)*

## Why "Warrant"

> A warrant for an argument is the underlying justification or logical bridge that
> connects your evidence (data) to your conclusion (claim). It explains why the data
> proves the point you are making, transforming a collection of facts into a cohesive
> and persuasive argument.

## Building

Requires the [.NET 10 SDK](https://dotnet.microsoft.com/download).

```sh
dotnet build
dotnet test
```

| Project | Contents |
|---|---|
| `src/Warrant` | The user package: `[Verified]`, `[Theorem]`, `Prove`, `Spec`, `Tactic`, and the IDE analyzer |
| `src/Warrant.Cic` | Names, universe levels, expressions, constants, declarations, environments |
| `src/Warrant.Lean4Export` | Strict reader (formats 3.0.0, 3.1.0) and writer (3.1.0) for lean4export NDJSON |
| `src/Warrant.Kernel` | The type-checking kernel: a port of Lean 4's C++ kernel ([docs/kernel.md](docs/kernel.md)) |
| `src/Warrant.Extraction`, `Warrant.Vir`, `Warrant.Semantics` | C# to the Verification IR, and VIR to CIC |
| `src/Warrant.Meta`, `Warrant.Engine` | Lean's Meta layer and tactics, ported; the verification service and the result cache |
| `src/Warrant.Server` | `warrant-server`, the per-user verification server |
| `src/Warrant.Store` | Store v1: imported Lean libraries on disk, loaded lazily |
| `src/Warrant.Analyzers` | Extraction's diagnostics in the IDE |
| `src/Warrant.Build` | The MSBuild task that runs `warrant verify` after the compiler |
| `src/Warrant.Cli` | `warrant`: `check`, `stats`, `export`, `translate`, `verify`, `explain`, `server`, `import`, `check-store`, `sample-store` |
| `tools/lean-replay` | Lean program used by `scripts/cross-check.sh` to re-check files with Lean's own kernel |
| `tests/` | Unit tests, the C# corpora and the export corpus (`tests/data`, see its README for provenance) |

To check an export file with the kernel, and to prove the M5a corpus's theorems:

```sh
dotnet run -c Release --project src/Warrant.Cli -- check tests/data/init-medium.ndjson.gz
dotnet run -c Release --project src/Warrant.Cli -- verify tests/corpus/m5a/accepted
```

[REPRODUCING.md](REPRODUCING.md) explains how everything here was done and how to
reproduce every result, including exporting and checking Lean's full Init library.

## Documents

- [Design](docs/design.md): architecture, semantics, trusted base, milestones, open questions
- [Writing proofs](docs/proving/README.md): the developer guide
- Milestone chapters: [M4](docs/m4/README.md) (translating C#), [M5a](docs/m5a/README.md) (tactics and the build), [M5b](docs/m5b/README.md) (server, cache, store, analyzers)
- [Kernel](docs/kernel.md): how the port maps to Lean's C++, deliberate differences, results
- [Checking Mathlib](docs/mathlib.md): all of Mathlib v4.35.0 through Warrant's kernel and Lean's, with time and memory
- [Reproducing](REPRODUCING.md): how the work was done and how to duplicate it
- [Design history](docs/history/README.md): the conversations that led here, including the full session transcript

## License

Apache License 2.0. See [LICENSE](LICENSE) and [NOTICE](NOTICE).
