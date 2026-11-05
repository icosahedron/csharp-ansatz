# Warrant

**Machine-checked proofs about ordinary C# code.**

> Status: **milestone 3 of 8.** A C# port of the Lean 4 kernel checks Lean's
> entire Init library (57,919 declarations at Lean 4.35.0), and Lean's own kernel re-checks
> everything it admits; the C#-to-CIC frontend comes next. Start with the [design document](docs/design.md).

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
content-addressed cache of proof certificates. An MSBuild task makes failed
proofs ordinary build errors, and certificates can be exported for
independent re-checking by other Lean kernels.

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

*(Target syntax under discussion; see [design §5](docs/design.md#5-the-c-surface).
A developer guide to writing proofs, written ahead of the implementation, is in
[docs/proving](docs/proving/README.md).)*

## Building

Requires the [.NET 10 SDK](https://dotnet.microsoft.com/download).

```sh
dotnet build
dotnet test
```

| Project | Contents |
|---|---|
| `src/Warrant.Cic` | Names, universe levels, expressions, constants, declarations, environments |
| `src/Warrant.Lean4Export` | Strict reader (formats 3.0.0, 3.1.0) and writer (3.1.0) for lean4export NDJSON |
| `src/Warrant.Kernel` | The type-checking kernel: a port of Lean 4's C++ kernel ([docs/kernel.md](docs/kernel.md)) |
| `src/Warrant.Cli` | `warrant check <export>` / `export <in> <out>`: re-check a lean4export file; write what the kernel admitted |
| `tools/lean-replay` | Lean program used by `scripts/cross-check.sh` to re-check files with Lean's own kernel |
| `tests/` | Unit tests and the export corpus (`tests/data`, see its README for provenance) |

To check an export file with the kernel:

```sh
dotnet run -c Release --project src/Warrant.Cli -- check tests/data/init-medium.ndjson.gz
```

[REPRODUCING.md](REPRODUCING.md) explains how everything here was done and how to
reproduce every result, including exporting and checking Lean's full Init library.

## Documents

- [Design](docs/design.md): architecture, semantics, trusted base, milestones, open questions
- [Kernel](docs/kernel.md): how the port maps to Lean's C++, deliberate differences, results
- [Checking Mathlib](docs/mathlib.md): all of Mathlib v4.35.0 through Warrant's kernel and Lean's, with time and memory
- [Reproducing](REPRODUCING.md): how the work was done and how to duplicate it
- [Design history](docs/history/README.md): the conversations that led here, including the full session transcript

## License

Apache License 2.0. See [LICENSE](LICENSE) and [NOTICE](NOTICE).
