# LeanSharp

**Machine-checked proofs about ordinary C# code.**

> Status: **design phase.** There is no code yet. Start with the
> [design document](docs/design.md).

LeanSharp translates selected C# methods into the Calculus of Inductive
Constructions, the type theory of [Lean 4](https://lean-lang.org/). Proofs
about them are checked by a C# port of the Lean 4 kernel. Lean's libraries,
including Mathlib, are available as imported declarations, and no Lean
toolchain is needed at verification time.

The project is inspired by [Ansatz](https://github.com/replikativ/ansatz), which
brings Lean 4's kernel to Clojure. LeanSharp's focus is different: it verifies
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

*(Target syntax under discussion; see [design §5](docs/design.md#5-the-c-surface).)*

## Documents

- [Design](docs/design.md): architecture, semantics, trusted base, milestones, open questions
- [Design history](docs/history/README.md): the conversations that led here

## License

Apache License 2.0. See [LICENSE](LICENSE) and [NOTICE](NOTICE).
