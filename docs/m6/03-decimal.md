# 3. `decimal`

> Part of the [M6 design](README.md). Decisions: KTD7, KTD11 and KTD23. Units: U4 (model), U17 (extraction), U21
> (translation).

The payment example's `Amount` is a `decimal`, so M6 models the part of `decimal` that example and its kind need:
literals, comparisons, numeric equality, `+`, `-`, unary `-`, and `Math.Min`, `Max` and `Abs` (design §12 Q1).
Multiplication, division, remainder and explicit rounding wait for M7, and extraction rejects them as
`decimal operator other than + and -`.

## The model

`lean/Warrant/Decimal.lean` (KTD7):

```lean
structure Decimal where
  negative : Bool
  mantissa : Nat
  scale : Nat
  mantissa_lt : mantissa < 2 ^ 96
  scale_le : scale ≤ 28
```

A value is `(-1)^negative × mantissa × 10^-scale`, stored as the CLR stores it, so `1.0m` and `1.00m` are different
values of the structure, and so are `0m` and negative zero.
`units d` is the value as an integer count of 10^-28, the finest scale: `num d × 10^(28 - scale)`.

- **Equality and order compare values.** `Decimal.eq a b` is `a.units = b.units`, with a `Decidable` instance, and `<`
  and `<=` compare `units`. So `1.0m == 1.00m` and `-0m == 0m`, as in C#. Lean's `Eq` on the structure would say
  otherwise, which is why translation never uses it for `decimal` (below).
- **Unary minus** flips the sign bit and never raises, so `-0m` is negative zero.
- **Addition** computes the exact sum at the larger operand scale. When its mantissa fits in 96 bits, that is the
  result. Otherwise the exact sum is rounded once, half to even, at the largest smaller scale whose rounded mantissa
  fits, and the sum raises `overflow` only when even scale 0's does not fit. An exactly zero sum takes the sign the
  CLR's `DecAddSub` gives it. `a - b` is `a + (-b)`, as in the CLR.
- **`Math.Min`, `Max` and `Abs`** on `decimal` (`lean/Warrant/Math.lean`) return the operand .NET returns on equal
  values, and `Abs` clears the sign. None can raise, since a `decimal`'s sign is a bit of its own.

`add` and `sub` are `ClrM` programs with `@[spec]` lemmas in the shape of chapter 2's; their precondition is stated over
`sum a b : Option Decimal`, `none` on overflow.
A literal is `Decimal.lit negative mantissa scale (Eq.refl true) (Eq.refl true)`: the two bounds are `Nat.ble` facts the
kernel checks by evaluation.

## Trusted definitions, proved lemmas

The definitions are trusted (#117): nothing proves that rounding at the largest fitting scale is what the CLR does.
They are kept small enough to read against the CLR, and a comment block in the file states the model.
The lemmas are proved in Lean and checked again by Warrant's kernel: equality is an equivalence
(`eq_refl`, `eq_symm`, `eq_trans`), the order is total (`le_total`, `lt_trichotomy`, transitivity, antisymmetry),
`units` of `-a` and of `Math.Abs a`, and that a sum whose exact mantissa fits is exact (`sum_of_fits`), so `a - b < a`
when `b > 0` and the subtraction is exact (`sub_lt_of_fits`).
Without exactness that last lemma is false: the CLR rounds `decimal.MaxValue - 0.4m` to `decimal.MaxValue`, and a named
agreement row pins it. The plan had assumed the unconditional form (#214).

What guards the definitions is agreement with the CLR.
`ClrAgreementTests` compares every operation with the CLR's own `decimal` arithmetic on the same operands, by
representation (sign, mantissa and scale), not by value: literals at every scale 0 to 28; `+` and `-` on boundary pairs
and on 150 random cases per row with the pinned seed; the named KTD7 cases (`MaxValue + 0.4m` and `+ 0.5m`, ties to even,
`0.1m + 0.2m` at scale 1); unary minus with negative zero; the six comparisons; and `Math.Min`, `Max` and `Abs`.
The generator (`tests/Warrant.TestSupport/Generators.cs`) leans toward `MaxValue` and `MinValue`, negative zero and zero
at several scales, mantissas near 2^96, pairs equal by value at different scales, a value with its negation, and a
large value with a scale-28 one.

## Extraction and translation

Extraction (U17) produces `decimal` literals exactly, scale included (VIR's `DecimalLitExpr` carries sign, mantissa and
scale), comparisons with a decimal comparison kind, `==` and `!=`, `+` and `-` (always marked checked), unary `-` and
`+`, record fields of type `decimal` and `decimal?`, and the three `Math` members.

Translation (U21, `src/Warrant.Semantics/Operators.cs`):

| C# | Lean |
|---|---|
| `decimal`, `decimal?` | `Warrant.Decimal`, `Option Warrant.Decimal` |
| a literal | `Decimal.lit neg m e (Eq.refl true) (Eq.refl true)` |
| `==`, `!=` | `Decimal.eq` through `Decimal.decEq`, by value |
| `<`, `<=`, `>`, `>=` | `Decimal.instLT`/`instLE` with `decLt`/`decLe`; `>` and `>=` swapped in bodies, `GT.gt`/`GE.ge` in quantified statements |
| unary `-` | `Decimal.neg`, pure |
| `+`, `-` | `Decimal.add`/`sub` in `ClrM`, raising even inside `unchecked` |
| `Math.Min`, `Max`, `Abs` | `Decimal.min`, `max`, `abs`, pure |
| `==` on a record with a `decimal` field | the record's `$eq` compares that field with `Decimal.eq` (#77) |

Because `+` and `-` raise in any context, a method that adds `decimal`s is a raising unit (KTD11, chapter 4), and its
obligation must show the sum does not overflow; `AddFee` and `Difference` in `tests/corpus/m6/refuted/Nullables.cs` fail
that way with no `Spec.Requires`.
A theorem statement cannot contain them (`decimal arithmetic`, WRT0002), since a theorem is a `Prop`, not a program.
Comparisons, unary `-` and the `Math` members are pure, so theorems may use them.
`docs/proving/proofs-that-work.md` ("`decimal` equality and order") has four theorems the engine test
`DecimalEqualityAndOrderAreProvable` proves, among them `new Price(1.0m) == new Price(1.00m)` by computation and
transitivity of `<` over every `decimal` with `Warrant.Decimal.lt_iff`, `le_iff` and `omega`.

The differential tests (chapter 8) run the 14 `decimal` members of the corpus against the CLR on 58,941 boundary inputs
and compare results by representation: `-1.00m` against the model's `-1.0m`, or `0m` against `-0m`, is a disagreement
(`ADecimalResultIsComparedByRepresentation`). All agree.

## Known gaps

Each of these makes a true claim fail or a method be rejected; none lets a false claim pass.

- **#216**: `Prove.That(Larger(a, b) >= a)` over parameters, with `Larger` returning `Math.Max(a, b)`, does not prove.
  After unfolding through `max_def` and `le_iff` the goal is `units a ≤ units (if … then a else b)`, and nothing splits
  the `if`: `omega` treats it as an atom. The `int` and `long` versions prove, because their models unfold to `Int32`
  comparisons `omega` reads.
- **#217**: `simp` does not compute `units` of a literal, so a claim over every `decimal` that mentions one
  (`Spec.Implies(a > 0m, -a < a)`) does not prove.
- **#218**: a record with a nullable field (`decimal?`, `int?`, `Payment?`) fails translation, because the record's
  `$eq` has no case for a nullable field. Extraction accepts such records; translation stops with an error.
