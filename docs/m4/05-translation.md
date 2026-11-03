# 5. Translation

> Part of the [M4 design](README.md). Decisions: KTD6 to KTD10, KTD17, KTD21, KTD22 in the [plan](../plans/2026-11-02-1245-feat-m4-pure-subset-plan.md).

Translation turns each VIR unit into kernel declarations: inductive types for records and closed types, definitions for methods, and propositions for theorems.
It lives in `src/Warrant.Semantics` (net10.0), which references `Warrant.Vir`, `Warrant.Cic` and `Warrant.Kernel` and never Roslyn.
It returns declarations; the engine (chapter 7) admits them.
It uses the kernel's binder helpers (`LocalContext.MkLambda`, `MkPi`, `ExprOps.Abstract`) to build terms with named free variables and close them into de Bruijn form, rather than counting indices by hand.

Translation is in the trusted base, and the boundary is drawn by assembly (KTD22).
`Warrant.Semantics` holds everything whose mistakes the kernel cannot catch: the types, the definitions and the theorem *statements*, because a wrong statement proves the wrong claim.
It builds every declaration whole, a theorem's name and type included, and leaves only the theorem's proof value for the engine to fill.
Proof terms, which the kernel checks, are built in `Warrant.Engine` (chapter 6), so the trusted assembly contains no untrusted code and a review can be scoped to it.
Translation is kept "deliberately simple and syntax-directed" (design §4.2): each VIR node has one rule, and the rule does not look at the node's context except where this chapter says so.

All Lean below is notation for reading the terms.
Warrant builds the terms directly and never writes Lean text (design §4).

## Names

A C# symbol's Lean name depends on that symbol alone, and is derived from its documentation-comment ID (KTD6):

| C# | Lean name |
|---|---|
| `Payouts.PayoutRules.Payout(int, int, int)` | `Cs.Payouts.PayoutRules.Payout(System.Int32,System.Int32,System.Int32)` |
| `Payouts.PayoutTheorems.CappedAtTheLimit()` | `Cs.Payouts.PayoutTheorems.CappedAtTheLimit` |
| `Rates.Fee(A.Status)` and `Rates.Fee(B.Status)` | `Cs.Rates.Fee(A.Status)` and `Cs.Rates.Fee(B.Status)` |
| A property `Payment.IsLarge` | `Cs.Claims.Payment.IsLarge` |
| A generic type `Result<T>` (later milestones) | ``Cs.Claims.Result`1`` |
| Record `Payment` and its constructor | `Cs.Claims.Payment` and `Cs.Claims.Payment.$mk` |
| Record `Payment`'s equality | `Cs.Claims.Payment.$eq` |
| Closed type `Outcome`'s member `Matched` | `Cs.Claims.Outcome.Matched` (a constructor) |
| Closed type `Outcome`'s index | `Cs.Claims.Outcome.$index` |

- Every name starts with the component `Cs`, so no C# name can collide with an Init name: C# namespaces called `Nat` or `Lean` are fine.
- Each namespace segment and each type in the path is one component, and the member is the last component.
  A member with parameters carries its fully qualified parameter list, exactly as the documentation-comment ID writes it, inside its own component.
  It always does, not only when the member is overloaded: otherwise adding an overload would rename the existing member, and names end up in exported certificates and in reports, where they must not change because a sibling did.
  Fully qualified types also keep `Fee(A.Status)` and `Fee(B.Status)` apart.
- Names that Warrant generates carry a `$`, which no C# identifier can contain, so they cannot collide with a user's member.
- Members named after Lean's auxiliary constructions (`rec`, `casesOn` and the others in chapter 3) are rejected, so the kernel's `T.rec` and M5a's generated auxiliaries never collide with C#.
- Any other collision is a translation error, never resolved by searching for a free name.

These names are for the kernel and for export.
People never have to read them: diagnostics and reports show C# display names, kept next to the translation.
A display name is fully qualified and lists the parameter types as C# writes them, `Payouts.PayoutRules.Payout(int, int, int)` or `Claims.Payments.Validate(Claims.Payment)`, so overloads stay apart in a report.
A WRT0001 message names the theorem by its short name (`'NeverWraps'`), because its location already says where it is (chapter 6).

## Types

| C# | CIC | Notes |
|---|---|---|
| `int`, `long`, `bool` | `Int32`, `Int64`, `Bool` | Init's types (chapter 1). |
| Open enum `PaymentStatus : int` (or `: long`) | `def Cs.Claims.PaymentStatus : Type := Int32` (or `Int64`) | Reducibility hint `abbrev`. Each member is an `abbrev` constant of that type, e.g. `Cs.Claims.PaymentStatus.Pending := 0`. Other underlying types are rejected. |
| `[Closed]` enum or class | An inductive type with one constructor per member, in declaration order | Plus `$index` (below). |
| Sealed record `Payment(int Id, int Amount, PaymentStatus Status)` | An inductive type with the single constructor `$mk : Int32 → Int32 → PaymentStatus → Payment` | Plus `$eq` (below). |

An open enum stays a named type, so a goal still says `PaymentStatus` where the C# did, but it unfolds to its underlying integer type.
Comparisons on open enums are emitted at the underlying type (`@Eq Int32 …`), so they use Init's instances directly.
Because the type is the underlying integer, a value such as `(PaymentStatus)7` is representable, which is exactly what "open" means (design D12).
The alternative, a one-field structure wrapping the integer, was rejected (KTD9): every goal would carry its constructor and projection, it would need instances of its own, and every cast would become a term, where the `abbrev` reuses Init's instances and makes a cast free.
The kernel's `abbrev` hint is not the same thing as Lean's `@[reducible]` attribute, which M5a's tactics read from an attribute sidecar; that sidecar will need entries for translated declarations too (plan, Deferred to Follow-Up Work).

A record field read `p.Amount` is a primitive projection, `Expr.Proj(Payment, 1, p)`; projection indices count from 0, in field order.
Translation generates no projection functions: the kernel's `Proj` already gives the field, and the kernel generates only `.rec` for an inductive, not the projections or `casesOn` that Lean's elaborator would add.
In the Lean notation in this chapter, `p.Amount` stands for that primitive projection.
`new Payment(a, b, c)` is `$mk a b c`, and `p with { Amount = x }` is `$mk p.Id x p.Status`.

## Literals and the operator table

Every literal and operator maps to one fixed term (KTD8).
The table below is the whole of M4's arithmetic.
Every constant in it appears in `lean/bundle-roots.txt`, and each row has a CLR-agreement test (chapter 7).
The shapes are the ones Lean 4.35.0's elaborator produces for the same Lean source, checked by printing them with `pp.all`, so translated terms look like Lean's and M5a's simp lemmas will match them.

| C# (VIR) | CIC term (`Int32`; `Int64` is the same with `64`) |
|---|---|
| literal `n ≥ 0` | `@OfNat.ofNat Int32 n (@Int32.instOfNat n)` |
| literal `-n` | `@Neg.neg Int32 Int32.instNeg (OfNat.ofNat n)` |
| `a + b` | `@HAdd.hAdd Int32 Int32 Int32 (@instHAdd Int32 instAddInt32) a b` |
| `a - b` | `@HSub.hSub … (@instHSub Int32 instSubInt32) a b` |
| `a * b` | `@HMul.hMul … (@instHMul Int32 instMulInt32) a b` |
| `-a` | `@Neg.neg Int32 Int32.instNeg a` |
| `(long)a` | `Int32.toInt64 a` |
| `(int)a` on a `long` | `Int64.toInt32 a` |
| `true`, `false` | `Bool.true`, `Bool.false` |

`int.MinValue` is the literal `-2147483648`, which the table turns into `-(2147483648)`.
`OfNat` wraps `2147483648` to `int.MinValue`, and negating `int.MinValue` gives `int.MinValue` again, so the result is right; a translation test pins it.

## Conditions and Boolean values

A C# `bool` expression is translated one of two ways, depending on where it is (KTD8).

**As a condition** (the test of an `if`, `?:` or `switch` guard, or a theorem statement) it becomes a proposition `P` together with a `Decidable P` instance, because Lean's `ite` takes both:

| C# condition | Proposition | Instance |
|---|---|---|
| `a == b` on `int` | `@Eq Int32 a b` | `instDecidableEqInt32 a b` |
| `a < b`, `a <= b` | `@LT.lt Int32 instLTInt32 a b`, `@LE.le Int32 instLEInt32 a b` | `Int32.decLt a b`, `Int32.decLe a b` |
| `a > b`, `a >= b` | `LT.lt b a`, `LE.le b a` | `Int32.decLt b a`, `Int32.decLe b a` |
| `a != b` | `Not (Eq a b)` | `@instDecidableNot _ (instDecidableEqInt32 a b)` |
| `x && y`, `x \|\| y` | `And Px Py`, `Or Px Py` | `@instDecidableAnd _ _ Dx Dy`, `@instDecidableOr _ _ Dx Dy` |
| `!x` | `Not Px` | `@instDecidableNot _ Dx` |
| a `bool` variable or call `b` | `@Eq Bool b Bool.true` | `instDecidableEqBool b Bool.true` |
| `r == s` on records | `@Eq Bool (R.$eq r s) Bool.true` | `instDecidableEqBool (R.$eq r s) Bool.true` |
| `r == s` on closed types | `@Eq Bool (Nat.beq (T.$index r) (T.$index s)) Bool.true` | `instDecidableEqBool (Nat.beq …) Bool.true` |
| `r != s` on records or closed types | `Not` of the row above | `@instDecidableNot _ D` |
| `Spec.Implies(x, y)` (statements only) | `∀ (_ : Px), Py` | `@forall_prop_decidable Px (fun _ => Py) Dx (fun _ => Dy)` |

**As a value** (assigned, returned, passed or compared) it becomes a `Bool`:

| C# value | Term |
|---|---|
| a comparison `a < b` | `@Decidable.decide (LT.lt a b) (Int32.decLt a b)` |
| `x && y`, `x & y` | `Bool.and x y` |
| `x \|\| y`, `x \| y` | `Bool.or x y` |
| `!x` | `Bool.not x` |
| `x ^ y` | `Bool.xor x y` |
| `x == y` on `bool` | `@Decidable.decide (Eq x y) (instDecidableEqBool x y)` |
| `r == s` on records or closed types | `@Decidable.decide (@Eq Bool (R.$eq r s) Bool.true) (instDecidableEqBool (R.$eq r s) Bool.true)`, and `Nat.beq` of the indexes for a closed type |

In general, any comparison used as a value is `decide` of its condition, with the condition's instance.
So `Same(a, b) => a == b` over a closed class returns `decide (Nat.beq a.$index b.$index = true)`, not the `Nat.beq` alone.

`&&` and `&` give the same term because nothing in M4 has side effects; M6 separates them when the right-hand side can throw (VIR keeps `logical` nodes for that reason, chapter 4).

The two forms are the ones Lean itself uses for `if a ≤ b ∧ ¬a = 0 then …` and for a `Bool`-valued `decide (x < y) && …`.
This was checked by elaborating both in Lean 4.35.0: Lean produces `ite` over `And`/`Not` with `instDecidableAnd`, `Int32.decLe` and `instDecidableNot`, and a bare `Bool` test `if x then …` becomes `ite (x = true)` with `instDecidableEqBool`.
Ansatz's history shows the cost of choosing other shapes: it had to add a Bool-to-Prop bridge later so that `simp` could see through its conditions.

## Statements and control flow

A method body is a list of statements, and CIC has no statements.
Translation threads an environment `ρ` that maps each C# local and parameter to the term that currently holds its value, and translates a statement list together with "the rest of the block" (KTD7):

- `return e` translates to `e`.
- `var x = e; rest` and `x = e; rest` translate to `let x := e; rest`, with `ρ` now mapping `x` to the new binder.
  This is how reassignment works without versions in VIR: each assignment is a new `let`, and later reads see the latest one.
  It holds inside branches too, so the value a branch hands on is a `let`-bound local, not the expression that computed it.
- `if (c) A else B; rest` uses the first rule that applies:
  1. **Neither branch falls through** (both end in `return` on every path): `ite c A B`.
     Nothing can follow, because Roslyn reports the following code as unreachable and extraction rejects it.
  2. **One branch falls through**: `rest` is translated once, into that branch.
     This is the early-return pattern, and it duplicates nothing.
  3. **Both fall through, neither contains a `return`, and they change exactly one local that `rest` reads**: `let x := ite c (x after A) (x after B); rest`.
  4. **Both fall through, neither contains a `return`, and they change no local that `rest` reads**: `rest`, as if the `if` were absent.
     The guard matters: in `if (c) { if (d) return 1; } else { … } return 2;` both branches can fall through and neither changes a local, but dropping the `if` would lose `return 1`.
     The corpus and the translation tests include exactly this shape (plan, U5 and U7).
  5. **Otherwise**: a join point.
     `let jp := fun (x₁ … xₙ) => rest; ite c A' B'`, where `x₁ … xₙ` are the locals that `rest` reads and some branch changes, in declaration order, and every point where `A` or `B` falls through becomes `jp` applied to the current values.
     When no such local exists (the nested-`return` shape above), the join point has no parameters and is simply `let jp := rest`.
- A `switch` statement follows the same rules with one branch per section: sections ending in `return` do not fall through, and sections ending in `break` do.
  A switch with no `default` section gets one more, empty branch, for the values no section matches.

Rules 3 and 4 are shortcuts, and both rely on M4's units being pure: a branch that could throw or call an external could be neither dropped nor reduced to a value.
M6's effectful units get a monadic translation instead, which keeps the join points and drops the shortcuts (KTD7).

These rules never copy a non-trivial continuation, so the size of a translated method is linear in the size of its source.
Copying the rest of the block into each branch is simpler but grows exponentially with a chain of `if`s; hax and the first version of Aeneas both did it and both moved away from it.
Join points appear in goals as `let`-bound functions, which the kernel and M5a's `simp` reduce by zeta and beta reduction.

### `Payout`

```csharp
if (loss <= deductible) return 0;          // rule 2: only the else side falls through
var covered = loss - deductible;
return covered > limit ? limit : covered;
```

```lean
fun (loss deductible limit : Int32) =>
  ite (loss ≤ deductible) 0
    (let covered := loss - deductible
     ite (limit < covered) limit covered)
```

### `Validate`

Each `if` returns, so each one puts the rest of the method into its `else`:

```lean
fun (p : Cs.Claims.Payment) =>
  ite (p.Amount ≤ 0) Cs.Claims.PaymentResult.InvalidAmount
    (ite (¬ (p.Status = Cs.Claims.PaymentStatus.Pending)) Cs.Claims.PaymentResult.InvalidStatus
      Cs.Claims.PaymentResult.Valid)
```

The second test is emitted at `Int32`, because `PaymentStatus` is an open enum.

### Reassignment, and a join point

```csharp
[Verified]
public static int Shipping(int weight, bool express, bool member)
{
    var cost = weight * 2;
    var bonus = 0;
    if (express) { cost = cost + 15; bonus = 1; }   // rule 5: both sides fall through, two locals change
    if (member) return cost - 5;                    // rule 2
    return cost + bonus;
}
```

```lean
fun (weight : Int32) (express member : Bool) =>
  let cost := weight * 2
  let bonus := 0
  let jp := fun (cost bonus : Int32) =>
    ite (member = true) (cost - 5) (cost + bonus)
  ite (express = true)
    (let cost := cost + 15
     let bonus := 1
     jp cost bonus)
    (jp cost bonus)
```

This is the term translation builds, decoded from the NDJSON that `warrant translate --out` writes, with names in place of de Bruijn indices and with the instance arguments left out; the translation tests check that it has exactly one join point.
Each assignment in the `express` branch is its own `let`, so the jump passes the new binders rather than the expressions `cost + 15` and `1`.

When only one local changes, rule 3 applies instead.
`Fee` in the corpus is that shape:

```csharp
var fee = 10;
if (rush) fee = fee * 2;     // rule 3: both sides fall through, one local changes
return price + fee;
```

```lean
let fee := 10
let fee := ite (rush = true) (let fee := fee * 2; fee) fee
price + fee
```

## `switch`

**Over a `[Closed]` enum**, a `switch` is the type's recursor with a constant motive, which is what Lean's `casesOn` unfolds to.
Constant patterns name members by value, which extraction has already resolved to constructors (chapter 3).
A closed *class* never reaches this rule: C# patterns must be constants, and a closed class's instances are not, so C# code compares them with `==`.

```lean
-- switch (status) { ClaimStatus.Open => 1, ClaimStatus.Paid => 2, _ => 0 }
@Cs.Claims.ClaimStatus.rec (fun _ => Int32) 1 2 0 status
```

There is one argument per constructor, in declaration order.
An arm `A or B` supplies the same value for both constructors, and `_` supplies every constructor no earlier arm covered.
Lean's elaborator would instead generate a named matcher (`f.match_1`), but Lean shares structurally equal matchers between functions and renames them, and nothing in M4 consumes matcher metadata, so translation uses the recursor directly (plan, Scope Boundaries).
Building a definition on `.rec` is fine for the kernel; only Lean's code generator refuses it, and Warrant never compiles these definitions.

**Over an integer or an open enum**, a `switch` is a chain of `ite` tests in source order, with the `_` or `default` arm last wherever it was written, because C# takes it only when nothing else matches:

```lean
-- switch (code) { 1 => 10, >= 5 and < 9 => 20, _ => 0 }
ite (code = 1) 10 (ite (5 ≤ code ∧ code < 9) 20 0)
```

A `switch` *statement* takes the same two forms, with each section as one branch under the placement rules above.
Over a closed enum, a section that several constructors reach is `let`-bound once, as `branch`, and the recursor's arguments refer to it, so it is not copied.
A section that carries both `default` and `case` labels is rejected by extraction (chapter 3), because the default branch must come last in the `ite` chain while its `case` labels would have to be tested in order.

## Equality on records and closed types

C# `==` on a sealed record calls the compiler-generated `Equals`, which compares the fields in order.
Translation generates the same thing as a `Bool` function (KTD10):

```lean
def Cs.Claims.Payment.$eq (a b : Cs.Claims.Payment) : Bool :=
  decide (a.Id = b.Id) && decide (a.Amount = b.Amount) && decide (a.Status = b.Status)
```

A field of record type uses that record's `$eq`, and a field of closed type uses the closed type's index comparison.
For a closed type, `$index` gives each constructor its position, and `==` compares positions:

```lean
def Cs.Claims.Outcome.$index (o : Cs.Claims.Outcome) : Nat := @Cs.Claims.Outcome.rec (fun _ => Nat) 0 1 o
-- a == b   ↦   Nat.beq a.$index b.$index
```

The `0` and `1` here are raw `Nat` literals (`Expr.NatLit`), not `OfNat.ofNat` applications: `Nat` literals are the kernel's own, so the index needs no instance.

In a condition or theorem, `r == s` becomes `R.$eq r s = true`, which Init's `Bool` instance decides.

The alternative is a `DecidableEq` instance per type, so that `r = s` itself would be decidable, which is what design D13 originally said for closed classes (D13 now says `$index`).
`$eq` won for a reason that goes beyond M4 (KTD10): C# `==` on a record is whatever the generated `Equals` computes, and that is not always structural equality of the model.
Once M6 adds `decimal`, a record holding `1.0m` equals one holding `1.00m` in C#, while the model keeps mantissa and scale, so the two values are different terms.
`$eq` stays faithful there; `DecidableEq` would not.
The cost is small in M4: Lean's derived instance is a matcher with nested `dite` and rewriting proofs for a structure (a constructor-index comparison for an enum-like type), the kernel generates none of it, and nothing in M4 needs `r = s` as a proposition.
M5a, whose tactics will want `r = s`, can generate the bridge lemma `R.$eq r s = true ↔ r = s`, but only for records whose fields all have lawful equality, which records with `decimal` fields will not.

All of these shapes were checked in Lean 4.35.0, and checked again independently: a `.rec`-based `switch`, an `$index`, a fieldwise `$eq` over an `Int32` field and a closed field, and `decide` on each reduce in the kernel and depend on no axioms.
Hand-built versions were exported with lean4export and accepted by Warrant's kernel and by `lean-replay`, including names with `$` components, which Lean source would have to write with `«»` quotes.

## Declarations

Each unit becomes a `DefinitionDecl`:

- **Type**: the `∀` over the parameters (with `self` first for an instance member of a record) ending in the return type.
- **Value**: the `fun` over the same parameters ending in the translated body.
- **Reducibility**: `regular h`, where `h` is one more than the largest height among the definitions the body mentions, which is how Lean computes it; open-enum types and members are `abbrev`.
- **Safety**: safe.

Type units become `InductiveDecl`s for records and closed types, and `abbrev` definitions for open enums.

Translation hands the declarations to the engine in dependency order, and the engine admits them into a fork of the checked bundle (KTD17).
The bundle is checked once and then frozen, and every fork is an overlay on it, so units and tests cannot see each other's declarations and forks are cheap.
`KernelEnvironment` already forked this way internally; M4 made the fork public for a frozen base (plan, U1).
