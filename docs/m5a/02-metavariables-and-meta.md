# 2. Metavariables and the Meta layer

> Part of the [M5a design](README.md). Decisions: KTD1 to KTD5, KTD30 in the [plan](../plans/2026-11-03-0838-feat-m5a-meta-tactics-plan.md).

A tactic builds a proof a piece at a time.
Between steps the proof has holes, and the holes are what the developer sees as goals.
This chapter is about how those holes are represented, why the kernel must never accept one, and the layer, `Warrant.Meta`, that computes with terms that contain them.

## A hole is a metavariable

Take the false theorem from the README after `intro`:

```lean
?g  : ∀ (x : Int32), Increment x > x          -- the theorem's goal
-- intro x assigns
?g := fun (x : Int32) => ?g₁ x                 -- through a delayed assignment, below
?g₁ : Increment x > x                          -- the new goal, with x in its context
```

`?g` and `?g₁` are metavariables.
In Lean, and now in Warrant, a metavariable is a term kind of its own: `Expr.mvar (id)`.
Its type and the hypotheses it may mention are not stored in the term; they live in a `MetavarContext`, keyed by the id.

Warrant adds this kind to its one shared term type, `Warrant.Cic.Expr`, rather than giving Meta a separate representation (KTD1).
Lean does the same, and so does Ansatz, which first tried encoding holes as free variables with a separate unifier and abandoned it after the two disagreed about which holes were solved.
The cost is that the trusted `Warrant.Cic` changes, so the change is kept small:

| Addition | Where |
|---|---|
| `MVarId` and `MVarExpr`, hashing tag 13, structural and alpha equality | `src/Warrant.Cic/Expr.cs` |
| `LMVarId` and `Level.MVar`, for universe holes | `src/Warrant.Cic/Level.cs` |
| cached flags `HasExprMVar` and `HasLevelMVar` on every term, `HasMVar` on every level | both |

Level holes are needed because tactics instantiate universe-polymorphic lemmas.
`apply congrArg` must create `@congrArg.{?u, ?v}` and let unification decide the levels, as Lean's `mkConstWithFreshMVarLevels` does.

## The kernel never accepts one

A proof with a hole is not a proof.
The kernel therefore rejects any declaration whose type or value has a metavariable, before it type-checks anything, as Lean's C++ kernel does.
The message is Lean's, without its `(kernel) ` prefix: `declaration has metavariables 'name'`.

```csharp
// Kernel.Add, in outline (KTD1)
CheckNoMVar(decl);   // new: O(1) with the cached flags; expression and level holes
CheckNoFVar(decl);   // M2
TypeCheck(decl);
```

The check catches level holes too.
Ansatz's kernel misses them: its universe check returns "no undefined parameter" for a level metavariable, so `Sort ?u` would pass.
Warrant's tests put a level hole only inside a binder's domain, where no other check would look, and in a constant's universe argument (`PUnit.{?u}`).
Without the up-front check, Warrant's kernel accepted both theorems: the gap was real, and the check closes it.

Every place in the kernel that switches on a term's kind gets an explicit `MVar` arm (13 sites in Cic, the kernel and the NDJSON writer).
Today an unexpected kind in `WhnfCore` throws `InvalidOperationException("unreachable")`, which the engine does not catch; after U4 it throws a `KernelException`, and `InferTypeCore` says "kernel type checker does not support meta variables", Lean's wording.
`ExprOps` passes holes through unchanged, and `LevelOps` treats a level hole as an atom, so Meta can reuse both.

The engine adds a second guard of its own: after a script finishes, it instantiates the goal and refuses to call the kernel if any hole remains (chapter 4).
The kernel's check is the one that is trusted.

## Time limits in the kernel

The kernel's only limit today is fuel, charged in `Tick()`.
A 30-second limit per theorem (design Q8) needs the kernel to stop on time as well, so `KernelLimits` gains an optional deadline that `Tick()` checks (KTD2).
Reading the clock costs more than a step, so `Tick()` reads it on the first step and then once every 1,024 steps, against a monotonic clock (`Stopwatch`).
Passing the deadline raises the same `KernelResourceException` as running out of fuel, so a resource limit still only ever rejects.

## Why Meta has its own reduction and unification

Tactics need to reduce terms (`whnf`), infer their types, and above all unify: decide whether two terms can be made equal by filling holes, and fill them.
The kernel can do none of that with holes in the terms:

- Its definitional equality checks; it never assigns.
- It ignores transparency: it unfolds every definition, and theorems too.
  `simp` must match lemmas while unfolding only abbreviations, or it fires different lemmas from Lean's.
- It caches results, and a result computed while `?m` was unassigned is wrong once `?m` is assigned.
- After U4 it throws on any hole.

So `Warrant.Meta` reimplements Lean's `Meta` versions of these operations, ported function by function from Lean 4.35.0 (KTD3):

| Lean 4.35.0 | Lines | Warrant.Meta |
|---|---|---|
| `Lean/MetavarContext.lean` | 1,577 | `Basic/MetavarContext.cs`, `MkBinding.cs`, `InstantiateMVars.cs` |
| `Lean/LocalContext.lean` | 690 | `Basic/LocalContext.cs` |
| `Lean/Meta/Basic.lean` | 2,851 | `Basic/MetaM.cs` |
| `Lean/Meta/InferType.lean` | 580 | `Reduce/InferType.cs` |
| `Lean/Meta/WHNF.lean` | 1,096 | `Reduce/Whnf.cs` |
| `Lean/Meta/ExprDefEq.lean`, `LevelDefEq.lean` | 2,585, 183 | `Reduce/ExprDefEq.cs`, `LevelDefEq.cs` |

Meta still uses the kernel in two ways.
Pure helpers from `Warrant.Kernel` (substitution, level normalisation, inductive metadata, Nat literal arithmetic) are reused directly.
And when a term has no holes, Meta can hand it to the kernel to check, which is how `Meta.check` and the final admission work.
A disagreement between the two can only make a proof fail: if Meta thinks two terms are equal and the kernel does not, the certificate is rejected and reported as WRT0010 (chapter 4).

## The metavariable context

A `MetavarContext` holds, per metavariable, a declaration (its type, the local context it may use, a depth and a kind) and possibly an assignment.
It is immutable, built on `System.Collections.Immutable`, so saving and restoring state for backtracking is a reference copy, as Lean's persistent maps make it.

The three kinds matter:

| Kind | Created by | Assigned by unification? |
|---|---|---|
| natural | `apply`'s arguments, telescopes | yes |
| synthetic | instance arguments | only by instance resolution |
| synthetic opaque | goals | no; only a tactic assigns a goal |

A depth counter lets a tactic run a sub-search, such as `simp`'s side-condition prover or instance resolution, in which outer holes are read-only (`withNewMCtxDepth`).
In Lean 4.35.0, `withNewMCtxDepth` restores the whole saved context when it returns (`Lean/Meta/Basic.lean`, line 2008), so assignments made inside the sub-search are discarded; the callers instantiate the result before they leave it, and Warrant's port does the same.

Assignments are checked before they are made (`checkAssignment`):

```lean
?m := f ?m        -- rejected: ?m occurs in its own value
?m := y           -- rejected when y is not in ?m's local context
```

The second check is what keeps a hypothesis from escaping its scope into a proof.

## Delayed assignment

`intro` must produce a function whose body is a hole that mentions the bound variable:

```lean
?g := fun (x : Int32) => ?g₁       -- ?g₁'s context contains x
```

Assigned literally, this leaves `x` free in `?g₁`'s eventual value, which is outside the `fun`.
Lean's answer, ported as is (KTD3), is the delayed assignment.
`mkLambdaFVars [x] ?g₁` creates a fresh `?n` and records `?n #[x] := ?g₁`, and the term becomes `fun x => ?n x`.
When `?g₁` is later assigned a value `v` that has no holes left, `instantiateMVars` replaces `?n x` by `v` with `x` substituted, and not before.

This rule is the subtlest one in the port, and getting it wrong leaks free variables into a certificate.
The kernel's `CheckNoFVar` then rejects the certificate (WRT0010), so the failure is visible, but U5 tests delayed assignment directly and U11's tests chain `intro`, `apply` and `intro` so it does not get that far.
`instantiateMVars` is implemented in C++ in Lean 4.35.0 and is not in the toolchain's sources, so U5 ports its documented behaviour and checks it against the upstream source and Ansatz.

## Transparency

Meta unfolds definitions only as far as the current transparency allows (KTD5).
Lean 4.35.0 has six modes and five reducibility statuses:

```text
modes:     none < reducible < instances < implicit < default < all
statuses:  reducible, semireducible (the default), irreducible,
           instanceReducible (every instance), implicitReducible (for example Int.bmod)
```

`simp` and the discrimination trees work at `reducible`: `GT.gt b a` unfolds to `LT.lt a b`, but `Int32.add` does not unfold.
Instance resolution works at `instances`.
Unification in `apply` and `exact` works at `default`, which unfolds everything but irreducible definitions and theorems.

Statuses are attributes, which the NDJSON bundle does not carry, so they come from the attribute sidecar (chapter 5).
A missing entry means `semireducible`, so a missing `reducible` entry silently stops `simp` from seeing through an abbreviation; the sidecar therefore exports every non-default status, including the two that are new in 4.x.
In the committed sidecar, `Int32.add`, `Int32.toInt`, `Int.add`, `Int.emod` and `Int.bmod` are `implicitReducible`, and `Nat.add` is `instanceReducible`.
Translated declarations get their statuses from the engine: every translated `abbrev` (an open enum and its members, M4 docs/m4/05) is reducible, recursive definitions are irreducible (chapter 3), and the generated `casesOn` is reducible (chapter 4).

Some of what Lean's elaborator records is in neither the bundle nor the sidecar, so Meta reconstructs it: a projection function is recognised from its value, an auxiliary recursor by its name (an inductive type's `casesOn`, `recOn`, `brecOn`, `binductionOn` or `below`), the `@[match_pattern]` declarations of Init are a fixed list, and Lean's `backward.*` options are fixed at their 4.35.0 defaults.

## Budgets inside Meta

Meta charges its own fuel in `whnf`, `isDefEq` and `inferType`, the operations that can loop, and checks the theorem's deadline at the same points.
Running out is reported as WRT0006 naming tactic fuel, separately from kernel fuel (chapter 7).
