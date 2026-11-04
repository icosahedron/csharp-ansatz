using System.Collections.Immutable;
using Warrant.Cic;
using Warrant.Kernel;

namespace Warrant.Meta;

/// <summary>
/// A rewrite rule <c>∀ xs, lhs = rhs</c> (Lean's <c>SimpTheorem</c>, Lean/Meta/Tactic/Simp/SimpTheorems.lean): a
/// global lemma, or a hypothesis that <c>contextual</c> adds, after simp's preprocessing.
/// </summary>
/// <remarks>
/// Lean stores a preprocessed global lemma as an auxiliary theorem (<c>_simp_1</c>); Warrant keeps the preprocessed
/// proof term itself, such as <c>fun … => propext (ite_eq_iff …)</c>, so a certificate names only bundle constants.
/// </remarks>
public sealed class SimpTheorem
{
    internal SimpTheorem(Name? declName, Expr? fvar, ImmutableArray<DiscrTreeKey> keys, EquatableArray<Name> levelParams, Expr proof, Expr type, int priority, bool post, bool rfl)
    {
        DeclName = declName;
        FVar = fvar;
        Keys = keys;
        LevelParams = levelParams;
        Proof = proof;
        Type = type;
        Priority = priority;
        Post = post;
        Rfl = rfl;
    }

    /// <summary>The lemma's name, for a global lemma.</summary>
    public Name? DeclName { get; }

    /// <summary>The hypothesis, for a local one.</summary>
    public Expr? FVar { get; }

    /// <summary>The discrimination-tree keys of the left side.</summary>
    public ImmutableArray<DiscrTreeKey> Keys { get; }

    /// <summary>The universe parameters <see cref="Proof"/> and <see cref="Type"/> abstract over.</summary>
    public EquatableArray<Name> LevelParams { get; }

    /// <summary>The proof of <see cref="Type"/>.</summary>
    public Expr Proof { get; }

    /// <summary><c>∀ xs, lhs = rhs</c>.</summary>
    public Expr Type { get; }

    /// <summary>The priority; higher ones are tried first.</summary>
    public int Priority { get; }

    /// <summary>Whether it rewrites after the subterms are simplified (Lean's <c>post</c>), rather than before.</summary>
    public bool Post { get; }

    /// <summary>Whether both sides are equal by definition, so a rewrite needs no proof (Lean's <c>rfl</c>).</summary>
    public bool Rfl { get; }

    /// <summary>The proof and its type at fresh universe metavariables (Lean's <c>SimpTheorem.getValue</c>).</summary>
    internal (Expr Value, Expr Type) Instantiate(MetaM m)
    {
        if (LevelParams.Count == 0)
        {
            return (Proof, Type);
        }
        var us = m.MkFreshLevelMVars(LevelParams.Count);
        return (ExprOps.InstantiateLevelParams(Proof, LevelParams, us), ExprOps.InstantiateLevelParams(Type, LevelParams, us));
    }

    /// <inheritdoc/>
    public override string ToString() => DeclName?.ToString() ?? FVar?.ToString() ?? "?";
}

/// <summary>
/// A set of simp theorems, indexed by their left sides in a <c>pre</c> and a <c>post</c> discrimination tree (Lean's
/// <c>SimpTheorems</c>). It is filled once and then only read.
/// </summary>
public sealed class SimpTheorems
{
    /// <summary>The theorems tried before a term's subterms are simplified.</summary>
    public DiscrTree<SimpTheorem> Pre { get; } = new();

    /// <summary>The theorems tried after.</summary>
    public DiscrTree<SimpTheorem> Post { get; } = new();

    /// <summary>Adds a theorem.</summary>
    public void Add(SimpTheorem theorem)
    {
        ArgumentNullException.ThrowIfNull(theorem);
        (theorem.Post ? Post : Pre).Insert(theorem.Keys, theorem);
    }

    /// <summary>Adds every theorem of <paramref name="theorems"/>.</summary>
    public void AddRange(IEnumerable<SimpTheorem> theorems)
    {
        ArgumentNullException.ThrowIfNull(theorems);
        foreach (var t in theorems)
        {
            Add(t);
        }
    }
}

// Lean/Meta/Tactic/Simp/SimpTheorems.lean: preprocess (with proofs), mkSimpTheoremFromConst and
// mkSimpTheoremFromExpr. The keys come from U16's SimpTheoremKeys. Permutation lemmas are not
// detected: the default set has none, so AC ordering is not ported (plan U17).
public sealed partial class MetaM
{
    /// <summary>Lean's default simp priority.</summary>
    public const int DefaultSimpPriority = 1000;

    /// <summary>
    /// The simp theorems Lean makes from the lemma <paramref name="declName"/> (Lean's <c>mkSimpTheoremFromConst</c>):
    /// one per conjunct, after turning <c>↔</c> into <c>=</c> with <c>propext</c>, <c>¬p</c> into <c>p = False</c>, and
    /// another proposition <c>p</c> into <c>p = True</c>; <paramref name="inverse"/> rewrites right to left.
    /// </summary>
    /// <exception cref="MetaException">The constant is not a proof of a proposition, or simp cannot use it.</exception>
    public IReadOnlyList<SimpTheorem> MkSimpTheoremsFromConst(Name declName, bool post = true, bool inverse = false, int priority = DefaultSimpPriority)
    {
        ArgumentNullException.ThrowIfNull(declName);
        var info = GetConstInfo(declName);
        var val = Expr.Const(declName, EquatableArray.Create<Level>([.. info.LevelParams.Select(Level.Param)]));
        return WithSimpGlobalConfig(() =>
        {
            var type = info.Type;
            if (!IsProp(type))
            {
                throw new MetaException($"invalid 'simp', proposition expected\n  {type}");
            }
            if (inverse || ShouldPreprocessSimp(type))
            {
                bool isEq = ForallTelescopeReducing(type, (_, body) => ExprOps.IsAppOfArity(body, SimpNames.Eq, 3));
                bool rfl = inverse && isEq && Attributes.HasDefEqAttribute(declName);
                return PreprocessSimpProof(val, type, inverse)
                    .Select(p => new SimpTheorem(declName, null, SimpTheoremKeys(p.Type), info.LevelParams, p.Proof, p.Type, priority, post, rfl))
                    .ToList();
            }
            return [new SimpTheorem(declName, null, SimpTheoremKeys(type), info.LevelParams, val, type, priority, post, Attributes.HasDefEqAttribute(declName))];
        });
    }

    /// <summary>
    /// The simp theorems made from a hypothesis or other proof <paramref name="proof"/> (Lean's
    /// <c>mkSimpTheoremFromExpr</c> on a non-constant): preprocessed as a lemma is, keyed with its arguments not indexed.
    /// </summary>
    public IReadOnlyList<SimpTheorem> MkSimpTheoremsFromProof(Expr proof, int priority = DefaultSimpPriority)
    {
        ArgumentNullException.ThrowIfNull(proof);
        return WithReducible(() =>
        {
            var type = this.InstantiateMVars(InferType(proof));
            if (!IsProp(type))
            {
                throw new MetaException($"invalid 'simp', proposition expected\n  {type}");
            }
            return PreprocessSimpProof(proof, type, inv: false)
                .Select(p => new SimpTheorem(null, proof is FVarExpr ? proof : null, SimpTheoremKeys(p.Type, noIndexAtArgs: true), [], p.Proof, p.Type, priority, post: true, rfl: false))
                .ToList();
        });
    }

    /// <summary>Lean's <c>simpGlobalConfig</c>: reducible, no iota, no projection reduction, no zeta-delta.</summary>
    internal T WithSimpGlobalConfig<T>(Func<T> k) =>
        WithConfig(c => c with { Iota = false, Proj = ProjReductionKind.No, ZetaDelta = false, Transparency = TransparencyMode.Reducible }, k);

    // Lean's preprocess.go: each (proof, type) with type an equation.
    private List<(Expr Proof, Expr Type)> PreprocessSimpProof(Expr e, Expr type, bool inv)
    {
        type = Whnf(type);
        if (type is ForallExpr)
        {
            return ForallTelescopeReducing(type, (xs, body) =>
                PreprocessSimpProof(ExprExtensions.MkAppN(e, xs), body, inv)
                    .Select(p => (MkLambdaFVars(xs, p.Proof), MkForallFVars(xs, p.Type)))
                    .ToList());
        }
        var args = type.GetAppArgs();
        if (ExprOps.IsAppOfArity(type, SimpNames.Eq, 3))
        {
            return [inv ? (MkEqSymm(e), MkEq(args[2], args[1])) : (e, type)];
        }
        if (ExprOps.IsAppOfArity(type, SimpNames.Iff, 2))
        {
            return [inv ? (MkEqSymm(MkPropExt(e)), MkEq(args[1], args[0])) : (MkPropExt(e), MkEq(args[0], args[1]))];
        }
        if (ExprOps.IsAppOfArity(type, SimpNames.Ne, 3))
        {
            if (inv)
            {
                throw new MetaException("Invalid `←` modifier: Cannot be applied to simp theorems of the form `a ≠ b`");
            }
            return [NegatedEq(e, args[1], args[2])];
        }
        if (ExprOps.IsAppOfArity(type, SimpNames.Not, 1))
        {
            if (inv)
            {
                throw new MetaException("Invalid `←` modifier: Cannot be applied to simp theorems of the form `¬ P`");
            }
            var p = args[0];
            if (ExprOps.IsAppOfArity(p, SimpNames.Eq, 3) && p.GetAppArgs() is [_, var lhs, var rhs]
                && (rhs.IsConstOf(SimpNames.BoolTrue) || rhs.IsConstOf(SimpNames.BoolFalse)))
            {
                return [NegatedEq(e, lhs, rhs)];
            }
            return [(MkEqFalse(e), MkEq(p, Expr.Const(SimpNames.False)))];
        }
        if (ExprOps.IsAppOfArity(type, SimpNames.And, 2))
        {
            return [.. PreprocessSimpProof(Expr.Proj(SimpNames.And, 0, e), args[0], inv), .. PreprocessSimpProof(Expr.Proj(SimpNames.And, 1, e), args[1], inv)];
        }
        if (inv)
        {
            throw new MetaException("Invalid `←` modifier: Cannot be applied to a rule that rewrites to `True`");
        }
        return [(MkEqTrue(e), MkEq(type, Expr.Const(SimpNames.True)))];

        // `lhs ≠ rhs`: `lhs = false` or `lhs = true` for a Bool constant, else `(lhs = rhs) = False`.
        (Expr, Expr) NegatedEq(Expr h, Expr lhs, Expr rhs) =>
            rhs.IsConstOf(SimpNames.BoolTrue) ? (MkAppM(SimpNames.BoolOfNotEqTrue, h), MkEq(lhs, Expr.Const(SimpNames.BoolFalse)))
            : rhs.IsConstOf(SimpNames.BoolFalse) ? (MkAppM(SimpNames.BoolOfNotEqFalse, h), MkEq(lhs, Expr.Const(SimpNames.BoolTrue)))
            : (MkEqFalse(h), MkEq(MkEq(lhs, rhs), Expr.Const(SimpNames.False)));
    }
}
