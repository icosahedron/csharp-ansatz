using System.Collections.Immutable;
using Warrant.Cic;
using Warrant.Kernel;

namespace Warrant.Meta;

/// <summary>
/// What a tactic substituted for the hypotheses of the goal it replaced (Lean's <c>FVarSubst</c>,
/// Lean/Meta/Tactic/FVarSubst.lean): a map from a hypothesis of the old goal to the term that stands for it in a new goal,
/// whose free variables are the new goal's. <c>cases</c> records that the variable it split became
/// <c>C params fields</c>, and <c>induction</c> that each reverted hypothesis was introduced again. Immutable.
/// </summary>
public sealed class FVarSubst
{
    // Lean's AssocList: the most recent entry first.
    private readonly ImmutableList<KeyValuePair<FVarId, Expr>> _map;

    private FVarSubst(ImmutableList<KeyValuePair<FVarId, Expr>> map) => _map = map;

    /// <summary>The empty substitution.</summary>
    public static FVarSubst Empty { get; } = new([]);

    /// <summary>Whether the substitution has no entries.</summary>
    public bool IsEmpty => _map.IsEmpty;

    /// <summary>Whether <paramref name="fvarId"/> has an entry.</summary>
    public bool Contains(FVarId fvarId) => _map.Any(p => p.Key == fvarId);

    /// <summary>
    /// Adds <c>fvarId ↦ v</c> unless <paramref name="fvarId"/> already has an entry, replacing <paramref name="fvarId"/> by
    /// <paramref name="v"/> in the existing entries (Lean's <c>FVarSubst.insert</c>).
    /// </summary>
    public FVarSubst Insert(FVarId fvarId, Expr v)
    {
        ArgumentNullException.ThrowIfNull(v);
        if (Contains(fvarId))
        {
            return this;
        }
        var map = _map.Select(p => new KeyValuePair<FVarId, Expr>(p.Key, ReplaceFVarId(p.Value, fvarId, v))).ToImmutableList();
        return new(map.Insert(0, new(fvarId, v)));
    }

    /// <summary>Removes the entry of <paramref name="fvarId"/> (Lean's <c>FVarSubst.erase</c>).</summary>
    public FVarSubst Erase(FVarId fvarId) => new(_map.RemoveAll(p => p.Key == fvarId));

    /// <summary>The entry of <paramref name="fvarId"/>, or null (Lean's <c>FVarSubst.find?</c>).</summary>
    public Expr? Find(FVarId fvarId) => _map.FirstOrDefault(p => p.Key == fvarId).Value;

    /// <summary>The entry of <paramref name="fvarId"/>, or the variable itself when it was not replaced (Lean's <c>FVarSubst.get</c>).</summary>
    public Expr Get(FVarId fvarId) => Find(fvarId) ?? Expr.FVar(fvarId);

    /// <summary>Replaces each variable with an entry by its term in <paramref name="e"/> (Lean's <c>FVarSubst.apply</c>).</summary>
    public Expr Apply(Expr e)
    {
        ArgumentNullException.ThrowIfNull(e);
        if (_map.IsEmpty || !e.HasFVar)
        {
            return e;
        }
        return ExprOps.Replace(e, (x, _) => x switch
        {
            FVarExpr f => Find(f.Id) ?? x,
            _ when !x.HasFVar => x,
            _ => null,
        });
    }

    private static Expr ReplaceFVarId(Expr e, FVarId fvarId, Expr v) =>
        !e.HasFVar ? e : ExprOps.Replace(e, (x, _) => x switch
        {
            FVarExpr f => f.Id == fvarId ? v : x,
            _ when !x.HasFVar => x,
            _ => null,
        });
}
