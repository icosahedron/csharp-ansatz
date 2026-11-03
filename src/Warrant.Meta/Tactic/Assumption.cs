using Warrant.Cic;

namespace Warrant.Meta;

public sealed partial class MetaM
{
    /// <summary>
    /// The newest hypothesis whose type is definitionally equal to <paramref name="type"/> (Lean's
    /// <c>findLocalDeclWithType?</c>, Lean/Meta/Tactic/Assumption.lean 16); implementation details are skipped.
    /// </summary>
    /// <returns>Its id, or null.</returns>
    public FVarId? FindLocalDeclWithType(Expr type)
    {
        ArgumentNullException.ThrowIfNull(type);
        foreach (var decl in LCtx.DeclsReversed())
        {
            Budget.Tick();
            if (!decl.IsImplementationDetail && IsDefEq(type, decl.Type))
            {
                return decl.FVarId;
            }
        }
        return null;
    }

    /// <summary>
    /// Closes the goal with a hypothesis of its type, and reports whether it found one (Lean's <c>MVarId.assumptionCore</c>,
    /// Assumption.lean 26).
    /// </summary>
    public bool AssumptionCore(MVarId mvarId) => WithContext(mvarId, () =>
    {
        CheckNotAssigned(mvarId, "assumption");
        if (FindLocalDeclWithType(GetMVarType(mvarId)) is not { } h)
        {
            return false;
        }
        Assign(mvarId, Expr.FVar(h));
        return true;
    });

    /// <summary>Closes the goal with a hypothesis of its type (Lean's <c>MVarId.assumption</c>).</summary>
    /// <exception cref="TacticException">There is none.</exception>
    public void Assumption(MVarId mvarId)
    {
        if (!AssumptionCore(mvarId))
        {
            throw new TacticException("assumption", mvarId, "Tactic `assumption` failed");
        }
    }
}
