using System.Collections.Immutable;
using Warrant.Cic;

namespace Warrant.Meta;

/// <summary>
/// One goal <c>cases</c> leaves (Lean's <c>CasesSubgoal</c>, Lean/Meta/Tactic/Cases.lean 155): an
/// <see cref="InductionSubgoal"/> and its constructor, with the split hypothesis mapped to <c>C params fields</c>.
/// </summary>
/// <param name="MVarId">The goal.</param>
/// <param name="Fields">The new hypotheses for the constructor's fields.</param>
/// <param name="Subst">What the old goal's hypotheses became; the split one is <c>C params fields</c>.</param>
/// <param name="CtorName">The constructor.</param>
public sealed record CasesSubgoal(MVarId MVarId, ImmutableArray<Expr> Fields, FVarSubst Subst, Name CtorName);

public sealed partial class MetaM
{
    private static readonly Name HEqName = Name.From("HEq");

    /// <summary>
    /// Splits the goal by the constructors of the hypothesis <paramref name="majorFVarId"/>'s type (Lean's
    /// <c>MVarId.cases</c>, Cases.lean 290), eliminating it with <c>T.casesOn</c>: one goal per constructor, in declaration
    /// order, named after it, with the constructor's fields as hypotheses and the hypothesis replaced by the constructor
    /// applied to them.
    /// </summary>
    /// <remarks>
    /// Only the path Lean takes for a type without indices is ported (KTD8). A type with indices, such as <c>a = b</c>,
    /// needs Lean's index generalization, equation unification and <c>noConfusion</c>, which no M5a goal needs, so it is
    /// reported as not supported yet.
    /// </remarks>
    /// <param name="mvarId">The goal.</param>
    /// <param name="majorFVarId">The hypothesis to split.</param>
    /// <returns>The new goals.</returns>
    /// <exception cref="TacticException">The hypothesis's type is not an inductive type with <c>casesOn</c>, or has indices.</exception>
    public IReadOnlyList<CasesSubgoal> Cases(MVarId mvarId, FVarId majorFVarId) => WithContext(mvarId, () =>
    {
        CheckNotAssigned(mvarId, "cases");
        var ival = MkCasesContext(majorFVarId) ?? throw TacticException.Failed("cases", mvarId, "not applicable to the given hypothesis");
        if (ival.NumIndices > 0)
        {
            throw TacticException.Failed("cases", mvarId, "cases on an indexed family is not supported yet");
        }
        RefuseUnassignedMVars("cases", mvarId);
        return InductionCasesOn(mvarId, majorFVarId, ival);
    });

    /// <summary>
    /// The inductive type of the hypothesis, if <c>cases</c> applies to it (Lean's <c>mkCasesContext?</c>, Cases.lean 166):
    /// <c>Eq</c> and <c>HEq</c> exist, its type reduces to a fully applied inductive type, and that type has <c>casesOn</c>.
    /// </summary>
    private InductiveInfo? MkCasesContext(FVarId majorFVarId)
    {
        if (Env.Find(TacticNames.Eq) is null || Env.Find(HEqName) is null)
        {
            return null;
        }
        var majorType = Whnf(GetLocalDecl(majorFVarId).Type);
        if (majorType.GetAppFn() is not ConstExpr c || Env.Find(c.Name) is not InductiveInfo ival)
        {
            return null;
        }
        if (majorType.GetAppNumArgs() != ival.NumIndices + ival.NumParams || Env.Find(ival.Name.Append("casesOn")) is null)
        {
            return null;
        }
        return ival;
    }

    /// <summary>
    /// <see cref="Induction"/> with <c>T.casesOn</c>, each goal labelled with its constructor (Lean's <c>inductionCasesOn</c>
    /// and <c>toCasesSubgoals</c>, Cases.lean 225 and 250).
    /// </summary>
    private List<CasesSubgoal> InductionCasesOn(MVarId mvarId, FVarId majorFVarId, InductiveInfo ival) => WithContext(mvarId, () =>
    {
        var majorType = InferType(Expr.FVar(majorFVarId));
        var (us, parameters) = GetInductiveUniverseAndParams(majorType);
        var subgoals = Induction(mvarId, majorFVarId, ival.Name.Append("casesOn"));
        var result = new List<CasesSubgoal>();
        for (int i = 0; i < subgoals.Count && i < ival.Constructors.Count; i++)
        {
            var s = subgoals[i];
            var ctorName = ival.Constructors[i];
            var ctorApp = ExprExtensions.MkAppN(ExprExtensions.MkAppN(Expr.Const(ctorName, us), parameters), s.Fields);
            result.Add(new CasesSubgoal(s.MVarId, s.Fields, s.Subst.Erase(majorFVarId).Insert(majorFVarId, ctorApp), ctorName));
        }
        return result;
    });

    /// <summary>The universe arguments and parameters of an inductive type (Lean's <c>getInductiveUniverseAndParams</c>, Cases.lean 23).</summary>
    private (EquatableArray<Level> Levels, Expr[] Params) GetInductiveUniverseAndParams(Expr type)
    {
        var whnf = WhnfD(type);
        if (whnf.GetAppFn() is not ConstExpr c || Env.Find(c.Name) is not InductiveInfo val)
        {
            throw new MetaException($"Failed to compile pattern matching: Expected an inductive type, but found\n  {Pp(type)}");
        }
        return (c.Levels, whnf.GetAppArgs()[..val.NumParams]);
    }
}
