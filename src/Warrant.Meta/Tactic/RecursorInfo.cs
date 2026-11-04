using System.Collections.Immutable;
using Warrant.Cic;

namespace Warrant.Meta;

/// <summary>
/// Where one universe argument of a recursor comes from (Lean's <c>RecursorUnivLevelPos</c>, Lean/Meta/RecursorInfo.lean 16):
/// the motive's universe (<see cref="MajorTypeIndex"/> null), or the given universe argument of the major premise's type.
/// </summary>
/// <param name="MajorTypeIndex">The position among the major premise type's universe arguments; null for the motive's.</param>
public sealed record RecursorUnivLevelPos(int? MajorTypeIndex)
{
    /// <summary>The motive's universe.</summary>
    public static RecursorUnivLevelPos Motive { get; } = new((int?)null);
}

/// <summary>
/// The shape of an eliminator that <c>induction</c> and <c>cases</c> apply (Lean's <c>RecursorInfo</c>,
/// Lean/Meta/RecursorInfo.lean 24): <c>T.rec</c>, or an auxiliary recursor such as <c>T.casesOn</c>.
/// </summary>
/// <param name="RecursorName">The eliminator.</param>
/// <param name="TypeName">The inductive type it eliminates.</param>
/// <param name="UnivLevelPos">Where each of its universe parameters comes from.</param>
/// <param name="DepElim">Whether the motive takes the major premise.</param>
/// <param name="Recursive">Whether a minor premise has an induction hypothesis.</param>
/// <param name="NumArgs">Its number of arguments.</param>
/// <param name="MajorPos">The position of the major premise.</param>
/// <param name="ParamsPos">
/// For each parameter, its position among the major premise type's arguments; null for an instance-implicit parameter
/// that is synthesized instead.
/// </param>
/// <param name="IndicesPos">For each index, its position among the major premise type's arguments.</param>
/// <param name="ProduceMotive">For each minor premise, whether it produces the motive.</param>
public sealed record MetaRecursorInfo(
    Name RecursorName,
    Name TypeName,
    ImmutableArray<RecursorUnivLevelPos> UnivLevelPos,
    bool DepElim,
    bool Recursive,
    int NumArgs,
    int MajorPos,
    ImmutableArray<int?> ParamsPos,
    ImmutableArray<int> IndicesPos,
    ImmutableArray<bool> ProduceMotive)
{
    /// <summary>The number of parameters.</summary>
    public int NumParams => ParamsPos.Length;

    /// <summary>The number of indices.</summary>
    public int NumIndices => IndicesPos.Length;

    /// <summary>The motive's position: right after the parameters.</summary>
    public int MotivePos => NumParams;

    /// <summary>The position of the first index, right before the major premise.</summary>
    public int FirstIndexPos => MajorPos - NumIndices;
}

public sealed partial class MetaM
{
    /// <summary>
    /// The shape of the eliminator <paramref name="declName"/> (Lean's <c>mkRecursorInfo</c> and <c>mkRecursorInfoCore</c>,
    /// RecursorInfo.lean 202 and 243). The major premise of <c>T.rec</c> is the motive's last argument; that of an
    /// auxiliary recursor such as <c>T.casesOn</c> is computed from <c>T.rec</c>. Warrant has no <c>[recursor]</c>
    /// attribute, so a user-defined eliminator must take its major premise as the motive's last argument.
    /// </summary>
    /// <exception cref="MetaException">The constant does not have the shape of an eliminator.</exception>
    public MetaRecursorInfo MkRecursorInfo(Name declName)
    {
        ArgumentNullException.ThrowIfNull(declName);
        var cinfo = GetConstInfo(declName);
        var majorPosQ = GetMajorPosIfAuxRecursor(declName);
        return ForallTelescopeReducing(cinfo.Type, (xs, type) =>
        {
            var motive = type.GetAppFn();
            var motiveArgs = type.GetAppArgs();
            if (motive is not FVarExpr || !motiveArgs.All(a => a is FVarExpr))
            {
                throw new MetaException($"invalid user defined recursor `{declName}`, result type must be of the form `C t`, where `C` is a bound variable, and t is a (possibly empty) sequence of bound variables");
            }
            int numParams = Array.IndexOf(xs, motive);
            if (numParams < 0)
            {
                numParams = xs.Length;
            }
            Expr major;
            int majorPos;
            bool depElim;
            if (majorPosQ is { } given)
            {
                if (given >= xs.Length)
                {
                    throw new MetaException($"invalid major premise position for user defined recursor, recursor has only {xs.Length} arguments");
                }
                (major, majorPos, depElim) = (xs[given], given, motiveArgs.Contains(xs[given]));
            }
            else
            {
                if (motiveArgs.Length == 0)
                {
                    throw new MetaException($"invalid user defined recursor, `{declName}` does not support dependent elimination, and position of the major premise was not specified");
                }
                major = motiveArgs[^1];
                majorPos = Array.IndexOf(xs, major);
                if (majorPos < 0)
                {
                    throw new MetaException($"ill-formed recursor `{declName}`");
                }
                depElim = true;
            }
            int numIndices = depElim ? motiveArgs.Length - 1 : motiveArgs.Length;
            if (majorPos < numIndices)
            {
                throw new MetaException($"invalid user defined recursor `{declName}`, indices must occur before major premise");
            }
            var majorType = InferType(major);
            if (majorType.GetAppFn() is not ConstExpr { Name: var iname, Levels: var ilevels })
            {
                throw new MetaException($"invalid user defined recursor `{declName}`, type of the major premise must be of the form (I ...), where I is a constant");
            }
            var iargs = majorType.GetAppArgs();

            var paramsPos = ImmutableArray.CreateBuilder<int?>();
            for (int i = 0; i < numParams; i++)
            {
                int j = Array.FindIndex(iargs, a => IsDefEq(a, xs[i]));
                if (j >= 0)
                {
                    paramsPos.Add(j);
                }
                else if (GetFVarLocalDecl(xs[i]).BinderInfo == BinderInfo.InstImplicit)
                {
                    paramsPos.Add(null);
                }
                else
                {
                    throw new MetaException($"invalid user defined recursor `{declName}`, type of the major premise does not contain the recursor parameter");
                }
            }
            var indicesPos = ImmutableArray.CreateBuilder<int>();
            for (int i = 0; i < numIndices; i++)
            {
                var x = xs[majorPos - numIndices + i];
                int j = Array.FindIndex(iargs, a => IsDefEq(a, x));
                indicesPos.Add(j >= 0 ? j : throw new MetaException($"invalid user defined recursor `{declName}`, type of the major premise does not contain the recursor index"));
            }

            var motiveType = InferType(motive);
            return ForallTelescopeReducing(motiveType, (motiveTypeParams, motiveResultType) =>
            {
                if (motiveResultType is not SortExpr { Level: var motiveLvl } || motiveArgs.Length != motiveTypeParams.Length)
                {
                    throw new MetaException($"invalid user defined recursor `{declName}`, motive must have a type of the form (C : Pi (i : B A), I A i -> Type), where A is a (possibly empty) sequence of variables (aka parameters), (i : B A) is a (possibly empty) telescope (aka indices), and I is a constant");
                }
                if (motiveLvl.Kind is not (LevelKind.Zero or LevelKind.Param))
                {
                    throw new MetaException($"invalid user defined recursor `{declName}`, motive result sort must be Prop or `Sort u` where u is a universe level parameter");
                }
                var univLevelPos = ImmutableArray.CreateBuilder<RecursorUnivLevelPos>();
                foreach (var p in cinfo.LevelParams)
                {
                    var param = Level.Param(p);
                    if (motiveLvl == param)
                    {
                        univLevelPos.Add(RecursorUnivLevelPos.Motive);
                        continue;
                    }
                    int i = ilevels.ToList().FindIndex(u => u == param);
                    univLevelPos.Add(i >= 0 ? new RecursorUnivLevelPos(i) : throw new MetaException($"invalid user defined recursor `{declName}`, major premise type does not contain universe level parameter `{p}`"));
                }

                // getProduceMotiveAndRecursive (RecursorInfo.lean 175).
                var produceMotive = ImmutableArray.CreateBuilder<bool>();
                bool recursive = false;
                for (int i = numParams + 1; i < xs.Length; i++)
                {
                    if (majorPos - numIndices <= i && i <= majorPos)
                    {
                        continue;
                    }
                    var xType = InferType(xs[i]);
                    ForallTelescopeReducing(xType, (minorArgs, minorResultType) =>
                    {
                        produceMotive.Add(minorResultType.GetAppFn() == motive);
                        recursive = recursive || minorArgs.Any(a => ExprOpsFind(InferType(a), motive));
                        return 0;
                    });
                }
                return new MetaRecursorInfo(
                    declName, iname, univLevelPos.ToImmutable(), depElim, recursive, xs.Length, majorPos,
                    paramsPos.ToImmutable(), indicesPos.ToImmutable(), produceMotive.ToImmutable());
            });
        });

        static bool ExprOpsFind(Expr e, Expr target) => Kernel.ExprOps.Find(e, (x, _) => x == target) is not null;
    }

    /// <summary>
    /// The major premise's position for an auxiliary recursor (Lean's <c>getMajorPosIfAuxRecursor?</c>,
    /// RecursorInfo.lean 78): after the parameters, the indices and, for <c>casesOn</c>, one motive, else all the motives.
    /// </summary>
    private int? GetMajorPosIfAuxRecursor(Name declName)
    {
        if (!IsAuxRecursor(declName) || declName.Kind != NameKind.Str || declName.Prefix is not { } p)
        {
            return null;
        }
        var s = declName.StringComponent;
        if (s is not ("recOn" or "casesOn" or "brecOn"))
        {
            return null;
        }
        if (Env.Find(p.Append("rec")) is not Cic.RecursorInfo val)
        {
            throw new MetaException($"unknown recursor '{p.Append("rec")}'");
        }
        return val.NumParams + val.NumIndices + (s == "casesOn" ? 1 : val.NumMotives);
    }
}
