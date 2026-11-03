using System.Collections.Immutable;
using Warrant.Cic;
using Warrant.Kernel;

namespace Warrant.Meta;

/// <summary>
/// A global instance as instance resolution indexes it (Lean's <c>InstanceEntry</c>,
/// Lean/Meta/Instances.lean): its keys, recomputed from its kernel-checked type, and the order in
/// which its instance arguments are synthesized.
/// </summary>
/// <param name="Name">The instance.</param>
/// <param name="Priority">Its priority.</param>
/// <param name="Keys">The discrimination-tree path of its type's conclusion (Lean's <c>mkInstanceKey</c>).</param>
/// <param name="SynthOrder">The positions of its instance arguments, in synthesis order (Lean's <c>computeSynthOrder</c>).</param>
public sealed record InstanceIndexEntry(Name Name, int Priority, ImmutableArray<DiscrTreeKey> Keys, ImmutableArray<int> SynthOrder);

// The global instance index (a port of Lean/Meta/Instances.lean's addInstance, mkInstanceKey and
// computeSynthOrder, and of Class.lean's computeOutLevelParams) over the sidecar's instances
// (plan U16, KTD10).
public sealed partial class MetaM
{
    private static readonly Name SemiOutParamName = Name.From("semiOutParam");

    private readonly Dictionary<Name, ImmutableArray<int>> _outLevelParamsCache = [];
    private (int Version, DiscrTree<InstanceIndexEntry> Tree)? _instanceIndex;

    /// <summary>
    /// The discrimination tree of the global instances (Lean's <c>getGlobalInstancesIndex</c>), built
    /// from <see cref="Attributes"/> in registration order and rebuilt when an instance is added. An
    /// instance whose constant is not in the environment is left out.
    /// </summary>
    /// <remarks>
    /// Keys are computed when the index is built, so reducibility statuses that change an instance's
    /// keys must be set before the first resolution.
    /// </remarks>
    public DiscrTree<InstanceIndexEntry> GetGlobalInstancesIndex()
    {
        int version = Attributes.InstanceVersion;
        if (_instanceIndex is { } cached && cached.Version == version)
        {
            return cached.Tree;
        }
        var tree = new DiscrTree<InstanceIndexEntry>();
        bool complete = true;
        // Lean's addInstance runs at the default configuration, outside any local context.
        WithReader(_ => MetaContext.Empty, () =>
        {
            foreach (var inst in Attributes.Instances)
            {
                if (Env.Find(inst.Name) is null)
                {
                    complete = false;
                    continue;
                }
                var entry = new InstanceIndexEntry(inst.Name, inst.Priority, MkInstanceKey(inst.Name), ComputeSynthOrder(inst.Name));
                tree.Insert(entry.Keys, entry);
            }
            return 0;
        });
        _instanceIndex = complete ? (version, tree) : null;
        return tree;
    }

    /// <summary>
    /// The discrimination-tree path of the conclusion of <paramref name="declName"/>'s type, its
    /// binders replaced by metavariables (Lean's <c>mkInstanceKey</c>).
    /// </summary>
    public ImmutableArray<DiscrTreeKey> MkInstanceKey(Name declName)
    {
        ArgumentNullException.ThrowIfNull(declName);
        var type = GetConstInfo(declName).Type;
        return WithNewMCtxDepth(() =>
        {
            var (_, _, body) = ForallMetaTelescopeReducing(type);
            return DiscrTree.MkPath(this, body);
        });
    }

    /// <summary>
    /// The order in which the instance arguments of <paramref name="declName"/> are synthesized
    /// (Lean's <c>computeSynthOrder</c>): the first one whose non-out-parameters are all known,
    /// repeatedly, so out-parameters are filled before they are needed; otherwise left to right.
    /// </summary>
    public ImmutableArray<int> ComputeSynthOrder(Name declName)
    {
        ArgumentNullException.ThrowIfNull(declName);
        var instTy = GetConstInfo(declName).Type;
        var projInfo = GetProjectionFnInfo(declName);
        return WithReducible(() => WithNewMCtxDepth(() =>
        {
            var (argMVars, argBIs, ty) = ForallMetaTelescopeReducing(instTy);
            ty = Whnf(ty);
            return ForallTelescopeReducing(instTy, (argVars, _) =>
            {
                var tyOutParams = SemiOutParamPositionsOf(ty);
                var tyArgs = ty.GetAppArgs();
                for (int i = 0; i < tyArgs.Length; i++)
                {
                    if (!tyOutParams.Contains(i))
                    {
                        AssignMVarsIn(tyArgs[i]);
                    }
                }
                var synthed = ImmutableArray.CreateBuilder<int>();
                var toSynth = Enumerable.Range(0, argMVars.Length).Where(i => argBIs[i] == BinderInfo.InstImplicit).ToList();
                while (toSynth.Count > 0)
                {
                    int next = toSynth.FirstOrDefault(IsReady, toSynth[0]);
                    synthed.Add(next);
                    toSynth.Remove(next);
                    AssignMVarsIn(InferType(argMVars[next]));
                    AssignMVarsIn(argMVars[next]);
                }
                return synthed.ToImmutable();

                bool IsReady(int i)
                {
                    var argTy = this.InstantiateMVars(InferType(argMVars[i]));
                    if (projInfo is not null && projInfo.NumParams == i)
                    {
                        AssignMVarsIn(argTy);
                        return true;
                    }
                    return ForallTelescopeReducing(argTy, (_, t) =>
                    {
                        t = Whnf(t);
                        var outs = SemiOutParamPositionsOf(t);
                        var args = t.GetAppArgs();
                        for (int j = 0; j < args.Length; j++)
                        {
                            if (!outs.Contains(j) && this.InstantiateMVars(args[j]).HasExprMVar)
                            {
                                return false;
                            }
                        }
                        return true;
                    });
                }

                // Assigns the argument metavariables in e (and in their types) their free variables.
                void AssignMVarsIn(Expr e)
                {
                    foreach (var mvarId in this.GetMVars(e))
                    {
                        int i = Array.FindIndex(argMVars, x => ((MVarExpr)x).Id == mvarId);
                        if (i >= 0)
                        {
                            Assign(mvarId, argVars[i]);
                        }
                        AssignMVarsIn(InferType(Expr.MVar(mvarId)));
                    }
                }
            });
        }));
    }

    // The out- and semi-out-parameter positions of the class `classTy` is an application of.
    private HashSet<int> SemiOutParamPositionsOf(Expr classTy)
    {
        if (classTy.GetAppFn() is not ConstExpr c)
        {
            return [];
        }
        return ForallTelescopeReducing(InferType(c), (args, _) =>
        {
            var pos = new HashSet<int>(Attributes.GetOutParams(c.Name) ?? []);
            for (int i = 0; i < args.Length; i++)
            {
                if (InferType(args[i]).IsAppOf(SemiOutParamName))
                {
                    pos.Add(i);
                }
            }
            return pos;
        });
    }

    /// <summary>
    /// The positions of the universe parameters of <paramref name="className"/> that occur only in
    /// its out-parameters' types (Lean's <c>getOutLevelParamPositions?</c>, computed as Class.lean's
    /// <c>computeOutLevelParams</c> does), or <see langword="null"/> if it is not a class.
    /// </summary>
    public ImmutableArray<int>? GetOutLevelParamPositions(Name className)
    {
        ArgumentNullException.ThrowIfNull(className);
        if (Attributes.GetOutParams(className) is not { } outParams || Env.Find(className) is not { } cinfo)
        {
            return null;
        }
        if (_outLevelParamsCache.TryGetValue(className, out var cached))
        {
            return cached;
        }
        var nonOut = new HashSet<Name>();
        var t = cinfo.Type;
        for (int i = 0; t is ForallExpr f; i++, t = f.Body)
        {
            if (!outParams.Contains(i))
            {
                CollectLevelParams(f.BinderType, nonOut);
            }
        }
        var result = Enumerable.Range(0, cinfo.LevelParams.Count).Where(i => !nonOut.Contains(cinfo.LevelParams[i])).ToImmutableArray();
        _outLevelParamsCache[className] = result;
        return result;
    }

    private static void CollectLevelParams(Expr e, HashSet<Name> into)
    {
        if (!e.HasLevelParam)
        {
            return;
        }
        ExprOps.ForEach(e, (x, _) =>
        {
            if (!x.HasLevelParam)
            {
                return false;
            }
            switch (x)
            {
                case ConstExpr c:
                    foreach (var l in c.Levels)
                    {
                        Collect(l);
                    }
                    break;
                case SortExpr s:
                    Collect(s.Level);
                    break;
            }
            return true;
        });

        void Collect(Level l)
        {
            if (!l.HasParam)
            {
                return;
            }
            if (l.Kind == LevelKind.Param)
            {
                into.Add(l.ParamName!);
            }
            if (l.Lhs is { } a)
            {
                Collect(a);
            }
            if (l.Rhs is { } b)
            {
                Collect(b);
            }
        }
    }
}
