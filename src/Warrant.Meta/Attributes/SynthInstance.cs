using System.Collections.Immutable;
using Warrant.Cic;
using Warrant.Kernel;

namespace Warrant.Meta;

/// <summary>The bounds of one instance resolution (KTD10).</summary>
/// <param name="MaxDepth">How deeply instances may be nested in a solution (a goal's subgoals are one level deeper).</param>
/// <param name="MaxSteps">How many instances may be tried in all before the search gives up.</param>
public sealed record SynthInstanceLimits(int MaxDepth = 32, int MaxSteps = 10_000)
{
    /// <summary>The defaults.</summary>
    public static SynthInstanceLimits Default { get; } = new();
}

// Instance resolution (plan U16, KTD10; docs/m5a/05 "Instances"): a port of Lean 4.35.0's
// Lean/Meta/SynthInstance.lean in which the tabled resolution loop (generator and consumer nodes,
// answers and waiters) is replaced by a depth-first search with backtracking, bounded in depth and
// in the number of instances tried. Kept from Lean: getInstances (the instance discrimination tree,
// priorities, local instances), getSubgoals, tryResolve, the `canonInstances` cut (a goal without
// metavariables takes its first answer), preprocess and preprocessOutParam, assignOutParams, the
// final check, and synthPending. Not kept: tabling, the result cache, removeUnusedArguments and
// maxResultSize, which matter for Mathlib's deep and cyclic class hierarchies but not for Init's
// instances at Int32, Int64, Int, Nat and Bool.
public sealed partial class MetaM
{
    // Lean's maxSynthPendingDepth default.
    private const int MaxSynthPendingDepth = 1;

    private int _synthPendingDepth;
    private int _synthSteps;

    /// <summary>The bounds of instance resolution.</summary>
    public SynthInstanceLimits SynthInstanceLimits { get; set; } = SynthInstanceLimits.Default;

    /// <summary>
    /// Synthesizes an instance of <paramref name="type"/>, or returns <see langword="null"/> if there
    /// is none within the bounds (Lean's <c>synthInstance?</c>). Out-parameters in
    /// <paramref name="type"/> (such as <c>?γ</c> in <c>HAdd Int Int ?γ</c>) are assigned. The search
    /// runs in a nested metavariable depth, so it never assigns the caller's other metavariables.
    /// </summary>
    /// <exception cref="IsDefEqStuckException">The problem is stuck on a metavariable the caller may assign later.</exception>
    public Expr? SynthInstance(Expr type)
    {
        ArgumentNullException.ThrowIfNull(type);
        return WithConfig(
            c => c with { IsDefEqStuckEx = true, Transparency = TransparencyMode.Instances, FoApprox = true, ConstApprox = false, UnivApprox = false },
            () =>
            {
                var (ptype, kind) = PreprocessSynth(this.InstantiateMVars(type));
                var abst = WithNewMCtxDepth(
                    () => SynthMain(kind == SynthPreprocessKind.MVarsNoOutputParams ? ptype : PreprocessOutParam(ptype)),
                    allowLevelAssignments: true);
                return ApplyAbstractResult(ptype, abst);
            });
    }

    /// <summary>Like <see cref="SynthInstance"/>, failing with an error (Lean's <c>synthInstance</c>).</summary>
    /// <exception cref="MetaException">No instance was found.</exception>
    public Expr SynthInstanceOrThrow(Expr type)
    {
        try
        {
            if (SynthInstance(type) is { } r)
            {
                return r;
            }
        }
        catch (IsDefEqStuckException)
        {
        }
        throw new MetaException($"failed to synthesize {this.InstantiateMVars(type)}");
    }

    /// <summary>
    /// Like <see cref="SynthInstance"/>, telling a failure (<c>False</c>) from a problem that is
    /// stuck on metavariables and may succeed later (<c>Undef</c>) (Lean's <c>trySynthInstance</c>).
    /// </summary>
    internal LBool TrySynthInstance(Expr type, out Expr? value)
    {
        try
        {
            value = SynthInstance(type);
            return value is null ? LBool.False : LBool.True;
        }
        catch (IsDefEqStuckException)
        {
            value = null;
            return LBool.Undef;
        }
    }

    // Lean's synthPendingImp: isDefEq's hook for a stuck instance metavariable.
    private bool SynthPendingImp(MVarId mvarId) => WithContext(mvarId, () =>
    {
        var decl = GetMVarDecl(mvarId);
        if (decl.Kind == MetavarKind.SyntheticOpaque || IsClass(decl.Type) is null || _synthPendingDepth > MaxSynthPendingDepth)
        {
            return false;
        }
        _synthPendingDepth++;
        try
        {
            Expr? val;
            try
            {
                val = SynthInstance(decl.Type);
            }
            catch (IsDefEqStuckException)
            {
                val = null;
            }
            if (val is null || IsAssigned(mvarId))
            {
                return false;
            }
            Assign(mvarId, val);
            return true;
        }
        finally
        {
            _synthPendingDepth--;
        }
    });

    private enum SynthPreprocessKind
    {
        NoMVars,
        MVarsNoOutputParams,
        MVarsOutputParams,
    }

    // Lean's preprocess: the type with its conclusion in whnf, and whether out-parameters matter.
    private (Expr Type, SynthPreprocessKind Kind) PreprocessSynth(Expr type) => ForallTelescopeReducing(type, (xs, body) =>
    {
        body = Whnf(body);
        var t = MkForallFVars(xs, body);
        if (!t.HasExprMVar && !t.HasLevelMVar)
        {
            return (t, SynthPreprocessKind.NoMVars);
        }
        if (body is ConstExpr || body.GetAppFn() is not ConstExpr c
            || Attributes.GetOutParams(c.Name) is not { } outs
            || (outs.IsEmpty && GetOutLevelParamPositions(c.Name) is { IsEmpty: true }))
        {
            return (t, SynthPreprocessKind.MVarsNoOutputParams);
        }
        return (t, SynthPreprocessKind.MVarsOutputParams);
    });

    // Lean's preprocessOutParam: out-parameter arguments (and universes only they use) become fresh metavariables.
    private Expr PreprocessOutParam(Expr type) => ForallTelescope(type, (xs, body) =>
    {
        if (body is ConstExpr || body.GetAppFn() is not ConstExpr c || Attributes.GetOutParams(c.Name) is not { } outs)
        {
            return type;
        }
        var outLevels = GetOutLevelParamPositions(c.Name) ?? [];
        if (outs.IsEmpty && outLevels.IsEmpty)
        {
            return type;
        }
        Expr head = c;
        if (!outLevels.IsEmpty)
        {
            head = Expr.Const(c.Name, c.Levels.Select((u, i) => outLevels.Contains(i) ? MkFreshLevelMVar() : u).ToArray());
        }
        var args = body.GetAppArgs();
        if (!outs.IsEmpty)
        {
            var t = InferType(head);
            for (int i = 0; i < args.Length; i++)
            {
                if (Whnf(t) is not ForallExpr f)
                {
                    throw new MetaException("type class resolution failed, insufficient number of arguments");
                }
                if (outs.Contains(i))
                {
                    args[i] = MkFreshExprMVar(f.BinderType);
                }
                t = ExprOps.Instantiate(f.Body, args[i]);
            }
        }
        return MkForallFVars(xs, ExprExtensions.MkAppN(head, args));
    });

    // A candidate instance (Lean's SynthInstance.Instance).
    private sealed record SynthCandidate(Expr Val, ImmutableArray<int> SynthOrder);

    // The search's answer, inside the nested depth: the solution with its own universe
    // metavariables abstracted as parameters, to be reopened outside (Lean's AbstractMVarsResult).
    private sealed record SynthAnswer(Expr Expr, EquatableArray<Name> ParamNames);

    private sealed class SynthStepsExhaustedException : Exception
    {
    }

    // Lean's SynthInstance.main, depth-first.
    private SynthAnswer? SynthMain(Expr type)
    {
        var mvar = MkFreshExprMVar(type);
        SynthAnswer? answer = null;
        int outerSteps = _synthSteps;
        _synthSteps = 0;
        try
        {
            SolveGoals([mvar], 0, () =>
            {
                var val = this.InstantiateMVars(mvar);
                // The root takes only answers without metavariables of the search's own depth.
                if (HasAssignableExprMVar(val))
                {
                    return false;
                }
                answer = AbstractLevelMVars(val);
                return true;
            });
        }
        catch (SynthStepsExhaustedException)
        {
            return null;
        }
        finally
        {
            _synthSteps = outerSteps;
        }
        return answer;
    }

    private bool HasAssignableExprMVar(Expr e) =>
        e.HasExprMVar && ExprOps.Find(e, (x, _) => x is MVarExpr mv && MCtx.GetDecl(mv.Id).Depth == MCtx.Depth) is not null;

    // Solves goals in order, then calls k; on k's failure, backtracks into the goals' other solutions.
    private bool SolveGoals(ImmutableList<Expr> goals, int depth, Func<bool> k)
    {
        // Subgoals solved while unifying an earlier instance are skipped (Lean's consume).
        while (!goals.IsEmpty && IsAssigned(((MVarExpr)goals[0]).Id))
        {
            goals = goals.RemoveAt(0);
        }
        if (goals.IsEmpty)
        {
            return k();
        }
        if (depth >= SynthInstanceLimits.MaxDepth)
        {
            return false;
        }
        var goal = goals[0];
        var rest = goals.RemoveAt(0);
        var goalType = this.InstantiateMVars(InferType(goal));
        var instances = GetSynthInstances(goalType);
        bool typeHasMVars = goalType.HasExprMVar || goalType.HasLevelMVar;
        // Lean tries the last candidate first: the highest priority, the most recent among equals.
        for (int i = instances.Count - 1; i >= 0; i--)
        {
            if (++_synthSteps > SynthInstanceLimits.MaxSteps)
            {
                throw new SynthStepsExhaustedException();
            }
            var saved = SaveState();
            bool answeredWithoutMVars = false;
            if (TryResolve(goal, instances[i]) is { } subgoals)
            {
                bool solved = SolveGoals(subgoals, depth + 1, () =>
                {
                    answeredWithoutMVars |= !HasAssignableExprMVar(this.InstantiateMVars(goal));
                    return SolveGoals(rest, depth, k);
                });
                if (solved)
                {
                    return true;
                }
            }
            Restore(saved);
            // Instances are morally canonical: a goal without metavariables needs one answer (Lean's canonInstances).
            if (!typeHasMVars && answeredWithoutMVars)
            {
                return false;
            }
        }
        return false;
    }

    // Lean's getInstances: the global instances that may unify with the goal, then the local ones.
    private List<SynthCandidate> GetSynthInstances(Expr type)
    {
        var localInstances = LocalInstances;
        return ForallTelescopeReducing(type, (_, body) =>
        {
            var result = new List<SynthCandidate>();
            if (IsClass(body) is not { } className)
            {
                return result; // Lean throws "type class instance expected"; the search just fails.
            }
            var globals = GetGlobalInstancesIndex().GetUnify(this, body).ToList();
            // A stable sort, as Lean's insertion sort.
            foreach (var e in globals.Select((e, i) => (e, i)).OrderBy(p => p.e.Priority).ThenBy(p => p.i).Select(p => p.e))
            {
                result.Add(new SynthCandidate(MkConstWithFreshMVarLevels(e.Name), e.SynthOrder));
            }
            foreach (var linst in localInstances)
            {
                if (linst.ClassName == className)
                {
                    var order = ForallTelescopeReducing(InferType(linst.FVar), (xs, _) =>
                        Enumerable.Range(0, xs.Length).Where(i => GetFVarLocalDecl(xs[i]).BinderInfo == BinderInfo.InstImplicit).ToImmutableArray());
                    result.Add(new SynthCandidate(linst.FVar, order));
                }
            }
            return result;
        });
    }

    // Lean's tryResolve: unify the goal with the instance's conclusion; its instance arguments are the new subgoals.
    private ImmutableList<Expr>? TryResolve(Expr mvar, SynthCandidate inst)
    {
        var mvarType = InferType(mvar);
        var lctx = LCtx;
        var localInsts = LocalInstances;
        return ForallTelescopeReducing(mvarType, (xs, mvarTypeBody) =>
        {
            var (subgoals, instVal, instTypeBody) = GetSubgoals(lctx, localInsts, xs, inst);
            if (!IsDefEq(mvarTypeBody, instTypeBody))
            {
                return null;
            }
            var val = MkLambdaFVars(xs, instVal, etaReduce: true);
            if (!this.InstantiateMVars(mvarTypeBody).HasExprMVar)
            {
                Assign(((MVarExpr)mvar).Id, val);
            }
            else if (!IsDefEq(mvar, val))
            {
                return null;
            }
            return subgoals;
        });
    }

    // Lean's getSubgoals: a metavariable `?mᵢ : ∀ xs, Aᵢ` for each parameter of the instance.
    private (ImmutableList<Expr> Subgoals, Expr InstVal, Expr InstTypeBody) GetSubgoals(
        LocalContext lctx, ImmutableArray<LocalInstance> localInsts, Expr[] xs, SynthCandidate inst)
    {
        var instVal = inst.Val;
        var instType = InferType(instVal);
        var mvars = new List<Expr>();
        var subst = new List<Expr>();
        while (true)
        {
            if (instType is ForallExpr f)
            {
                var d = f.BinderType.InstantiateRev(subst);
                var mv = MkFreshExprMVarAt(lctx, localInsts, MkForallFVars(xs, d));
                var arg = ExprExtensions.MkAppN(mv, xs);
                subst.Add(arg);
                instVal = Expr.App(instVal, arg);
                instType = f.Body;
                mvars.Add(mv);
                continue;
            }
            instType = Whnf(instType.InstantiateRev(subst));
            instVal = instVal.InstantiateRev(subst);
            subst.Clear();
            if (instType is not ForallExpr)
            {
                break;
            }
        }
        return ([.. inst.SynthOrder.Where(i => i < mvars.Count).Select(i => mvars[i])], instVal, instType);
    }

    // Lean's abstractMVars, for universes: the search's own universe metavariables become parameters.
    private SynthAnswer AbstractLevelMVars(Expr e)
    {
        if (!e.HasLevelMVar)
        {
            return new SynthAnswer(e, EquatableArray<Name>.Empty);
        }
        var map = new Dictionary<LMVarId, Level>();
        var names = new List<Name>();
        var r = ExprOps.Replace(e, (x, _) => x switch
        {
            _ when !x.HasLevelMVar => x,
            ConstExpr c => Expr.Const(c.Name, c.Levels.Select(Visit).ToArray()),
            SortExpr s => Expr.Sort(Visit(s.Level)),
            _ => null,
        });
        return new SynthAnswer(r, [.. names]);

        Level Visit(Level l)
        {
            if (!l.HasMVar)
            {
                return l;
            }
            switch (l.Kind)
            {
                case LevelKind.Succ:
                    return Level.Succ(Visit(l.Lhs!));
                case LevelKind.Max:
                    return Level.Max(Visit(l.Lhs!), Visit(l.Rhs!));
                case LevelKind.IMax:
                    return Level.IMax(Visit(l.Lhs!), Visit(l.Rhs!));
                case LevelKind.MVar:
                {
                    var id = l.MVarId!.Value;
                    if (MCtx.GetLevelDecl(id).Depth != MCtx.Depth)
                    {
                        return l;
                    }
                    if (!map.TryGetValue(id, out var p))
                    {
                        var name = Name.From("_tc_u", names.Count.ToString(System.Globalization.CultureInfo.InvariantCulture));
                        names.Add(name);
                        map[id] = p = Level.Param(name);
                    }
                    return p;
                }
                default:
                    return l;
            }
        }
    }

    // Lean's applyAbstractResult?: reopen the answer, assign the out-parameters, check if needed.
    private Expr? ApplyAbstractResult(Expr type, SynthAnswer? answer)
    {
        if (answer is null)
        {
            return null;
        }
        var result = answer.ParamNames.Count == 0
            ? answer.Expr
            : ExprOps.InstantiateLevelParams(answer.Expr, answer.ParamNames, MkFreshLevelMVars(answer.ParamNames.Count));
        if (!WithDefault(() => WithAssignableSyntheticOpaque(() => IsDefEq(type, InferType(result)))))
        {
            return null;
        }
        result = this.InstantiateMVars(result);
        if (CheckMayHaveSideEffects(result))
        {
            Check(result);
        }
        return result;
    }

    // Lean's checkMayHaveSideEffects: whether a metavariable is reachable from the result or its free variables.
    private bool CheckMayHaveSideEffects(Expr result)
    {
        if (result.HasExprMVar || result.HasLevelMVar)
        {
            return true;
        }
        var todo = new Stack<Expr>([result]);
        var seen = new HashSet<FVarId>();
        while (todo.Count > 0)
        {
            var e = todo.Pop();
            if (!e.HasFVar)
            {
                continue;
            }
            foreach (var fv in CollectFVarIds(e))
            {
                if (!seen.Add(fv) || FindLocalDecl(fv) is not { } decl)
                {
                    continue;
                }
                var t = this.InstantiateMVars(decl.Type);
                if (t.HasExprMVar || t.HasLevelMVar)
                {
                    return true;
                }
                todo.Push(t);
                if (decl is LDecl { Value: var v0 })
                {
                    var v = this.InstantiateMVars(v0);
                    if (v.HasExprMVar || v.HasLevelMVar)
                    {
                        return true;
                    }
                    todo.Push(v);
                }
            }
        }
        return false;

        static List<FVarId> CollectFVarIds(Expr e)
        {
            var ids = new List<FVarId>();
            ExprOps.ForEach(e, (x, _) =>
            {
                if (x is FVarExpr f)
                {
                    ids.Add(f.Id);
                }
                return x.HasFVar;
            });
            return ids;
        }
    }
}
