using Warrant.Cic;

namespace Warrant.Meta;

/// <summary>
/// Unification is stuck on a read-only metavariable while <see cref="MetaConfig.IsDefEqStuckEx"/>
/// is on (Lean's <c>isDefEqStuck</c> internal exception); instance resolution retries later.
/// </summary>
public sealed class IsDefEqStuckException : MetaException
{
    /// <summary>Creates the exception.</summary>
    public IsDefEqStuckException()
        : base("isDefEq is stuck")
    {
    }

    /// <summary>Creates the exception with a message.</summary>
    public IsDefEqStuckException(string message)
        : base(message)
    {
    }

    /// <summary>Creates the exception with a message and inner exception.</summary>
    public IsDefEqStuckException(string message, Exception innerException)
        : base(message, innerException)
    {
    }
}

// Definitional equality with metavariable assignment (a port of Lean 4.35.0's
// Lean/Meta/ExprDefEq.lean, with `isDefEq`, `approxDefEq` and friends from Lean/Meta/Basic.lean).
//
// Lean's `backward.*` options are fixed at their 4.35.0 defaults: respectTransparency,
// respectTransparency.types, implicitBump, lazyProjDelta, lazyWhnfCore and
// whnf.reducibleClassField are on, throwOnStuckAfterApp is off. Not ported: unification hints
// (`tryUnificationHints` is false), context approximation, and the instance-typed metavariables of
// `respectTransparency.instanceSearchTypes` (no metavariable is instance-typed until instance
// resolution exists). `synthPending` calls instance resolution (Attributes/SynthInstance.cs).
public sealed partial class MetaM
{
    private readonly Dictionary<DefEqKey, bool> _defEqTransCache = [];
    private readonly Dictionary<DefEqKey, bool> _defEqPermCache = [];

    // Lean's DefEqCacheKey: the configuration and an unordered pair.
    private readonly struct DefEqKey : IEquatable<DefEqKey>
    {
        private readonly ulong _config;
        private readonly Expr _a;
        private readonly Expr _b;

        public DefEqKey(ulong config, Expr lhs, Expr rhs)
        {
            _config = config;
            (_a, _b) = lhs.GetHashCode() <= rhs.GetHashCode() ? (lhs, rhs) : (rhs, lhs);
        }

        public bool Equals(DefEqKey other) => _config == other._config && _a.Equals(other._a) && _b.Equals(other._b);

        public override bool Equals(object? obj) => obj is DefEqKey k && Equals(k);

        public override int GetHashCode() => HashCode.Combine(_config, _a.GetHashCode(), _b.GetHashCode());
    }

    private static LBool ToLBool(bool b) => b ? LBool.True : LBool.False;

    /// <summary>
    /// Synthesizes a pending instance metavariable by instance resolution (Lean's <c>synthPending</c>):
    /// a natural or synthetic metavariable whose type is a class is assigned the instance found, at
    /// most two nested calls deep. Returns whether it was assigned.
    /// </summary>
    public bool SynthPending(MVarId mvarId) => SynthPendingImp(mvarId);

    // ---------------------------------------------------------------- small predicates

    // fun xs => ?m ys with ?m unassigned and assignable.
    private bool IsAbstractedUnassignedMVar(Expr e)
    {
        while (true)
        {
            switch (e)
            {
                case LamExpr l:
                    e = l.Body;
                    continue;
                case AppExpr a:
                    e = a.Fn;
                    continue;
                case MVarExpr mv:
                    return !IsReadOnlyOrSyntheticOpaque(mv.Id) && !IsAssigned(mv.Id);
                default:
                    return false;
            }
        }
    }

    // fun xs => ?m xs with ?m unassigned and assignable.
    private bool IsEtaUnassignedMVar(Expr e) =>
        e.EtaExpanded() is MVarExpr mv && !IsReadOnlyOrSyntheticOpaque(mv.Id) && !IsAssigned(mv.Id);

    private bool TrySynthPending(Expr e) => GetStuckMVar(e) is { } m && SynthPending(m);

    private bool IsAssignedMVar(Expr e) => e is MVarExpr mv && IsAssigned(mv.Id);

    private bool IsAssignable(Expr e) => e is MVarExpr mv && !IsReadOnlyOrSyntheticOpaque(mv.Id);

    private static bool EtaEq(Expr t, Expr s) => t.EtaExpanded() is { } t1 && t1.Equals(s);

    // ---------------------------------------------------------------- eta, eta-struct, Nat, strings

    // b = mk a.1 … a.n with a not a constructor application.
    private bool IsDefEqEtaStruct(Expr a, Expr b)
    {
        if (b.GetAppFn() is not ConstExpr bc || Env.Find(bc.Name) is not ConstructorInfo ctorVal)
        {
            return false;
        }
        if (!UseEtaStruct(ctorVal.Inductive))
        {
            return false;
        }
        if (a.GetAppFn() is ConstExpr ac && Env.Find(ac.Name) is ConstructorInfo)
        {
            return false;
        }
        if (ctorVal.NumParams + ctorVal.NumFields != b.GetAppNumArgs() || !IsNonRecStructure(ctorVal.Inductive))
        {
            return false;
        }
        if (!IsDefEq(InferType(a), InferType(b)))
        {
            return false;
        }
        return CheckpointDefEq(() =>
        {
            var args = b.GetAppArgs();
            var @params = args[..ctorVal.NumParams];
            for (int i = ctorVal.NumParams; i < args.Length; i++)
            {
                var proj = MkProjFn(ctorVal, bc.Levels, @params, i - ctorVal.NumParams, a);
                // Skip a likely proof-irrelevant subproblem: the types already agree.
                if (IsProof(proj) && !IsAbstractedUnassignedMVar(args[i]))
                {
                    continue;
                }
                if (!IsDefEq(proj, args[i]))
                {
                    return false;
                }
            }
            return true;
        });
    }

    // (fun x => t) =?= b by eta-expanding b (no backtracking, Lean PR #2002).
    private LBool IsDefEqEta(Expr a, Expr b)
    {
        if (a is LamExpr && b is not LamExpr)
        {
            if (WhnfD(InferType(b)) is ForallExpr f)
            {
                var b1 = Expr.Lam(f.BinderName, f.BinderType, Expr.App(b, Expr.BVar(0)), f.BinderInfo);
                return ToLBool(IsExprDefEqAux(a, b1));
            }
        }
        return LBool.Undef;
    }

    private LBool IsDefEqNat(Expr s, Expr t)
    {
        if (s.HasFVar || s.HasExprMVar || s.HasLevelMVar || t.HasFVar || t.HasExprMVar || t.HasLevelMVar)
        {
            return LBool.Undef;
        }
        var s1 = ReduceNat(s);
        var t1 = ReduceNat(t);
        if (s1 is null && t1 is null)
        {
            return LBool.Undef;
        }
        return ToLBool(IsExprDefEqAux(s1 ?? s, t1 ?? t));
    }

    private LBool IsDefEqStringLit(Expr s, Expr t)
    {
        if (s is StrLitExpr && t.IsAppOf(MetaNames.StringOfList))
        {
            return ToLBool(IsExprDefEqAux(ToCtorIfLit(s), t));
        }
        if (s.IsAppOf(MetaNames.StringOfList) && t is StrLitExpr)
        {
            return ToLBool(IsExprDefEqAux(s, ToCtorIfLit(t)));
        }
        return LBool.Undef;
    }

    // ---------------------------------------------------------------- arguments

    // Lean's isDefEqArgsFirstPass: explicit arguments and easy ?m =?= t cases now; other implicit
    // arguments, and higher-order output parameters, postponed.
    private bool IsDefEqArgsFirstPass(FunInfo finfo, Expr[] args1, Expr[] args2, List<int> postponedImplicit, List<int> postponedHO)
    {
        for (int i = 0; i < finfo.ParamInfo.Length; i++)
        {
            var info = finfo.ParamInfo[i];
            var a1 = args1[i];
            var a2 = args2[i];
            if (info.DependsOnHigherOrderOutParam || info.HigherOrderOutParam)
            {
                postponedHO.Add(i);
            }
            else if (info.IsExplicit)
            {
                if (info.IsProp && !IsAbstractedUnassignedMVar(a1) && !IsAbstractedUnassignedMVar(a2))
                {
                    continue; // proof irrelevance: the types already agree
                }
                if (!IsExprDefEqAux(a1, a2))
                {
                    return false;
                }
            }
            else if (IsEtaUnassignedMVar(a1) || IsEtaUnassignedMVar(a2))
            {
                // An easy case at an implicit position gets the second pass's transparency bump.
                if (!WithImplicitConfig(() => IsExprDefEqAux(a1, a2)))
                {
                    return false;
                }
            }
            else
            {
                if (info.IsProp && !IsAbstractedUnassignedMVar(a1) && !IsAbstractedUnassignedMVar(a2))
                {
                    continue;
                }
                postponedImplicit.Add(i);
            }
        }
        return true;
    }

    private bool IsDefEqArgs(Expr f, Expr[] args1, Expr[] args2)
    {
        if (args1.Length != args2.Length)
        {
            return false;
        }
        var finfo = GetFunInfoNArgs(f, args1.Length);
        var postponedImplicit = new List<int>();
        var postponedHO = new List<int>();
        if (!IsDefEqArgsFirstPass(finfo, args1, args2, postponedImplicit, postponedHO))
        {
            return false;
        }
        for (int i = finfo.ParamInfo.Length; i < args1.Length; i++)
        {
            if (!IsExprDefEqAux(args1[i], args2[i]))
            {
                return false;
            }
        }
        foreach (int i in postponedImplicit)
        {
            // Implicit arguments at `implicit`: reducible, instance- and implicit-reducible constants unfold.
            var a1 = args1[i];
            var a2 = args2[i];
            if (finfo.ParamInfo[i].IsInstImplicit)
            {
                TrySynthPending(a1);
                TrySynthPending(a2);
            }
            if (!WithImplicitConfig(() => IsExprDefEqAux(a1, a2)))
            {
                return false;
            }
        }
        foreach (int i in postponedHO)
        {
            var a1 = args1[i];
            var a2 = args2[i];
            if (!WithImplicitConfig(() => IsExprDefEqAux(a1, a2)))
            {
                return false;
            }
        }
        return true;
    }

    // ---------------------------------------------------------------- binders

    private bool IsDefEqBindingDomain(Expr[] fvars, Expr[] ds2, Func<bool> k)
    {
        return Loop(0);

        bool Loop(int i)
        {
            if (i >= fvars.Length)
            {
                return k();
            }
            var fvar = fvars[i];
            var fvarType = GetFVarLocalDecl(fvar).Type;
            if (!IsExprDefEqAux(fvarType, ds2[i]))
            {
                return false;
            }
            if (IsClass(fvarType) is { } className)
            {
                return WithReader(c => c with { LocalInstances = c.LocalInstances.Add(new LocalInstance(className, fvar)) }, () => Loop(i + 1));
            }
            return Loop(i + 1);
        }
    }

    private bool IsDefEqBinding(Expr a, Expr b)
    {
        var lctx = LCtx;
        var fvars = new List<Expr>();
        var ds2 = new List<Expr>();
        var e1 = a;
        var e2 = b;
        while ((e1 is ForallExpr && e2 is ForallExpr) || (e1 is LamExpr && e2 is LamExpr))
        {
            var b1 = (BindingExpr)e1;
            var b2 = (BindingExpr)e2;
            var d1 = b1.BinderType.InstantiateRev(fvars);
            var d2 = b2.BinderType.InstantiateRev(fvars);
            var fvarId = MkFreshFVarId();
            lctx = lctx.MkLocalDecl(fvarId, b1.BinderName, d1);
            fvars.Add(Expr.FVar(fvarId));
            ds2.Add(d2);
            e1 = b1.Body;
            e2 = b2.Body;
        }
        Expr[] xs = [.. fvars];
        var body1 = e1;
        var body2 = e2;
        return WithReader(c => c with { LCtx = lctx }, () =>
            IsDefEqBindingDomain(xs, [.. ds2], () => IsExprDefEqAux(body1.InstantiateRev(xs), body2.InstantiateRev(xs))));
    }

    // ---------------------------------------------------------------- assignment

    // The types of ?m and v must agree before ?m := v (at `implicit`, Lean's respectTransparency.types).
    private bool CheckTypesAndAssign(Expr mvar, Expr v)
    {
        if (mvar is not MVarExpr mv)
        {
            return false;
        }
        var mvarType = InferType(mvar);
        var vType = InferType(v);
        return WithImplicitConfig(() =>
        {
            if (!IsExprDefEqAux(mvarType, vType))
            {
                return false;
            }
            Assign(mv.Id, v);
            return true;
        });
    }

    // Lean's mkLambdaFVarsWithLetDeps: `fun ys => v` where ys adds the let-declarations between
    // xs[0] and xs.back that some x depends on, so the lambda's type matches ?m's.
    private Expr MkLambdaFVarsWithLetDeps(Expr[] xs, Expr v)
    {
        if (!HasLetDeclsInBetween())
        {
            return MkLambdaFVars(xs, v, etaReduce: true);
        }
        var lctx = LCtx;
        int start = lctx.GetFVar(xs[0]).Index;
        int stop = lctx.GetFVar(xs[^1]).Index;
        var s = new HashSet<FVarId>(xs.Select(x => ((FVarExpr)x).Id));
        for (int i = stop; i > start; i--)
        {
            if (lctx.GetAt(i) is { } decl && s.Contains(decl.FVarId))
            {
                CollectLetDeclsFrom(decl.Type);
                if (decl.GetValue() is { } val)
                {
                    CollectLetDeclsFrom(val);
                }
            }
        }
        var ys = new List<Expr>();
        for (int i = start; i <= stop; i++)
        {
            if (lctx.GetAt(i) is { } decl && s.Contains(decl.FVarId))
            {
                ys.Add(decl.ToExpr());
            }
        }
        return MkLambdaFVars(ys, v, etaReduce: true);

        bool HasLetDeclsInBetween()
        {
            if (xs.Length <= 1)
            {
                return false;
            }
            var l = LCtx;
            int a = l.GetFVar(xs[0]).Index;
            int b = l.GetFVar(xs[^1]).Index;
            for (int i = a + 1; i < b; i++)
            {
                if (l.GetAt(i) is { } d && d.IsLet())
                {
                    return true;
                }
            }
            return false;
        }

        void CollectLetDeclsFrom(Expr e)
        {
            Kernel.ExprOps.ForEach(this.InstantiateMVars(e), (x, _) =>
            {
                if (x is FVarExpr fv && LCtx.Find(fv.Id) is { } d && d.IsLet() && d.Index > start)
                {
                    s.Add(d.FVarId);
                }
                return x.HasFVar;
            });
        }
    }

    private Expr MkAuxMVar(LocalContext lctx, System.Collections.Immutable.ImmutableArray<LocalInstance> localInsts, Expr type, int numScopeArgs = 0) =>
        MkFreshExprMVarAt(lctx, localInsts, type, MetavarKind.Natural, Name.Anonymous, numScopeArgs);

    private bool ProcessAssignmentFOApproxAux(Expr mvar, Expr[] args, Expr v)
    {
        v = v.ConsumeMData();
        if (v is not AppExpr app || args.Length == 0)
        {
            return false;
        }
        return IsExprDefEqAux(args[^1], app.Arg) && IsExprDefEqAux(ExprExtensions.MkAppRange(mvar, 0, args.Length - 1, args), app.Fn);
    }

    // First-order approximation, unfolding v when it fails (to solve `?m Unit =?= ITactic`).
    private bool ProcessAssignmentFOApprox(Expr mvar, Expr[] args, Expr v)
    {
        while (true)
        {
            if (!Config.FoApprox)
            {
                return false;
            }
            v = v.HeadBeta();
            var v1 = v;
            if (CheckpointDefEq(() => ProcessAssignmentFOApproxAux(mvar, args, v1)))
            {
                return true;
            }
            if (UnfoldDefinition(v) is not { } v2)
            {
                return false;
            }
            v = v2;
        }
    }

    private Expr SimpAssignmentArg(Expr arg)
    {
        if (arg.GetAppFn().HasExprMVar)
        {
            arg = this.InstantiateMVars(arg);
        }
        while (true)
        {
            switch (arg)
            {
                case MDataExpr m:
                    arg = m.Expr;
                    continue;
                case FVarExpr fv when GetLocalDecl(fv.Id).GetValue() is { } value:
                    arg = value;
                    continue;
                default:
                    return arg;
            }
        }
    }

    // ?m := fun a₁ … a_numArgs => v.
    private bool AssignConst(Expr mvar, int numArgs, Expr v)
    {
        var mvarDecl = GetMVarDecl(((MVarExpr)mvar).Id);
        return ForallBoundedTelescope(mvarDecl.Type, numArgs, (xs, _) =>
        {
            if (xs.Length != numArgs)
            {
                return false;
            }
            var v1 = MkLambdaFVarsWithLetDeps(xs, v);
            return CheckAssignment(((MVarExpr)mvar).Id, [], v1) is { } v2 && CheckTypesAndAssign(mvar, v2);
        });
    }

    // Constant approximation (Lean's processConstApprox): find the longest prefix of the pattern
    // variables for which the assignment is valid.
    private bool ProcessConstApprox(Expr mvar, Expr[] args, int patternVarPrefix, Expr v)
    {
        var mvarId = ((MVarExpr)mvar).Id;
        var mvarDecl = GetMVarDecl(mvarId);
        int numArgs = args.Length;
        if (mvarDecl.NumScopeArgs != numArgs && !Config.ConstApprox)
        {
            return false;
        }
        if (patternVarPrefix == 0)
        {
            return DefaultCase();
        }
        var argsPrefix = args[..patternVarPrefix];
        var type = InstantiateForall(mvarDecl.Type, argsPrefix);
        int suffixSize = numArgs - argsPrefix.Length;
        return ForallBoundedTelescope(type, suffixSize, (xs, _) =>
        {
            if (xs.Length != suffixSize)
            {
                return DefaultCase();
            }
            return Go(argsPrefix, MkLambdaFVarsWithLetDeps(xs, v));
        });

        bool DefaultCase() => AssignConst(mvar, numArgs, v);

        bool Go(Expr[] argsPrefix, Expr v)
        {
            while (true)
            {
                if (CheckAssignment(mvarId, argsPrefix, v) is { } vNew)
                {
                    var vNew1 = MkLambdaFVarsWithLetDeps(argsPrefix, vNew);
                    bool ok = argsPrefix.Any(mvarDecl.LCtx.ContainsFVar)
                        // Abstraction may have produced an ill-typed term (A2 in ExprDefEq.lean).
                        ? IsTypeCorrect(vNew1) && CheckTypesAndAssign(mvar, vNew1)
                        : CheckTypesAndAssign(mvar, vNew1);
                    if (ok)
                    {
                        return true;
                    }
                }
                if (argsPrefix.Length == 0)
                {
                    return DefaultCase();
                }
                v = MkLambdaFVarsWithLetDeps([argsPrefix[^1]], v);
                argsPrefix = argsPrefix[..^1];
            }
        }
    }

    /// <summary>
    /// Solves <c>?m a₁ … aₙ =?= v</c> for an unassigned <c>?m</c> by assigning it: as a Miller
    /// pattern when the <c>aᵢ</c> are distinct free variables outside <c>?m</c>'s context, otherwise
    /// by first-order or constant approximation (Lean's <c>processAssignment</c>).
    /// </summary>
    private bool ProcessAssignment(Expr mvarApp, Expr v)
    {
        var mvar = mvarApp.GetAppFn();
        var mvarId = ((MVarExpr)mvar).Id;
        var mvarDecl = GetMVarDecl(mvarId);
        var args = mvarApp.GetAppArgs();
        for (int i = 0; i < args.Length; i++)
        {
            var arg = SimpAssignmentArg(args[i]);
            args[i] = arg;
            if (arg is not FVarExpr fv)
            {
                return UseFOApprox(i);
            }
            bool repeated = false;
            for (int j = 0; j < i; j++)
            {
                if (args[j].Equals(arg))
                {
                    repeated = true;
                    break;
                }
            }
            if (repeated || (mvarDecl.LCtx.Contains(fv.Id) && !Config.QuasiPatternApprox))
            {
                return UseFOApprox(i);
            }
        }
        v = this.InstantiateMVars(v); // A4
        if (v.GetAppFn().Equals(mvar))
        {
            return UseFOApprox(args.Length); // A6
        }
        if (CheckAssignment(mvarId, args, v) is not { } v1)
        {
            return UseFOApprox(args.Length);
        }
        var v2 = MkLambdaFVarsWithLetDeps(args, v1);
        if (args.Any(mvarDecl.LCtx.ContainsFVar))
        {
            // Abstraction may have produced an ill-typed term (A2 in ExprDefEq.lean).
            return IsTypeCorrect(v2) ? CheckTypesAndAssign(mvar, v2) : UseFOApprox(args.Length);
        }
        return CheckTypesAndAssign(mvar, v2);

        bool UseFOApprox(int i) => ProcessAssignmentFOApprox(mvar, args, v) || ProcessConstApprox(mvar, args, i, v);
    }

    // processAssignment, retried on whnf v (for `?m =?= { α := ?m, … }.α`).
    private bool ProcessAssignment1(Expr mvarApp, Expr v)
    {
        if (ProcessAssignment(mvarApp, v))
        {
            return true;
        }
        var vNew = Whnf(v);
        if (vNew.Equals(v))
        {
            return false;
        }
        return mvarApp.Equals(vNew) || ProcessAssignment(mvarApp, vNew);
    }

    // ---------------------------------------------------------------- lazy delta

    private ConstantInfo? IsDeltaCandidate(Expr t) => t.GetAppFn() is ConstExpr c ? GetUnfoldableConst(c.Name) : null;

    private LBool IsDefEqLeft(Expr t, Expr s) => ToLBool(IsExprDefEqAux(t, s));

    private bool IsNonTrivialRegular(DefinitionInfo info)
    {
        switch (info.Hints.Kind)
        {
            case ReducibilityHintsKind.Regular:
                if (info.Hints.Height > 2)
                {
                    return true;
                }
                var val = info.Value;
                while (true)
                {
                    if (val is MDataExpr m)
                    {
                        val = m.Expr;
                    }
                    else if (val is LamExpr l)
                    {
                        val = l.Body;
                    }
                    else
                    {
                        break;
                    }
                }
                return !IsSimple(val, allowApp: true);
            case ReducibilityHintsKind.Abbrev:
                // A class projection is nontrivial at `reducible` (Lean PR #12650).
                return GetProjectionFnInfo(info.Name) is { FromClass: true } && GetTransparency() == TransparencyMode.Reducible;
            default:
                return false;
        }

        static bool IsSimple(Expr e, bool allowApp) => e switch
        {
            BVarExpr or SortExpr or NatLitExpr or StrLitExpr or FVarExpr or MVarExpr => true,
            AppExpr a => IsSimple(a.Arg, false) && IsSimple(a.Fn, allowApp),
            ProjExpr p => IsSimple(p.Struct, false),
            MDataExpr m => IsSimple(m.Expr, allowApp),
            _ => false,
        };
    }

    // f a₁ … aₙ =?= f b₁ … bₙ by aᵢ =?= bᵢ (arguments before universe levels).
    private bool TryHeuristic(Expr t, Expr s)
    {
        var tFn = (ConstExpr)t.GetAppFn();
        var sFn = (ConstExpr)s.GetAppFn();
        if (GetConstInfo(tFn.Name) is not DefinitionInfo info)
        {
            return false;
        }
        if (!IsNonTrivialRegular(info) && GetMatcherInfo(tFn.Name) is null && !t.HasExprMVar && !s.HasExprMVar)
        {
            return false;
        }
        return CheckpointDefEq(() => IsDefEqArgs(tFn, t.GetAppArgs(), s.GetAppArgs()) && IsListLevelDefEqAux(tFn.Levels, sFn.Levels));
    }

    private LBool UnfoldBothDefEq(Expr t, Expr s)
    {
        if (t is ConstExpr tc && s is ConstExpr sc)
        {
            if (IsListLevelDefEqAux(tc.Levels, sc.Levels))
            {
                return LBool.True;
            }
            if (UnfoldDefinition(t) is { } t1 && UnfoldDefinition(s) is { } s1)
            {
                return IsDefEqLeft(t1, s1);
            }
            return LBool.Undef;
        }
        if (t is AppExpr && s is AppExpr)
        {
            if (TryHeuristic(t, s))
            {
                return LBool.True;
            }
            if (UnfoldDefinition(t) is { } t1)
            {
                return UnfoldDefinition(s) is { } s1 ? IsDefEqLeft(t1, s1) : IsDefEqLeft(t1, s);
            }
            return UnfoldDefinition(s) is { } s2 ? IsDefEqLeft(t, s2) : LBool.Undef;
        }
        return LBool.False;
    }

    private static bool SameHeadSymbol(Expr t, Expr s) =>
        t.GetAppFn() is ConstExpr c1 && s.GetAppFn() is ConstExpr c2 && c1.Name == c2.Name;

    private LBool UnfoldComparingHeadsDefEq(Expr t, Expr s)
    {
        if (UnfoldDefinition(t) is not { } tNew)
        {
            return UnfoldDefinition(s) is { } s1 ? IsDefEqLeft(t, s1) : LBool.Undef;
        }
        if (SameHeadSymbol(tNew, s))
        {
            return IsDefEqLeft(tNew, s);
        }
        if (UnfoldDefinition(s) is not { } sNew)
        {
            return IsDefEqLeft(tNew, s);
        }
        return SameHeadSymbol(t, sNew) ? IsDefEqLeft(t, sNew) : IsDefEqLeft(tNew, sNew);
    }

    // Without metavariables, the kernel's strategy: unfold the side with the greater height first.
    private LBool UnfoldDefEq(ConstantInfo tInfo, ConstantInfo sInfo, Expr t, Expr s)
    {
        if (!t.HasExprMVar && !s.HasExprMVar)
        {
            if (tInfo.Hints().HintsLt(sInfo.Hints()))
            {
                return UnfoldDefinition(t) is { } t1 ? IsDefEqLeft(t1, s) : UnfoldComparingHeadsDefEq(t, s);
            }
            if (sInfo.Hints().HintsLt(tInfo.Hints()))
            {
                return UnfoldDefinition(s) is { } s1 ? IsDefEqLeft(t, s1) : UnfoldComparingHeadsDefEq(t, s);
            }
        }
        return UnfoldComparingHeadsDefEq(t, s);
    }

    // At default and all, unfold a reducible side before a non-reducible one.
    private LBool UnfoldReducibleDefEq(ConstantInfo tInfo, ConstantInfo sInfo, Expr t, Expr s)
    {
        if (ShouldReduceReducibleOnly())
        {
            return UnfoldDefEq(tInfo, sInfo, t, s);
        }
        bool tReducible = IsReducible(tInfo.Name);
        bool sReducible = IsReducible(sInfo.Name);
        if (tReducible && !sReducible)
        {
            return UnfoldDefinition(t) is { } t1 ? IsDefEqLeft(t1, s) : UnfoldDefEq(tInfo, sInfo, t, s);
        }
        if (!tReducible && sReducible)
        {
            return UnfoldDefinition(s) is { } s1 ? IsDefEqLeft(t, s1) : UnfoldDefEq(tInfo, sInfo, t, s);
        }
        return UnfoldDefEq(tInfo, sInfo, t, s);
    }

    // Unfold the side that is not a projection function first; for class projections, unpack them
    // and check whether the other side's function appears (Lean issue #1419).
    private LBool UnfoldNonProjFnDefEq(ConstantInfo tInfo, ConstantInfo sInfo, Expr t, Expr s)
    {
        var tProjInfo = GetProjectionFnInfo(tInfo.Name);
        var sProjInfo = GetProjectionFnInfo(sInfo.Name);
        if (PackedInstanceOf(tProjInfo, t, sInfo.Name) is { } tNew)
        {
            return IsDefEqLeft(tNew, s);
        }
        if (PackedInstanceOf(sProjInfo, s, tInfo.Name) is { } sNew)
        {
            return IsDefEqLeft(t, sNew);
        }
        if (tProjInfo is not null && sProjInfo is null)
        {
            return UnfoldDefinition(s) is { } s1 ? IsDefEqLeft(t, s1) : UnfoldDefEq(tInfo, sInfo, t, s);
        }
        if (tProjInfo is null && sProjInfo is not null)
        {
            return UnfoldDefinition(t) is { } t1 ? IsDefEqLeft(t1, s) : UnfoldDefEq(tInfo, sInfo, t, s);
        }
        return UnfoldReducibleDefEq(tInfo, sInfo, t, s);

        Expr? PackedInstanceOf(ProjectionFunctionInfo? projInfo, Expr e, Name declName)
        {
            while (true)
            {
                if (projInfo is not { FromClass: true } || UnfoldDefinition(e) is not { } e1)
                {
                    return null;
                }
                e = WhnfCore(e1);
                if (e.IsAppOf(declName))
                {
                    return e;
                }
                if (e.GetAppFn() is not ConstExpr c)
                {
                    return null;
                }
                projInfo = GetProjectionFnInfo(c.Name);
            }
        }
    }

    // Lazy delta reduction (Lean's isDefEqDelta, steps 1-11 of its comment).
    private LBool IsDefEqDelta(Expr t, Expr s)
    {
        var tInfo = IsDeltaCandidate(t);
        var sInfo = IsDeltaCandidate(s);
        if (tInfo is null && sInfo is null)
        {
            return LBool.Undef;
        }
        if (sInfo is null)
        {
            return UnfoldDefinition(t) is { } t1 ? IsDefEqLeft(t1, s) : LBool.Undef;
        }
        if (tInfo is null)
        {
            return UnfoldDefinition(s) is { } s1 ? IsDefEqLeft(t, s1) : LBool.Undef;
        }
        return tInfo.Name == sInfo.Name ? UnfoldBothDefEq(t, s) : UnfoldNonProjFnDefEq(tInfo, sInfo, t, s);
    }

    // ---------------------------------------------------------------- delayed assignments, proof irrelevance

    private Expr? ExpandDelayedAssigned(Expr t)
    {
        if (t.GetAppFn() is not MVarExpr tFn || MCtx.GetDelayedMVarAssignment(tFn.Id) is not { } d)
        {
            return null;
        }
        var tNew = this.InstantiateMVars(t);
        if (!tNew.Equals(t))
        {
            return tNew;
        }
        // With assignSyntheticOpaque, follow ?m [xs] := ?pending by dropping xs.size arguments.
        if (!Config.AssignSyntheticOpaque)
        {
            return null;
        }
        var tArgs = t.GetAppArgs();
        if (tArgs.Length < d.FVars.Length)
        {
            return null;
        }
        return ExprExtensions.MkAppRange(Expr.MVar(d.MVarIdPending), d.FVars.Length, tArgs.Length, tArgs);
    }

    private LBool IsDefEqProofIrrel(Expr t, Expr s)
    {
        if (!Config.ProofIrrelevance)
        {
            return LBool.Undef;
        }
        switch (IsProofQuick(t))
        {
            case LBool.False:
                return LBool.Undef;
            case LBool.True:
            {
                var tType = InferType(t);
                var sType = InferType(s);
                return ToLBool(IsExprDefEqAux(tType, sType));
            }
            default:
            {
                var tType = InferType(t);
                if (!IsProp(tType))
                {
                    return LBool.Undef;
                }
                var sType = InferType(s);
                return ToLBool(IsExprDefEqAux(tType, sType));
            }
        }
    }

    // ?m args₁ =?= ?m args₂.
    private bool IsDefEqMVarSelf(Expr mvar, Expr[] args1, Expr[] args2)
    {
        if (args1.Length != args2.Length)
        {
            return false;
        }
        if (IsDefEqArgs(mvar, args1, args2))
        {
            return true;
        }
        if (!IsAssignable(mvar))
        {
            return false;
        }
        var mvarDecl = GetMVarDecl(((MVarExpr)mvar).Id);
        if (mvarDecl.NumScopeArgs == args1.Length || Config.ConstApprox)
        {
            var type = InferType(ExprExtensions.MkAppN(mvar, args1));
            var auxMVar = MkAuxMVar(mvarDecl.LCtx, mvarDecl.LocalInstances, type);
            return AssignConst(mvar, args1.Length, auxMVar);
        }
        return false;
    }

    private Expr ConsumeLetIfZeta(Expr e)
    {
        var cfg = Config;
        return cfg.Zeta || cfg.ZetaUnused ? ConsumeUnusedLet(e, consumeNondep: cfg.ZetaUnused || cfg.ZetaHave) : e;
    }

    // ---------------------------------------------------------------- quick

    private LBool IsDefEqQuick(Expr t, Expr s)
    {
        t = ConsumeLetIfZeta(t);
        s = ConsumeLetIfZeta(s);
        switch (t, s)
        {
            case (NatLitExpr or StrLitExpr, NatLitExpr or StrLitExpr):
                return ToLBool(t.Equals(s));
            case (SortExpr u, SortExpr v):
                return ToLBool(IsLevelDefEqAux(u.Level, v.Level));
            case (LamExpr, LamExpr):
            case (ForallExpr, ForallExpr):
                return t.Equals(s) ? LBool.True : ToLBool(IsDefEqBinding(t, s));
            case (FVarExpr f1, FVarExpr f2):
                if (f1.Id == f2.Id)
                {
                    return LBool.True;
                }
                if (GetLocalDecl(f1.Id).IsLet() || GetLocalDecl(f2.Id).IsLet())
                {
                    return LBool.Undef;
                }
                return IsDefEqProofIrrel(t, s);
            default:
                return IsDefEqQuickOther(t, s);
        }
    }

    private LBool IsDefEqQuickOther(Expr t, Expr s)
    {
        // Pattern annotations must not be propagated; other metadata is kept for the printer.
        if (t.PatternAnnotation() is { } t0)
        {
            return IsDefEqQuick(t0, s);
        }
        if (s.PatternAnnotation() is { } s0)
        {
            return IsDefEqQuick(t, s0);
        }
        if (t.Equals(s))
        {
            return LBool.True;
        }
        if (EtaEq(t, s) || EtaEq(s, t))
        {
            return LBool.True; // t =?= fun xs => t xs
        }
        var tFn = t.GetAppFn();
        var sFn = s.GetAppFn();
        if (tFn is not MVarExpr && sFn is not MVarExpr)
        {
            return LBool.Undef;
        }
        if (IsAssignedMVar(tFn))
        {
            return IsDefEqQuick(this.InstantiateMVars(t), s);
        }
        if (IsAssignedMVar(sFn))
        {
            return IsDefEqQuick(t, this.InstantiateMVars(s));
        }
        if (ExpandDelayedAssigned(t) is { } t1)
        {
            return IsDefEqQuick(t1, s);
        }
        if (ExpandDelayedAssigned(s) is { } s1)
        {
            return IsDefEqQuick(t, s1);
        }
        if (tFn is MVarExpr && sFn is MVarExpr && tFn.Equals(sFn))
        {
            return ToLBool(IsDefEqMVarSelf(tFn, t.GetAppArgs(), s.GetAppArgs()));
        }
        bool tAssign = IsAssignable(tFn);
        bool sAssign = IsAssignable(sFn);
        if (tAssign && !sAssign)
        {
            return ToLBool(ProcessAssignment1(t, s));
        }
        if (!tAssign && sAssign)
        {
            return ToLBool(ProcessAssignment1(s, t));
        }
        if (!tAssign && !sAssign)
        {
            // Both read-only or goals: proof irrelevance may still solve it (Lean's isDefEqPerfIssue).
            var r = IsDefEqProofIrrel(t, s);
            if (r != LBool.Undef)
            {
                return r;
            }
            if (Config.IsDefEqStuckEx)
            {
                throw new IsDefEqStuckException();
            }
            return LBool.False;
        }
        return IsDefEqQuickMVarMVar(t, s);
    }

    // Both sides are ?m … applications.
    private LBool IsDefEqQuickMVarMVar(Expr t, Expr s)
    {
        if (s is MVarExpr && t is not MVarExpr)
        {
            // ?m t =?= ?n: try ?n := ?m t first, which is precise.
            return CheckpointDefEq(() => ProcessAssignment(s, t)) ? LBool.True : ToLBool(ProcessAssignment(t, s));
        }
        return CheckpointDefEq(() => ProcessAssignment(t, s)) ? LBool.True : ToLBool(ProcessAssignment(s, t));
    }

    private static bool WhenUndefDo(LBool x, Func<bool> k) => x switch
    {
        LBool.True => true,
        LBool.False => false,
        _ => k(),
    };

    private bool UnstuckMVar(Expr e, Func<Expr, bool> successK, Func<bool> failK)
    {
        if (GetStuckMVar(e) is not { } mvarId)
        {
            return failK();
        }
        if (SynthPending(mvarId))
        {
            return successK(this.InstantiateMVars(e));
        }
        if (Config.IsDefEqStuckEx && GetMVarDecl(mvarId).Depth < MCtx.Depth)
        {
            throw new IsDefEqStuckException(); // Lean issue #2736
        }
        return failK();
    }

    private bool IsDefEqOnFailure(Expr t, Expr s) =>
        UnstuckMVar(t, t1 => IsExprDefEqAux(t1, s), () =>
            UnstuckMVar(s, s1 => IsExprDefEqAux(t, s1), () => false)); // no unification hints

    // ---------------------------------------------------------------- projections

    private enum DeltaStepKind
    {
        Eq,
        Unknown,
        Cont,
        Diff,
    }

    // One step of lazy delta for (f a).i =?= (g a).i.
    private (DeltaStepKind Kind, Expr T, Expr S) IsDefEqDeltaStep(Expr t, Expr s)
    {
        var tInfo = IsDeltaCandidate(t);
        var sInfo = IsDeltaCandidate(s);
        if (tInfo is null && sInfo is null)
        {
            return (DeltaStepKind.Unknown, t, s);
        }
        if (sInfo is null)
        {
            return UnfoldDefinition(t) is { } t1 ? K(t1, s) : (DeltaStepKind.Unknown, t, s);
        }
        if (tInfo is null)
        {
            return UnfoldDefinition(s) is { } s1 ? K(t, s1) : (DeltaStepKind.Unknown, t, s);
        }
        switch (tInfo.Hints().HintsCompare(sInfo.Hints()))
        {
            case < 0:
                return UnfoldDefinition(t) is { } t2 ? K(t2, s) : (DeltaStepKind.Unknown, t, s);
            case > 0:
                return UnfoldDefinition(s) is { } s2 ? K(t, s2) : (DeltaStepKind.Unknown, t, s);
            default:
                if (tInfo.Name == sInfo.Name && t is AppExpr && s is AppExpr && TryHeuristic(t, s))
                {
                    return (DeltaStepKind.Eq, t, s);
                }
                return UnfoldBoth(t, s);
        }

        (DeltaStepKind, Expr, Expr) UnfoldBoth(Expr t, Expr s)
        {
            if (UnfoldDefinition(t) is { } t1)
            {
                return UnfoldDefinition(s) is { } s1 ? K(t1, s1) : K(t1, s);
            }
            return UnfoldDefinition(s) is { } s2 ? K(t, s2) : (DeltaStepKind.Unknown, t, s);
        }

        (DeltaStepKind, Expr, Expr) K(Expr t, Expr s)
        {
            t = WhnfCore(t);
            s = WhnfCore(s);
            return IsDefEqQuick(t, s) switch
            {
                LBool.True => (DeltaStepKind.Eq, t, s),
                LBool.False => (DeltaStepKind.Diff, t, s),
                _ => (DeltaStepKind.Cont, t, s),
            };
        }
    }

    private bool IsDefEqProjDelta(Expr t, Expr s, int i)
    {
        t = WhnfCore(t);
        s = WhnfCore(s);
        if (IsDefEqQuick(t, s) == LBool.True)
        {
            return true;
        }
        while (true)
        {
            var (kind, t1, s1) = IsDefEqDeltaStep(t, s);
            switch (kind)
            {
                case DeltaStepKind.Cont:
                    (t, s) = (t1, s1);
                    continue;
                case DeltaStepKind.Eq:
                    return true;
                default:
                    if (ProjectCore(t1, i) is { } tp && ProjectCore(s1, i) is { } sp)
                    {
                        return IsExprDefEqAux(tp, sp);
                    }
                    return IsExprDefEqAux(t1, s1);
            }
        }
    }

    private bool IsDefEqProj(Expr t, Expr s)
    {
        switch (t, s)
        {
            case (ProjExpr pt, ProjExpr ps):
            {
                // A class's projection parameter is instance-implicit: compare at `implicit`.
                bool fromClass = Attributes.IsClass(pt.TypeName);
                if (pt.Index != ps.Index || pt.TypeName != ps.TypeName)
                {
                    return false;
                }
                return fromClass
                    ? WithImplicitConfig(() => IsDefEqProjDelta(pt.Struct, ps.Struct, pt.Index))
                    : IsDefEqProjDelta(pt.Struct, ps.Struct, pt.Index);
            }
            case (ProjExpr { Index: 0 } p, _):
                return IsDefEqSingleton(p.TypeName, p.Struct, s);
            case (_, ProjExpr { Index: 0 } p):
                return IsDefEqSingleton(p.TypeName, p.Struct, t);
            default:
                return false;
        }

        // (?m …).1 =?= v for a one-field structure: ?m … =?= ⟨v⟩ (not for classes, Lean issue #2011).
        bool IsDefEqSingleton(Name structName, Expr s, Expr v)
        {
            if (Attributes.IsClass(structName))
            {
                return false;
            }
            if (GetNonRecStructureCtor(structName) is not { NumFields: 1 } ctorVal)
            {
                return false;
            }
            var sType = Whnf(InferType(s));
            if (sType.GetAppFn() is not ConstExpr sTypeFn || sTypeFn.Name != structName)
            {
                return false;
            }
            s = Whnf(s);
            var sFn = s.GetAppFn();
            if (sFn is not MVarExpr || !IsAssignable(sFn))
            {
                return false;
            }
            var ctorApp = Expr.App(ExprExtensions.MkAppN(Expr.Const(ctorVal.Name, sTypeFn.Levels), sType.GetAppArgs()), v);
            return ProcessAssignment1(s, ctorApp);
        }
    }

    // ---------------------------------------------------------------- applications and the rest

    // Applications in whnf: compare heads and arguments (spines once, not curried prefixes).
    private bool IsDefEqApp(Expr t, Expr s)
    {
        var tFn = t.GetAppFn();
        var sFn = s.GetAppFn();
        if (tFn is ConstExpr tc && sFn is ConstExpr sc && tc.Name == sc.Name)
        {
            return CheckpointDefEq(() => IsDefEqArgs(tFn, t.GetAppArgs(), s.GetAppArgs()) && IsListLevelDefEqAux(tc.Levels, sc.Levels));
        }
        return CheckpointDefEq(() => IsExprDefEqAux(tFn, sFn) && IsDefEqArgs(tFn, t.GetAppArgs(), s.GetAppArgs()));
    }

    // Values of a structure with one constructor and no fields are all equal.
    private bool IsDefEqUnitLike(Expr t, Expr s)
    {
        var tType = Whnf(InferType(t));
        if (tType.GetAppFn() is not ConstExpr c || GetNonRecStructureCtor(c.Name) is not { } ctorVal)
        {
            return false;
        }
        if (ctorVal.NumFields != 0 || !UseEtaStruct(ctorVal.Inductive))
        {
            return false;
        }
        return IsExprDefEqAux(tType, InferType(s));
    }

    // Keeps isDefEq consistent with whnf's class-projection unfolding at instances and implicit.
    private LBool IsDefEqProjInst(Expr t, Expr s)
    {
        if (GetTransparency() is not (TransparencyMode.Instances or TransparencyMode.Implicit))
        {
            return LBool.Undef;
        }
        var t1 = UnfoldProjInstWhenInstances(t);
        var s1 = UnfoldProjInstWhenInstances(s);
        if (t1 is null && s1 is null)
        {
            return LBool.Undef;
        }
        return ToLBool(IsExprDefEqAux(t1 ?? t, s1 ?? s));
    }

    private LBool IsDefEqLateSpecialCases(Expr t, Expr s)
    {
        var r = IsDefEqProjInst(t, s);
        if (r != LBool.Undef)
        {
            return r;
        }
        r = IsDefEqStringLit(t, s);
        if (r != LBool.Undef)
        {
            return r;
        }
        return IsDefEqUnitLike(t, s) ? LBool.True : LBool.Undef;
    }

    // throwOnStuckAfterApp off: a stuck exception from isDefEqOnFailure is deferred until the late
    // special cases have had their chance.
    private bool IsDefEqAppFallback(Expr t, Expr s)
    {
        var saved = SaveState();
        bool? r;
        try
        {
            r = IsDefEqOnFailure(t, s);
        }
        catch (IsDefEqStuckException)
        {
            Restore(saved);
            r = null;
        }
        if (r == true)
        {
            return true;
        }
        if (IsDefEqLateSpecialCases(t, s) == LBool.True)
        {
            return true;
        }
        if (r is null)
        {
            throw new IsDefEqStuckException();
        }
        return false;
    }

    private bool IsExprDefEqExpensive(Expr t, Expr s)
    {
        var r = IsDefEqEta(t, s);
        if (r != LBool.Undef)
        {
            return r == LBool.True;
        }
        r = IsDefEqEta(s, t);
        if (r != LBool.Undef)
        {
            return r == LBool.True;
        }
        if (IsDefEqProj(t, s))
        {
            return true;
        }
        var t1 = WhnfCore(t);
        var s1 = WhnfCore(s);
        if (!t.Equals(t1) || !s.Equals(s1))
        {
            return IsExprDefEqAux(t1, s1);
        }
        r = IsDefEqNat(t, s);
        if (r != LBool.Undef)
        {
            return r == LBool.True;
        }
        r = IsDefEqOffset(t, s);
        if (r != LBool.Undef)
        {
            return r == LBool.True;
        }
        r = IsDefEqDelta(t, s);
        if (r != LBool.Undef)
        {
            return r == LBool.True;
        }
        // Structure eta after lazy delta, or it would run at every step of a reduction chain.
        if (IsDefEqEtaStruct(t, s) || IsDefEqEtaStruct(s, t))
        {
            return true;
        }
        if (t is ConstExpr tc && s is ConstExpr sc)
        {
            return tc.Name == sc.Name && IsListLevelDefEqAux(tc.Levels, sc.Levels);
        }
        if (t is AppExpr && s is AppExpr)
        {
            return IsDefEqApp(t, s) || IsDefEqAppFallback(t, s);
        }
        return WhenUndefDo(IsDefEqLateSpecialCases(t, s), () => IsDefEqOnFailure(t, s));
    }

    // whnfCore with proj := yesWithDeltaI (backward.isDefEq.lazyWhnfCore).
    private Expr WhnfCoreAtDefEq(Expr e) =>
        Config.Proj == ProjReductionKind.YesWithDeltaI ? WhnfCore(e) : WithConfig(c => c with { Proj = ProjReductionKind.YesWithDeltaI }, () => WhnfCore(e));

    /// <summary>
    /// Unifies <paramref name="t"/> and <paramref name="s"/>, assigning metavariables (Lean's
    /// <c>isExprDefEqAuxImpl</c>). Assignments are not rolled back on failure; use
    /// <see cref="IsDefEq"/> for that.
    /// </summary>
    public bool IsExprDefEqAux(Expr t, Expr s)
    {
        ArgumentNullException.ThrowIfNull(t);
        ArgumentNullException.ThrowIfNull(s);
        while (true)
        {
            Budget.Tick();
            var r = IsDefEqQuick(t, s);
            if (r != LBool.Undef)
            {
                return r == LBool.True;
            }
            r = IsDefEqProofIrrel(t, s);
            if (r != LBool.Undef)
            {
                return r == LBool.True;
            }
            var t1 = WhnfCoreAtDefEq(t);
            var s1 = WhnfCoreAtDefEq(s);
            if (!t.Equals(t1) || !s.Equals(s1))
            {
                (t, s) = (t1, s1);
                continue;
            }
            break;
        }
        // Instantiate once here, not at every level (Ansatz's quadratic re-instantiation).
        t = this.InstantiateMVars(t);
        s = this.InstantiateMVars(s);
        int numPostponed = Postponed.Count;
        bool permanent = !t.HasExprMVar && !t.HasLevelMVar && !s.HasExprMVar && !s.HasLevelMVar;
        var cache = permanent ? _defEqPermCache : _defEqTransCache;
        var key = new DefEqKey(Config.Key, t, s);
        if (cache.TryGetValue(key, out bool cached))
        {
            return cached;
        }
        bool result = IsExprDefEqExpensive(t, s);
        if (numPostponed == Postponed.Count)
        {
            if (!permanent)
            {
                // Key on the current assignments, or it is wrong after backtracking (Lean issue #1870).
                key = new DefEqKey(Config.Key, this.InstantiateMVars(t), this.InstantiateMVars(s));
            }
            cache[key] = result;
        }
        return result;
    }

    // ---------------------------------------------------------------- entry points

    /// <summary>
    /// Whether <paramref name="t"/> and <paramref name="s"/> are definitionally equal at the
    /// current transparency, assigning metavariables of the current depth to make them so (Lean's
    /// <c>isDefEq</c>). On failure the metavariable context is left as it was.
    /// </summary>
    public bool IsDefEq(Expr t, Expr s)
    {
        ArgumentNullException.ThrowIfNull(t);
        ArgumentNullException.ThrowIfNull(s);
        _defEqPermCache.Clear();
        return CheckpointDefEq(() => IsExprDefEqAux(t, s), mayPostpone: true);
    }

    /// <summary>
    /// <see cref="IsDefEq"/>, returning false when unification throws a Meta error (Lean's
    /// <c>isDefEqGuarded</c>). Running out of fuel or time still propagates, as Lean's runtime
    /// exceptions do.
    /// </summary>
    public bool IsDefEqGuarded(Expr t, Expr s)
    {
        try
        {
            return IsDefEq(t, s);
        }
        catch (MetaException ex) when (ex is not MetaResourceException)
        {
            return false;
        }
    }

    /// <summary><see cref="IsDefEq"/> at <c>default</c> (Lean's <c>isDefEqD</c>).</summary>
    public bool IsDefEqD(Expr t, Expr s) => WithDefault(() => IsDefEq(t, s));

    /// <summary><see cref="IsDefEq"/> at <c>instances</c> (Lean's <c>isDefEqI</c>).</summary>
    public bool IsDefEqI(Expr t, Expr s) => WithReducibleAndInstances(() => IsDefEq(t, s));

    /// <summary>Runs <paramref name="k"/> with first-order and quasi-pattern approximation (Lean's <c>approxDefEq</c>).</summary>
    public T ApproxDefEq<T>(Func<T> k) => WithConfig(c => c with { FoApprox = true, QuasiPatternApprox = true }, k);

    /// <summary>Like <see cref="ApproxDefEq{T}"/>, with constant approximation too (Lean's <c>fullApproxDefEq</c>).</summary>
    public T FullApproxDefEq<T>(Func<T> k) => WithConfig(c => c with { FoApprox = true, QuasiPatternApprox = true, ConstApprox = true }, k);

    /// <summary><see cref="IsDefEq"/> under <see cref="ApproxDefEq{T}"/> (Lean's <c>isDefEqNoConstantApprox</c>).</summary>
    public bool IsDefEqNoConstantApprox(Expr t, Expr s) => ApproxDefEq(() => IsDefEq(t, s));
}
