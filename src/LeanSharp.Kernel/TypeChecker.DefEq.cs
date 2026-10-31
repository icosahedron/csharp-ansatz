using LeanSharp.Cic;

namespace LeanSharp.Kernel;

public sealed partial class TypeChecker
{
    private enum Tri : byte
    {
        False,
        True,
        Unknown,
    }

    private enum ReductionStatus : byte
    {
        Continue,
        DefUnknown,
        DefEqual,
        DefDiff,
    }

    private static Tri ToTri(bool b) => b ? Tri.True : Tri.False;

    /// <summary>Whether <paramref name="t"/> and <paramref name="s"/> are definitionally equal (sound, incomplete).</summary>
    public bool IsDefEq(Expr t, Expr s)
    {
        bool r = IsDefEqCore(t, s);
        if (r)
        {
            CacheSuccess(t, s);
        }
        return r;
    }

    private bool IsDefEqCore(Expr t, Expr s)
    {
        Tick();
        var r = QuickIsDefEq(t, s);
        if (r != Tri.Unknown)
        {
            return r == Tri.True;
        }

        // Proofs by reflection: a closed term against `Bool.true` is fully reduced.
        if ((!t.HasFVar || _eagerReduce) && s is ConstExpr sc && sc.Name == KernelNames.BoolTrue)
        {
            if (Whnf(t) is ConstExpr wc && wc.Name == KernelNames.BoolTrue)
            {
                return true;
            }
        }

        // whnf_core without delta, and without whnf on projected structures.
        var tn = WhnfCore(t, cheapRec: false, cheapProj: true);
        var sn = WhnfCore(s, cheapRec: false, cheapProj: true);
        if (!ReferenceEquals(tn, t) || !ReferenceEquals(sn, s))
        {
            r = QuickIsDefEq(tn, sn);
            if (r != Tri.Unknown)
            {
                return r == Tri.True;
            }
        }

        r = IsDefEqProofIrrel(tn, sn);
        if (r != Tri.Unknown)
        {
            return r == Tri.True;
        }

        // Lazy delta reduction updates tn and sn even when it returns Unknown.
        r = LazyDeltaReduction(ref tn, ref sn);
        if (r != Tri.Unknown)
        {
            return r == Tri.True;
        }

        if (tn is ConstExpr tc && sn is ConstExpr sc2 && tc.Name == sc2.Name && IsDefEqLevels(tc.Levels, sc2.Levels))
        {
            return true;
        }
        if (tn is FVarExpr tf && sn is FVarExpr sf && tf.Id == sf.Id)
        {
            return true;
        }
        if (tn is ProjExpr tp && sn is ProjExpr sp && tp.TypeName == sp.TypeName && tp.Index == sp.Index)
        {
            var tStruct = tp.Struct;
            var sStruct = sp.Struct;
            if (LazyDeltaProjReduction(ref tStruct, ref sStruct, tp.TypeName, tp.Index))
            {
                return true;
            }
        }

        // whnf_core again, now using whnf to reduce projected structures.
        var tnn = WhnfCore(tn);
        var snn = WhnfCore(sn);
        if (!ReferenceEquals(tnn, tn) || !ReferenceEquals(snn, sn))
        {
            return IsDefEqCore(tnn, snn);
        }

        // tn and sn are in weak head normal form (modulo proof irrelevance).
        if (IsDefEqApp(tn, sn))
        {
            return true;
        }
        if (TryEtaExpansion(tn, sn))
        {
            return true;
        }
        if (TryEtaStruct(tn, sn))
        {
            return true;
        }
        r = TryStringLitExpansion(tn, sn);
        if (r != Tri.Unknown)
        {
            return r == Tri.True;
        }
        return IsDefEqUnitLike(tn, sn);
    }

    /// <summary>The easy cases of definitional equality.</summary>
    private Tri QuickIsDefEq(Expr t, Expr s)
    {
        if (t.AlphaEquals(s) || SucceededBefore(t, s))
        {
            return Tri.True;
        }
        if (t.Kind == s.Kind)
        {
            switch (t)
            {
                case BindingExpr:
                    return ToTri(IsDefEqBinding((BindingExpr)t, (BindingExpr)s));
                case SortExpr ts:
                    return ToTri(LevelOps.IsEquivalent(ts.Level, ((SortExpr)s).Level));
                case MDataExpr tm:
                    return ToTri(IsDefEq(tm.Expr, ((MDataExpr)s).Expr));
                case NatLitExpr tn:
                    return ToTri(tn.Value == ((NatLitExpr)s).Value);
                case StrLitExpr tstr:
                    return ToTri(string.Equals(tstr.Value, ((StrLitExpr)s).Value, StringComparison.Ordinal));
            }
        }
        return Tri.Unknown;
    }

    /// <summary>
    /// Lambdas/Pis are definitionally equal if their domains and bodies are (bodies compared under
    /// fresh free variables, created only when a body actually uses its binder).
    /// </summary>
    private bool IsDefEqBinding(BindingExpr t0, BindingExpr s0)
    {
        var kind = t0.Kind;
        var subst = new List<Expr>();
        Expr t = t0, s = s0;
        do
        {
            var tb = (BindingExpr)t;
            var sb = (BindingExpr)s;
            Expr? varSType = null;
            if (!tb.BinderType.AlphaEquals(sb.BinderType))
            {
                var span = System.Runtime.InteropServices.CollectionsMarshal.AsSpan(subst);
                varSType = ExprOps.InstantiateRev(sb.BinderType, span);
                var varTType = ExprOps.InstantiateRev(tb.BinderType, span);
                if (!IsDefEq(varTType, varSType))
                {
                    return false;
                }
            }
            if (tb.Body.HasLooseBVars || sb.Body.HasLooseBVars)
            {
                varSType ??= ExprOps.InstantiateRev(sb.BinderType, System.Runtime.InteropServices.CollectionsMarshal.AsSpan(subst));
                subst.Add(LocalContext.MkLocalDecl(_ngen, sb.BinderName, varSType, sb.BinderInfo));
            }
            else
            {
                subst.Add(DontCare);
            }
            t = tb.Body;
            s = sb.Body;
        }
        while (t.Kind == kind && s.Kind == kind);
        var final = System.Runtime.InteropServices.CollectionsMarshal.AsSpan(subst);
        return IsDefEq(ExprOps.InstantiateRev(t, final), ExprOps.InstantiateRev(s, final));
    }

    private static bool IsDefEqLevels(EquatableArray<Level> a, EquatableArray<Level> b)
    {
        if (a.Count != b.Count)
        {
            return false;
        }
        for (int i = 0; i < a.Count; i++)
        {
            if (!LevelOps.IsEquivalent(a[i], b[i]))
            {
                return false;
            }
        }
        return true;
    }

    private bool IsDefEqArgs(Expr t, Expr s)
    {
        while (t is AppExpr ta && s is AppExpr sa)
        {
            if (!IsDefEq(ta.Arg, sa.Arg))
            {
                return false;
            }
            t = ta.Fn;
            s = sa.Fn;
        }
        return t is not AppExpr && s is not AppExpr;
    }

    private bool TryEtaExpansion(Expr t, Expr s) => TryEtaExpansionCore(t, s) || TryEtaExpansionCore(s, t);

    /// <summary>Solves <c>(fun x => b) =?= s</c> by eta-expanding <c>s</c>.</summary>
    private bool TryEtaExpansionCore(Expr t, Expr s)
    {
        if (t is LamExpr && s is not LamExpr)
        {
            if (Whnf(Infer(s)) is not ForallExpr sType)
            {
                return false;
            }
            var newS = Expr.Lam(sType.BinderName, sType.BinderType, Expr.App(s, Expr.BVar(0)), sType.BinderInfo);
            return IsDefEq(t, newS);
        }
        return false;
    }

    private bool TryEtaStruct(Expr t, Expr s) => TryEtaStructCore(t, s) || TryEtaStructCore(s, t);

    /// <summary>Checks whether <c>s</c> is <c>S.mk t.1 … t.n</c>.</summary>
    private bool TryEtaStructCore(Expr t, Expr s)
    {
        if (s.GetAppFn() is not ConstExpr f || Env.Find(f.Name) is not ConstructorInfo fVal)
        {
            return false;
        }
        if (s.GetAppNumArgs() != fVal.NumParams + fVal.NumFields || !IsNonRecStructure(fVal.Inductive))
        {
            return false;
        }
        if (!IsDefEq(Infer(t), Infer(s)))
        {
            return false;
        }
        var sArgs = s.GetAppArgs();
        for (int i = fVal.NumParams; i < sArgs.Length; i++)
        {
            var proj = Expr.Proj(fVal.Inductive, i - fVal.NumParams, t);
            if (!IsDefEq(proj, sArgs[i]))
            {
                return false;
            }
        }
        return true;
    }

    /// <summary><c>f a₁ … aₙ =?= g b₁ … bₙ</c> by <c>f =?= g</c> and <c>aᵢ =?= bᵢ</c>.</summary>
    private bool IsDefEqApp(Expr t, Expr s)
    {
        if (t is not AppExpr || s is not AppExpr)
        {
            return false;
        }
        var tArgs = t.GetAppArgs();
        var sArgs = s.GetAppArgs();
        if (!IsDefEq(t.GetAppFn(), s.GetAppFn()) || tArgs.Length != sArgs.Length)
        {
            return false;
        }
        for (int i = 0; i < tArgs.Length; i++)
        {
            if (!IsDefEq(tArgs[i], sArgs[i]))
            {
                return false;
            }
        }
        return true;
    }

    /// <summary>Proof irrelevance: two proofs of the same proposition are equal.</summary>
    private Tri IsDefEqProofIrrel(Expr t, Expr s)
    {
        var tType = Infer(t);
        if (!IsProp(tType))
        {
            return Tri.Unknown;
        }
        var sType = Infer(s);
        return ToTri(IsDefEq(tType, sType));
    }

    private static (Expr, Expr) Ordered(Expr t, Expr s) => t.GetHashCode() <= s.GetHashCode() ? (t, s) : (s, t);

    private bool FailedBefore(Expr t, Expr s) =>
        t.GetHashCode() == s.GetHashCode()
            ? _defEqFailure.Contains((t, s)) || _defEqFailure.Contains((s, t))
            : _defEqFailure.Contains(Ordered(t, s));

    private void CacheFailure(Expr t, Expr s) => _defEqFailure.Add(Ordered(t, s));

    private bool SucceededBefore(Expr t, Expr s) =>
        t.GetHashCode() == s.GetHashCode()
            ? _defEqSuccess.Contains((t, s)) || _defEqSuccess.Contains((s, t))
            : _defEqSuccess.Contains(Ordered(t, s));

    private void CacheSuccess(Expr t, Expr s) => _defEqSuccess.Add(Ordered(t, s));

    /// <summary>If <paramref name="e"/> is a projection application that <c>WhnfCore</c> reduces, the reduct.</summary>
    private Expr? TryUnfoldProjApp(Expr e)
    {
        if (e.GetAppFn() is ProjExpr)
        {
            var eNew = WhnfCore(e);
            return eNew.AlphaEquals(e) ? null : eNew;
        }
        return null;
    }

    private static int CompareHints(ReducibilityHints h1, ReducibilityHints h2)
    {
        if (h1.Kind == h2.Kind)
        {
            if (h1.Kind == ReducibilityHintsKind.Regular)
            {
                return h1.Height == h2.Height ? 0 : h1.Height > h2.Height ? -1 : 1;
            }
            return 0;
        }
        if (h1.Kind == ReducibilityHintsKind.Opaque)
        {
            return 1;
        }
        if (h2.Kind == ReducibilityHintsKind.Opaque)
        {
            return -1;
        }
        if (h1.Kind == ReducibilityHintsKind.Abbrev)
        {
            return -1;
        }
        if (h2.Kind == ReducibilityHintsKind.Abbrev)
        {
            return 1;
        }
        throw new InvalidOperationException("unreachable hint combination");
    }

    /// <summary>One step of lazy delta reduction: unfold the side with the greater definitional height.</summary>
    private ReductionStatus LazyDeltaReductionStep(ref Expr tn, ref Expr sn)
    {
        var dt = IsDelta(tn);
        var ds = IsDelta(sn);
        if (dt is null && ds is null)
        {
            return ReductionStatus.DefUnknown;
        }
        if (dt is not null && ds is null)
        {
            if (TryUnfoldProjApp(sn) is { } snNew)
            {
                sn = snNew;
            }
            else
            {
                tn = WhnfCore(UnfoldDefinition(tn)!, cheapRec: false, cheapProj: true);
            }
        }
        else if (dt is null && ds is not null)
        {
            if (TryUnfoldProjApp(tn) is { } tnNew)
            {
                tn = tnNew;
            }
            else
            {
                sn = WhnfCore(UnfoldDefinition(sn)!, cheapRec: false, cheapProj: true);
            }
        }
        else
        {
            int c = CompareHints(HintsOf(dt!), HintsOf(ds!));
            if (c < 0)
            {
                tn = WhnfCore(UnfoldDefinition(tn)!, cheapRec: false, cheapProj: true);
            }
            else if (c > 0)
            {
                sn = WhnfCore(UnfoldDefinition(sn)!, cheapRec: false, cheapProj: true);
            }
            else
            {
                if (tn is AppExpr && sn is AppExpr && ReferenceEquals(dt, ds) && HintsOf(dt!).Kind == ReducibilityHintsKind.Regular)
                {
                    // Same definition on both sides: try the arguments before unfolding.
                    if (!FailedBefore(tn, sn))
                    {
                        if (IsDefEqLevels(((ConstExpr)tn.GetAppFn()).Levels, ((ConstExpr)sn.GetAppFn()).Levels)
                            && IsDefEqArgs(tn, sn))
                        {
                            return ReductionStatus.DefEqual;
                        }
                        CacheFailure(tn, sn);
                    }
                }
                tn = WhnfCore(UnfoldDefinition(tn)!, cheapRec: false, cheapProj: true);
                sn = WhnfCore(UnfoldDefinition(sn)!, cheapRec: false, cheapProj: true);
            }
        }
        return QuickIsDefEq(tn, sn) switch
        {
            Tri.True => ReductionStatus.DefEqual,
            Tri.False => ReductionStatus.DefDiff,
            _ => ReductionStatus.Continue,
        };
    }

    private static bool IsNatZero(Expr t) =>
        (t is ConstExpr c && c.Name == KernelNames.NatZero && c.Levels.Count == 0) || (t is NatLitExpr n && n.Value.IsZero);

    private static Expr? IsNatSucc(Expr t)
    {
        if (t is NatLitExpr n && !n.Value.IsZero)
        {
            return Expr.NatLit(n.Value - 1);
        }
        if (t is AppExpr a && a.Fn is ConstExpr c && c.Name == KernelNames.NatSucc && c.Levels.Count == 0)
        {
            return a.Arg;
        }
        return null;
    }

    private Tri IsDefEqOffset(Expr t, Expr s)
    {
        if (IsNatZero(t) && IsNatZero(s))
        {
            return Tri.True;
        }
        if (IsNatSucc(t) is { } pt && IsNatSucc(s) is { } ps)
        {
            return ToTri(IsDefEqCore(pt, ps));
        }
        return Tri.Unknown;
    }

    private Tri LazyDeltaReduction(ref Expr tn, ref Expr sn)
    {
        while (true)
        {
            var r = IsDefEqOffset(tn, sn);
            if (r != Tri.Unknown)
            {
                return r;
            }
            if ((!tn.HasFVar && !sn.HasFVar) || _eagerReduce)
            {
                if (ReduceNat(tn) is { } tv)
                {
                    return ToTri(IsDefEqCore(tv, sn));
                }
                if (ReduceNat(sn) is { } sv)
                {
                    return ToTri(IsDefEqCore(tn, sv));
                }
            }
            if (ReduceNative(tn) is { } tnat)
            {
                return ToTri(IsDefEqCore(tnat, sn));
            }
            if (ReduceNative(sn) is { } snat)
            {
                return ToTri(IsDefEqCore(tn, snat));
            }
            switch (LazyDeltaReductionStep(ref tn, ref sn))
            {
                case ReductionStatus.Continue:
                    break;
                case ReductionStatus.DefUnknown:
                    return Tri.Unknown;
                case ReductionStatus.DefEqual:
                    return Tri.True;
                default:
                    return Tri.False;
            }
        }
    }

    /// <summary>Checks <c>t.idx =?= s.idx</c> by lazily unfolding <c>t</c> and <c>s</c>.</summary>
    private bool LazyDeltaProjReduction(ref Expr tn, ref Expr sn, Name structName, int idx)
    {
        while (true)
        {
            switch (LazyDeltaReductionStep(ref tn, ref sn))
            {
                case ReductionStatus.Continue:
                    break;
                case ReductionStatus.DefEqual:
                    return true;
                default:
                    if (ReduceProjCore(tn, structName, idx) is { } t && ReduceProjCore(sn, structName, idx) is { } s)
                    {
                        return IsDefEqCore(t, s);
                    }
                    return IsDefEqCore(tn, sn);
            }
        }
    }

    private Tri TryStringLitExpansionCore(Expr t, Expr s)
    {
        if (t is StrLitExpr && s is AppExpr sa && sa.Fn is ConstExpr c && c.Name == KernelNames.StringOfList && c.Levels.Count == 0)
        {
            return ToTri(IsDefEqCore(Whnf(StringLitToConstructor(t)), s));
        }
        return Tri.Unknown;
    }

    private Tri TryStringLitExpansion(Expr t, Expr s)
    {
        var r = TryStringLitExpansionCore(t, s);
        return r != Tri.Unknown ? r : TryStringLitExpansionCore(s, t);
    }

    /// <summary>Values of a structure with one constructor and no fields are all equal.</summary>
    private bool IsDefEqUnitLike(Expr t, Expr s)
    {
        var tType = Whnf(Infer(t));
        if (tType.GetAppFn() is not ConstExpr I || !IsNonRecStructure(I.Name))
        {
            return false;
        }
        var ctorName = ((InductiveInfo)Env.Get(I.Name)).Constructors[0];
        if (((ConstructorInfo)Env.Get(ctorName)).NumFields != 0)
        {
            return false;
        }
        return IsDefEqCore(tType, Infer(s));
    }
}
