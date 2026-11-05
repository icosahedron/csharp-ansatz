using Warrant.Cic;
using Warrant.Kernel;

namespace Warrant.Meta;

/// <summary>The Init constants <c>simp</c> builds its proofs from; <c>Warrant.Engine.EmittedConstants</c> lists them all (KTD29).</summary>
public static class SimpNames
{
#pragma warning disable CS1591 // Each field is the Init constant of its name.
    public static readonly Name Eq = Name.From("Eq");
    public static readonly Name EqRefl = Name.From("Eq", "refl");
    public static readonly Name EqSymm = Name.From("Eq", "symm");
    public static readonly Name EqTrans = Name.From("Eq", "trans");
    public static readonly Name EqMp = Name.From("Eq", "mp");
    public static readonly Name EqMpr = Name.From("Eq", "mpr");
    public static readonly Name EqNdrec = Name.From("Eq", "ndrec");
    public static readonly Name EqSubstr = Name.From("Eq", "substr");
    public static readonly Name Rfl = Name.From("rfl");
    public static readonly Name Iff = Name.From("Iff");
    public static readonly Name Ne = Name.From("Ne");
    public static readonly Name Not = Name.From("Not");
    public static readonly Name And = Name.From("And");
    public static readonly Name True = Name.From("True");
    public static readonly Name TrueIntro = Name.From("True", "intro");
    public static readonly Name False = Name.From("False");
    public static readonly Name FalseElim = Name.From("False", "elim");
    public static readonly Name Bool = Name.From("Bool");
    public static readonly Name BoolTrue = Name.From("Bool", "true");
    public static readonly Name BoolFalse = Name.From("Bool", "false");
    public static readonly Name Propext = Name.From("propext");
    public static readonly Name Funext = Name.From("funext");
    public static readonly Name CongrArg = Name.From("congrArg");
    public static readonly Name CongrFun = Name.From("congrFun");
    public static readonly Name CongrFun2 = Name.From("congrFun'");
    public static readonly Name Congr = Name.From("congr");
    public static readonly Name ImpliesCongr = Name.From("implies_congr");
    public static readonly Name ImpliesCongrCtx = Name.From("implies_congr_ctx");
    public static readonly Name ImpliesDepCongrCtx = Name.From("implies_dep_congr_ctx");
    public static readonly Name ForallCongr = Name.From("forall_congr");
    public static readonly Name ForallPropDomainCongr = Name.From("forall_prop_domain_congr");
    public static readonly Name OfEqTrue = Name.From("of_eq_true");
    public static readonly Name OfEqFalse = Name.From("of_eq_false");
    public static readonly Name EqTrue = Name.From("eq_true");
    public static readonly Name EqFalse = Name.From("eq_false");
    public static readonly Name EqTrueOfDecide = Name.From("eq_true_of_decide");
    public static readonly Name EqFalseOfDecide = Name.From("eq_false_of_decide");
    public static readonly Name Decide = Name.From("Decidable", "decide");
    public static readonly Name Ite = Name.From("ite");
    public static readonly Name Dite = Name.From("dite");
    public static readonly Name IteEqLeftOfEqTrue = Name.From("ite_eq_left_of_eq_true");
    public static readonly Name IteEqRightOfEqFalse = Name.From("ite_eq_right_of_eq_false");
    public static readonly Name DiteEqLeftOfEqTrue = Name.From("dite_eq_left_of_eq_true");
    public static readonly Name DiteEqRightOfEqFalse = Name.From("dite_eq_right_of_eq_false");
    public static readonly Name BoolOfNotEqTrue = Name.From("Bool", "of_not_eq_true");
    public static readonly Name BoolOfNotEqFalse = Name.From("Bool", "of_not_eq_false");
#pragma warning restore CS1591

    /// <summary>
    /// Every constant above that a proof can contain, except <c>True</c>: it is not a bundle root, but it is the type of
    /// the root <c>True.intro</c>, so it is always in the bundle.
    /// </summary>
    public static IReadOnlyList<Name> ProofConstants { get; } =
    [
        Eq, EqRefl, EqSymm, EqTrans, EqMp, EqMpr, EqNdrec, EqSubstr, Rfl, And, TrueIntro, False, FalseElim,
        Bool, BoolTrue, BoolFalse, Propext, Funext, CongrArg, CongrFun, CongrFun2, Congr, ImpliesCongr, ImpliesCongrCtx,
        ImpliesDepCongrCtx, ForallCongr, ForallPropDomainCongr, OfEqTrue, OfEqFalse, EqTrue, EqFalse, EqTrueOfDecide,
        EqFalseOfDecide, Decide, IteEqLeftOfEqTrue, IteEqRightOfEqFalse, DiteEqLeftOfEqTrue, DiteEqRightOfEqFalse,
        BoolOfNotEqTrue, BoolOfNotEqFalse,
    ];
}

// Lean/Meta/AppBuilder.lean: the proof-building helpers simp uses. The nested-congrArg fusion of
// Lean's mkCongrArg/mkCongrFun (congrArg?) is not ported; it only shortens proofs.
public sealed partial class MetaM
{
    /// <summary><c>a = b</c> (Lean's <c>mkEq</c>).</summary>
    public Expr MkEq(Expr a, Expr b)
    {
        var aType = InferType(a);
        return Expr.App(Expr.Const(SimpNames.Eq, GetLevel(aType)), aType, a, b);
    }

    /// <summary>A proof of <c>a = a</c> (Lean's <c>mkEqRefl</c>).</summary>
    public Expr MkEqRefl(Expr a)
    {
        var aType = InferType(a);
        return Expr.App(Expr.Const(SimpNames.EqRefl, GetLevel(aType)), aType, a);
    }

    /// <summary><c>@id.{0} prop proof</c> (Lean's <c>mkExpectedPropHint</c>).</summary>
    public static Expr MkExpectedPropHint(Expr proof, Expr prop) =>
        Expr.App(Expr.Const(TacticNames.Id, Level.Zero), prop, proof);

    /// <summary>Given <c>h : False</c>, a term of <paramref name="e"/> (Lean's <c>mkFalseElim</c>).</summary>
    public Expr MkFalseElim(Expr e, Expr h) => Expr.App(Expr.Const(SimpNames.FalseElim, GetLevel(e)), e, h);

    /// <summary>The <c>(α, a, b)</c> of an equality proof's type, in weak head normal form at default transparency.</summary>
    private (Expr Type, Expr Lhs, Expr Rhs, Level Level) EqProofSides(Name op, Expr h)
    {
        var hType = WhnfD(InferType(h));
        if (!ExprOps.IsAppOfArity(hType, SimpNames.Eq, 3))
        {
            throw new MetaException($"AppBuilder for `{op}`, equality proof expected\n  {h}\nhas type\n  {hType}");
        }
        var args = hType.GetAppArgs();
        return (args[0], args[1], args[2], ((ConstExpr)hType.GetAppFn()).Levels[0]);
    }

    private static bool IsRefl(Expr h) => h.IsAppOf(SimpNames.EqRefl);

    /// <summary>Given <c>h : a = b</c>, a proof of <c>b = a</c> (Lean's <c>mkEqSymm</c>).</summary>
    public Expr MkEqSymm(Expr h)
    {
        if (IsRefl(h))
        {
            return h;
        }
        var (α, a, b, u) = EqProofSides(SimpNames.EqSymm, h);
        return Expr.App(Expr.Const(SimpNames.EqSymm, u), α, a, b, h);
    }

    /// <summary>Given <c>h₁ : a = b</c> and <c>h₂ : b = c</c>, a proof of <c>a = c</c> (Lean's <c>mkEqTrans</c>).</summary>
    public Expr MkEqTrans(Expr h1, Expr h2)
    {
        if (IsRefl(h1))
        {
            return h2;
        }
        if (IsRefl(h2))
        {
            return h1;
        }
        var (α, a, b, u) = EqProofSides(SimpNames.EqTrans, h1);
        var (_, _, c, _) = EqProofSides(SimpNames.EqTrans, h2);
        return Expr.App(Expr.Const(SimpNames.EqTrans, u), α, a, b, c, h1, h2);
    }

    /// <summary>Given <c>f : α → β</c> and <c>h : a = b</c>, a proof of <c>f a = f b</c> (Lean's <c>mkCongrArg</c>).</summary>
    public Expr MkCongrArg(Expr f, Expr h)
    {
        if (IsRefl(h))
        {
            return MkEqRefl(Expr.App(f, ((AppExpr)h).Arg));
        }
        var (_, a, b, _) = EqProofSides(SimpNames.CongrArg, h);
        if (WhnfD(InferType(f)) is not ForallExpr { Body.HasLooseBVars: false } fType)
        {
            throw new MetaException($"AppBuilder for `congrArg`, non-dependent function expected\n  {f}");
        }
        return Expr.App(Expr.Const(SimpNames.CongrArg, GetLevel(fType.BinderType), GetLevel(fType.Body)), fType.BinderType, fType.Body, a, b, f, h);
    }

    /// <summary>Given <c>h : f = g</c> and <c>a</c>, a proof of <c>f a = g a</c> (Lean's <c>mkCongrFun</c>).</summary>
    public Expr MkCongrFun(Expr h, Expr a)
    {
        if (IsRefl(h))
        {
            return MkEqRefl(Expr.App(((AppExpr)h).Arg, a));
        }
        var (ρ, f, g, _) = EqProofSides(SimpNames.CongrFun, h);
        if (WhnfD(ρ) is not ForallExpr pi)
        {
            throw new MetaException($"AppBuilder for `congrFun`, equality proof between functions expected\n  {h}");
        }
        var β = Expr.Lam(pi.BinderName, pi.BinderType, pi.Body);
        var u = GetLevel(pi.BinderType);
        var v = GetLevel(Expr.App(β, a).HeadBeta());
        return Expr.App(Expr.Const(SimpNames.CongrFun, u, v), pi.BinderType, β, f, g, h, a);
    }

    /// <summary>Given <c>h₁ : f = g</c> and <c>h₂ : a = b</c>, a proof of <c>f a = g b</c> (Lean's <c>mkCongr</c>).</summary>
    public Expr MkCongr(Expr h1, Expr h2)
    {
        if (IsRefl(h1))
        {
            return MkCongrArg(((AppExpr)h1).Arg, h2);
        }
        if (IsRefl(h2))
        {
            return MkCongrFun(h1, ((AppExpr)h2).Arg);
        }
        var (ρ, f, g, _) = EqProofSides(SimpNames.Congr, h1);
        var (α, a, b, _) = EqProofSides(SimpNames.Congr, h2);
        if (WhnfD(ρ) is not ForallExpr { Body.HasLooseBVars: false } pi)
        {
            throw new MetaException($"AppBuilder for `congr`, non-dependent function expected\n  {h1}");
        }
        return Expr.App(Expr.Const(SimpNames.Congr, GetLevel(α), GetLevel(pi.Body)), α, pi.Body, f, g, a, b, h1, h2);
    }

    /// <summary>
    /// <c>@c args</c> with the implicit and instance arguments of <paramref name="constName"/> inferred: implicit ones by
    /// unifying each explicit argument's type with its binder, instances by synthesis (Lean's <c>mkAppM</c>).
    /// </summary>
    /// <exception cref="MetaException">An argument's type does not fit, or a hole remains.</exception>
    public Expr MkAppM(Name constName, params Expr[] args)
    {
        ArgumentNullException.ThrowIfNull(args);
        return WithNewMCtxDepth(() =>
        {
            var f = MkConstWithFreshMVarLevels(constName);
            var type = InferType(f);
            var applied = new List<Expr>();
            var instances = new List<MVarExpr>();
            int i = 0;
            while (i < args.Length)
            {
                if (type is not ForallExpr)
                {
                    type = WhnfD(type);
                }
                if (type is not ForallExpr pi)
                {
                    throw new MetaException($"AppBuilder for `{constName}`, too many explicit arguments provided");
                }
                Expr arg;
                if (pi.BinderInfo == BinderInfo.Default)
                {
                    arg = args[i++];
                    var argType = InferType(arg);
                    if (!IsDefEq(pi.BinderType, argType))
                    {
                        throw new MetaException($"AppBuilder for `{constName}`, application type mismatch\n  {arg}\nhas type\n  {this.InstantiateMVars(argType)}\nbut is expected to have type\n  {this.InstantiateMVars(pi.BinderType)}");
                    }
                }
                else
                {
                    var mvar = MkFreshExprMVar(pi.BinderType, pi.BinderInfo == BinderInfo.InstImplicit ? MetavarKind.Synthetic : MetavarKind.Natural, pi.BinderName);
                    if (pi.BinderInfo == BinderInfo.InstImplicit)
                    {
                        instances.Add(mvar);
                    }
                    arg = mvar;
                }
                applied.Add(arg);
                type = ExprOps.Instantiate(pi.Body, arg);
            }
            foreach (var inst in instances)
            {
                if (!IsAssigned(inst.Id))
                {
                    Assign(inst.Id, SynthInstanceOrThrow(this.InstantiateMVars(GetMVarType(inst.Id))));
                }
            }
            var result = this.InstantiateMVars(ExprExtensions.MkAppN(f, applied));
            if (HasAssignableMVar(result))
            {
                throw new MetaException($"AppBuilder for `{constName}`, result contains metavariables\n  {result}");
            }
            return result;
        });
    }

    /// <summary>
    /// Whether <paramref name="e"/>, instantiated, has a metavariable that can be assigned at the current depth (Lean's
    /// <c>hasAssignableMVar</c>).
    /// </summary>
    public bool HasAssignableMVar(Expr e)
    {
        ArgumentNullException.ThrowIfNull(e);
        e = this.InstantiateMVars(e);
        if (!e.HasExprMVar && !e.HasLevelMVar)
        {
            return false;
        }
        bool found = false;
        ExprOps.ForEach(e, (x, _) =>
        {
            if (found || (!x.HasExprMVar && !x.HasLevelMVar))
            {
                return false;
            }
            switch (x)
            {
                case MVarExpr m when !IsReadOnly(m.Id):
                    found = true;
                    return false;
                case ConstExpr c when c.Levels.Any(LevelHasAssignableMVar):
                case SortExpr s when LevelHasAssignableMVar(s.Level):
                    found = true;
                    return false;
                default:
                    return true;
            }
        });
        return found;
    }

    private bool LevelHasAssignableMVar(Level l) => l.Kind switch
    {
        _ when !l.HasMVar => false,
        LevelKind.MVar => !IsReadOnly(l.MVarId!.Value),
        LevelKind.Succ => LevelHasAssignableMVar(l.Lhs!),
        LevelKind.Max or LevelKind.IMax => LevelHasAssignableMVar(l.Lhs!) || LevelHasAssignableMVar(l.Rhs!),
        _ => false,
    };

    /// <summary><c>propext h</c> (Lean's <c>mkPropExt</c>).</summary>
    public Expr MkPropExt(Expr h) => MkAppM(SimpNames.Propext, h);

    /// <summary><c>funext h</c> (Lean's <c>mkFunExt</c>).</summary>
    public Expr MkFunExt(Expr h) => MkAppM(SimpNames.Funext, h);

    /// <summary><c>of_eq_true h</c>, or <c>h'</c> for <c>h = eq_true h'</c> (Lean's <c>mkOfEqTrue</c>).</summary>
    public Expr MkOfEqTrue(Expr h) =>
        ExprOps.IsAppOfArity(h, SimpNames.EqTrue, 2) ? ((AppExpr)h).Arg : MkAppM(SimpNames.OfEqTrue, h);

    /// <summary><c>eq_true h</c>, or <c>h'</c> for <c>h = of_eq_true h'</c> (Lean's <c>mkEqTrue</c>).</summary>
    public Expr MkEqTrue(Expr h) =>
        ExprOps.IsAppOfArity(h, SimpNames.OfEqTrue, 2) ? ((AppExpr)h).Arg : Expr.App(Expr.Const(SimpNames.EqTrue), InferType(h), h);

    /// <summary><c>eq_false h</c> for <c>h : ¬p</c>, or <c>h'</c> for <c>h = of_eq_false h'</c> (Lean's <c>mkEqFalse</c>).</summary>
    public Expr MkEqFalse(Expr h) =>
        ExprOps.IsAppOfArity(h, SimpNames.OfEqFalse, 2) ? ((AppExpr)h).Arg : MkAppM(SimpNames.EqFalse, h);

    /// <summary><c>implies_congr h₁ h₂</c> (Lean's <c>mkImpCongr</c>).</summary>
    public Expr MkImpCongr(Expr h1, Expr h2) => MkAppM(SimpNames.ImpliesCongr, h1, h2);

    /// <summary><c>implies_congr_ctx h₁ h₂</c> (Lean's <c>mkImpCongrCtx</c>).</summary>
    public Expr MkImpCongrCtx(Expr h1, Expr h2) => MkAppM(SimpNames.ImpliesCongrCtx, h1, h2);

    /// <summary><c>implies_dep_congr_ctx h₁ h₂</c> (Lean's <c>mkImpDepCongrCtx</c>).</summary>
    public Expr MkImpDepCongrCtx(Expr h1, Expr h2) => MkAppM(SimpNames.ImpliesDepCongrCtx, h1, h2);

    /// <summary><c>forall_congr h</c> (Lean's <c>mkForallCongr</c>).</summary>
    public Expr MkForallCongr(Expr h) => MkAppM(SimpNames.ForallCongr, h);

    /// <summary>
    /// <c>@Eq.ndrec α a motive h₁ b h₂</c>, or <c>h₁</c> when <c>h₂</c> is reflexivity (Lean's <c>mkEqNDRec</c>).
    /// </summary>
    public Expr MkEqNDRec(Expr motive, Expr h1, Expr h2)
    {
        if (IsRefl(h2))
        {
            return h1;
        }
        var (α, a, b, u2) = EqProofSides(SimpNames.EqNdrec, h2);
        if (WhnfD(InferType(motive)) is not ForallExpr { Body: SortExpr { Level: var u1 } })
        {
            throw new MetaException($"AppBuilder for `Eq.ndrec`, invalid motive\n  {motive}");
        }
        return Expr.App(Expr.Const(SimpNames.EqNdrec, u1, u2), α, a, motive, h1, b, h2);
    }

    /// <summary><c>@Decidable.decide p inst</c> with the instance synthesized (Lean's <c>mkDecide</c>).</summary>
    /// <exception cref="MetaException">There is no instance.</exception>
    public Expr MkDecide(Expr p) =>
        Expr.App(Expr.Const(SimpNames.Decide), p, SynthInstanceOrThrow(Expr.App(Expr.Const(Name.From("Decidable")), p)));
}
