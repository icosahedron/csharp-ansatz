using System.Numerics;
using Warrant.Cic;
using Warrant.Kernel;

namespace Warrant.Meta;

/// <summary>The names Meta's reduction and unification treat specially.</summary>
internal static class MetaNames
{
    public static readonly Name Nat = Name.From("Nat");
    public static readonly Name NatZero = Name.From("Nat", "zero");
    public static readonly Name NatSucc = Name.From("Nat", "succ");
    public static readonly Name NatAdd = Name.From("Nat", "add");
    public static readonly Name NatSub = Name.From("Nat", "sub");
    public static readonly Name NatMul = Name.From("Nat", "mul");
    public static readonly Name NatDiv = Name.From("Nat", "div");
    public static readonly Name NatMod = Name.From("Nat", "mod");
    public static readonly Name NatPow = Name.From("Nat", "pow");
    public static readonly Name NatGcd = Name.From("Nat", "gcd");
    public static readonly Name NatBeq = Name.From("Nat", "beq");
    public static readonly Name NatBle = Name.From("Nat", "ble");
    public static readonly Name NatLand = Name.From("Nat", "land");
    public static readonly Name NatLor = Name.From("Nat", "lor");
    public static readonly Name NatXor = Name.From("Nat", "xor");
    public static readonly Name NatShiftLeft = Name.From("Nat", "shiftLeft");
    public static readonly Name NatShiftRight = Name.From("Nat", "shiftRight");
    public static readonly Name OfNatOfNat = Name.From("OfNat", "ofNat");
    public static readonly Name InstOfNatNat = Name.From("instOfNatNat");
    public static readonly Name HAddHAdd = Name.From("HAdd", "hAdd");
    public static readonly Name InstHAdd = Name.From("instHAdd");
    public static readonly Name InstAddNat = Name.From("instAddNat");
    public static readonly Name BoolTrue = Name.From("Bool", "true");
    public static readonly Name BoolFalse = Name.From("Bool", "false");
    public static readonly Name StringOfList = Name.From("String", "ofList");
    public static readonly Name Dite = Name.From("dite");
    public static readonly Name AccRec = Name.From("Acc", "rec");
    public static readonly Name WellFoundedRec = Name.From("WellFounded", "rec");
    public static readonly Name EqNdrec = Name.From("Eq", "ndrec");
    public static readonly Name EqNdrecSymm = Name.From("Eq", "ndrec_symm");
    public static readonly Name EqNdrecOn = Name.From("Eq", "ndrecOn");
    public static readonly Name OutParam = Name.From("outParam");
    public static readonly Name Inaccessible = Name.From("_inaccessible");
    public static readonly Name PatWithRef = Name.From("_patWithRef");

    public static Expr NatConst { get; } = Expr.Const(Nat);

    /// <summary>Lean's <c>mkNatLit</c>: <c>@OfNat.ofNat Nat n (instOfNatNat n)</c>.</summary>
    public static Expr MkNatLit(BigInteger n)
    {
        var r = Expr.NatLit(n);
        return Expr.App(Expr.Const(OfNatOfNat, Level.Zero), NatConst, r, Expr.App(Expr.Const(InstOfNatNat), r));
    }

    /// <summary>Lean's <c>mkNatSucc</c>.</summary>
    public static Expr MkNatSucc(Expr e) => Expr.App(Expr.Const(NatSucc), e);

    /// <summary>Lean's <c>mkNatAdd</c>: <c>@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) a b</c>.</summary>
    public static Expr MkNatAdd(Expr a, Expr b) =>
        Expr.App(Expr.Const(HAddHAdd, Level.Zero, Level.Zero, Level.Zero), NatConst, NatConst, NatConst, MkInstHAdd(), a, b);

    /// <summary>Lean's <c>Nat.mkInstAdd</c>.</summary>
    public static Expr MkInstAdd() => Expr.Const(InstAddNat);

    /// <summary>Lean's <c>Nat.mkInstHAdd</c>.</summary>
    public static Expr MkInstHAdd() => Expr.App(Expr.Const(InstHAdd, Level.Zero), NatConst, MkInstAdd());

    /// <summary>Lean's <c>toExpr</c> on a <c>Bool</c>.</summary>
    public static Expr MkBool(bool b) => Expr.Const(b ? BoolTrue : BoolFalse);
}

/// <summary>The <c>Lean.Expr</c> and <c>Lean.Level</c> predicates the reduction layer needs.</summary>
internal static class ReduceExprExtensions
{
    /// <summary>Lean's <c>consumeMData</c>.</summary>
    public static Expr ConsumeMData(this Expr e)
    {
        while (e is MDataExpr m)
        {
            e = m.Expr;
        }
        return e;
    }

    /// <summary>Lean's <c>isAppOf</c>: the head is the constant <paramref name="name"/>.</summary>
    public static bool IsAppOf(this Expr e, Name name) => e.GetAppFn() is ConstExpr c && c.Name == name;

    /// <summary>Lean's <c>isConstOf</c>.</summary>
    public static bool IsConstOf(this Expr e, Name name) => e is ConstExpr c && c.Name == name;

    /// <summary>Lean's <c>updateFn</c>: replaces the head of an application spine.</summary>
    public static Expr UpdateFn(this Expr e, Expr newFn) => e is AppExpr a ? Expr.App(a.Fn.UpdateFn(newFn), a.Arg) : newFn;

    /// <summary>Lean's <c>Expr.etaExpanded?</c>: <c>f</c> if <paramref name="e"/> is <c>fun x₁ … xₙ => f x₁ … xₙ</c>.</summary>
    public static Expr? EtaExpanded(this Expr e)
    {
        int n = 0;
        while (e is LamExpr lam)
        {
            e = lam.Body;
            n++;
        }
        int i = 0;
        while (n > 0)
        {
            if (e is AppExpr { Arg: BVarExpr b } app && b.Index == i)
            {
                e = app.Fn;
                n--;
                i++;
            }
            else
            {
                return null;
            }
        }
        return e.HasLooseBVars ? null : e;
    }

    /// <summary>Lean's <c>patternAnnotation?</c>: the term under an <c>inaccessible</c> or <c>patternWithRef</c> annotation.</summary>
    public static Expr? PatternAnnotation(this Expr e) =>
        e is MDataExpr m && m.Data.Entries.Count == 1
        && (m.Data.Entries[0].Key == MetaNames.Inaccessible.ToString() || m.Data.Entries[0].Key == MetaNames.PatWithRef.ToString())
            ? m.Expr
            : null;

    /// <summary>Lean's <c>Level.occurs</c>: <paramref name="u"/> is <paramref name="v"/> or a subterm of it.</summary>
    public static bool Occurs(this Level u, Level v)
    {
        if (u == v)
        {
            return true;
        }
        return v.Kind switch
        {
            LevelKind.Succ => u.Occurs(v.Lhs!),
            LevelKind.Max or LevelKind.IMax => u.Occurs(v.Lhs!) || u.Occurs(v.Rhs!),
            _ => false,
        };
    }

    /// <summary>Whether <paramref name="l"/> is <c>max _ _</c>.</summary>
    public static bool IsMax(this Level l) => l.Kind == LevelKind.Max;

    /// <summary>Whether <paramref name="l"/> is a universe metavariable.</summary>
    public static bool IsMVar(this Level l) => l.Kind == LevelKind.MVar;

    /// <summary>Lean's <c>Level.isNeverZero</c>.</summary>
    public static bool IsNeverZero(this Level l) => LevelOps.IsNotZero(l);

    /// <summary>Lean's <c>RecursorVal.getMajorIdx</c>.</summary>
    public static int GetMajorIdx(this RecursorInfo r) => r.NumParams + r.NumMotives + r.NumMinors + r.NumIndices;

    /// <summary>Lean's <c>RecursorVal.getMajorInduct</c>.</summary>
    public static Name GetMajorInduct(this RecursorInfo r)
    {
        var t = r.Type;
        for (int i = r.GetMajorIdx(); i > 0; i--)
        {
            t = ((ForallExpr)t).Body;
        }
        return ((ConstExpr)((ForallExpr)t).BinderType.GetAppFn()).Name;
    }

    /// <summary>Lean's <c>ConstantInfo.hints</c>.</summary>
    public static ReducibilityHints Hints(this ConstantInfo info) => info is DefinitionInfo d ? d.Hints : ReducibilityHints.Opaque;

    /// <summary>Lean's <c>ReducibilityHints.lt</c>: whether the constant with <paramref name="a"/> should be unfolded first.</summary>
    public static bool HintsLt(this ReducibilityHints a, ReducibilityHints b) => (a.Kind, b.Kind) switch
    {
        (ReducibilityHintsKind.Abbrev, ReducibilityHintsKind.Abbrev) => false,
        (ReducibilityHintsKind.Abbrev, _) => true,
        (ReducibilityHintsKind.Regular, ReducibilityHintsKind.Regular) => a.Height > b.Height,
        (ReducibilityHintsKind.Regular, ReducibilityHintsKind.Opaque) => true,
        _ => false,
    };

    /// <summary>Lean's <c>ReducibilityHints.compare</c>.</summary>
    public static int HintsCompare(this ReducibilityHints a, ReducibilityHints b) => (a.Kind, b.Kind) switch
    {
        (ReducibilityHintsKind.Abbrev, ReducibilityHintsKind.Abbrev) => 0,
        (ReducibilityHintsKind.Abbrev, _) => -1,
        (ReducibilityHintsKind.Regular, ReducibilityHintsKind.Abbrev) => 1,
        (ReducibilityHintsKind.Regular, ReducibilityHintsKind.Regular) => b.Height.CompareTo(a.Height),
        (ReducibilityHintsKind.Regular, ReducibilityHintsKind.Opaque) => -1,
        (ReducibilityHintsKind.Opaque, ReducibilityHintsKind.Opaque) => 0,
        _ => 1,
    };
}

/// <summary>
/// Lean's <c>ProjectionFunctionInfo</c> for a structure projection function such as
/// <c>Prod.fst</c> or the class field <c>HAdd.hAdd</c>.
/// </summary>
/// <param name="CtorName">The structure's constructor.</param>
/// <param name="NumParams">The structure's parameters, which the function takes before the structure.</param>
/// <param name="Index">The field index.</param>
/// <param name="FromClass">Whether the structure is a class.</param>
public sealed record ProjectionFunctionInfo(Name CtorName, int NumParams, int Index, bool FromClass);

/// <summary>Lean's <c>ReduceMatcherResult</c>.</summary>
internal enum ReduceMatcherKind
{
    Reduced,
    Stuck,
    NotMatcher,
    PartialApp,
}

// Weak head normal forms (a port of Lean 4.35.0's Lean/Meta/WHNF.lean). Smart unfolding is not
// ported: Warrant's environments carry no `_sunfold` declarations (the bundle has none and the
// translator emits none), so only its consequence for matchers is kept — a matcher is reduced by
// `reduceMatcher?` in `whnfCore`, never delta-unfolded by `unfoldDefinition?`.
public sealed partial class MetaM
{
    private readonly Dictionary<(ulong, Expr), Expr> _whnfCache = [];
    private readonly Dictionary<Name, ProjectionFunctionInfo?> _projFnInfoCache = [];

    // ---------------------------------------------------------------- helpers

    /// <summary>Lean's <c>Expr.toCtorIfLit</c>: a literal as a constructor application.</summary>
    public Expr ToCtorIfLit(Expr e) => e switch
    {
        NatLitExpr n => n.Value.IsZero ? Expr.Const(MetaNames.NatZero) : Expr.App(Expr.Const(MetaNames.NatSucc), Expr.NatLit(n.Value - 1)),
        StrLitExpr => Whnf(TypeChecker.StringLitToConstructor(e)),
        _ => e,
    };

    /// <summary>
    /// Lean's <c>isAuxRecursor</c>: the auxiliary recursors (<c>casesOn</c>, <c>recOn</c>,
    /// <c>brecOn</c>, <c>binductionOn</c>, <c>below</c> of an inductive type) and <c>Eq.ndrec</c>,
    /// <c>Eq.ndrec_symm</c>, <c>Eq.ndrecOn</c>, which <c>whnfCore</c> unfolds at every transparency.
    /// </summary>
    /// <remarks>
    /// Lean tags these in an environment extension the bundle does not carry; Warrant recognizes
    /// them by name, as definitions <c>I.casesOn</c> etc. of an inductive type <c>I</c>.
    /// </remarks>
    public bool IsAuxRecursor(Name declName)
    {
        ArgumentNullException.ThrowIfNull(declName);
        if (declName == MetaNames.EqNdrec || declName == MetaNames.EqNdrecSymm || declName == MetaNames.EqNdrecOn)
        {
            return true;
        }
        if (declName.Kind != NameKind.Str || declName.Prefix is not { } prefix || Env.Find(prefix) is not InductiveInfo)
        {
            return false;
        }
        var s = declName.StringComponent;
        foreach (var suffix in (ReadOnlySpan<string>)["casesOn", "recOn", "brecOn", "binductionOn", "below"])
        {
            if (s == suffix || s.StartsWith(suffix + "_", StringComparison.Ordinal))
            {
                return true;
            }
        }
        return false;
    }

    private bool IsAuxDef(Name constName) => IsAuxRecursor(constName);

    /// <summary>
    /// Lean's <c>getProjectionFnInfo?</c>. The bundle does not carry Lean's structure extension, so a
    /// projection function is recognized by its value <c>fun params (self : S params) => self.i</c>
    /// over a structure <c>S</c> (one constructor, no indices).
    /// </summary>
    public ProjectionFunctionInfo? GetProjectionFnInfo(Name declName)
    {
        ArgumentNullException.ThrowIfNull(declName);
        if (_projFnInfoCache.TryGetValue(declName, out var cached))
        {
            return cached;
        }
        var info = ComputeProjectionFnInfo(declName);
        _projFnInfoCache[declName] = info;
        return info;
    }

    private ProjectionFunctionInfo? ComputeProjectionFnInfo(Name declName)
    {
        if (Env.Find(declName) is not DefinitionInfo d)
        {
            return null;
        }
        var v = d.Value;
        int n = 0;
        while (v is LamExpr lam)
        {
            v = lam.Body;
            n++;
        }
        v = v.ConsumeMData();
        if (n == 0 || v is not ProjExpr { Struct: BVarExpr { Index: 0 } } p)
        {
            return null;
        }
        if (Env.Find(p.TypeName) is not InductiveInfo { Constructors.Count: 1, NumIndices: 0 } ind
            || Env.Find(ind.Constructors[0]) is not ConstructorInfo ctor
            || ctor.NumParams != n - 1)
        {
            return null;
        }
        return new ProjectionFunctionInfo(ctor.Name, ctor.NumParams, p.Index, Attributes.IsClass(p.TypeName));
    }

    private bool IsProjInst(Name declName) => GetProjectionFnInfo(declName) is { FromClass: true };

    private Name? GetFirstCtor(Name d) =>
        Env.Find(d) is InductiveInfo { Constructors.Count: > 0 } ind ? ind.Constructors[0] : null;

    private Expr? MkNullaryCtor(Expr type, int nparams)
    {
        if (type.GetAppFn() is not ConstExpr d || GetFirstCtor(d.Name) is not { } ctor)
        {
            return null;
        }
        var args = type.GetAppArgs();
        return ExprExtensions.MkAppRange(Expr.Const(ctor, d.Levels), 0, Math.Min(nparams, args.Length), args);
    }

    private static RecursorRule? GetRecRuleFor(RecursorInfo recVal, Expr major)
    {
        if (major.GetAppFn() is not ConstExpr fn)
        {
            return null;
        }
        foreach (var r in recVal.Rules)
        {
            if (r.Constructor == fn.Name)
            {
                return r;
            }
        }
        return null;
    }

    private Expr ToCtorWhenK(RecursorInfo recVal, Expr major)
    {
        var majorType = this.InstantiateMVars(Whnf(InferType(major)));
        if (!majorType.GetAppFn().IsConstOf(recVal.GetMajorInduct()))
        {
            return major;
        }
        if (majorType.HasExprMVar && majorType.GetAppArgs().Skip(recVal.NumParams).Any(a => a.HasExprMVar))
        {
            return major;
        }
        if (MkNullaryCtor(majorType, recVal.NumParams) is not { } newCtorApp)
        {
            return major;
        }
        var newType = InferType(newCtorApp);
        // withNewMCtxDepth: a major premise `h : Eq ?x y` must not get K by assigning ?x := y.
        return WithAtLeastTransparency(TransparencyMode.Default, () => WithNewMCtxDepth(() => IsDefEq(majorType, newType)))
            ? newCtorApp
            : major;
    }

    /// <summary>
    /// The <paramref name="i"/>th projection of <paramref name="major"/>: the projection function
    /// when the structure has one, otherwise <c>Expr.proj</c> (Lean's <c>mkProjFn</c>). Projection
    /// functions are found by the constructor's field names.
    /// </summary>
    private Expr MkProjFn(ConstructorInfo ctorVal, EquatableArray<Level> us, Expr[] @params, int i, Expr major)
    {
        var t = ctorVal.Type;
        for (int k = 0; k < ctorVal.NumParams + i && t is ForallExpr f; k++)
        {
            t = f.Body;
        }
        if (t is ForallExpr field)
        {
            var projName = ctorVal.Inductive + field.BinderName;
            if (GetProjectionFnInfo(projName) is { } info && info.Index == i && info.CtorName == ctorVal.Name)
            {
                return Expr.App(ExprExtensions.MkAppN(Expr.Const(projName, us), @params), major);
            }
        }
        return Expr.Proj(ctorVal.Inductive, i, major);
    }

    /// <summary>Lean's <c>isConstructorApp?</c> (with <c>litToCtor</c> for Nat literals).</summary>
    private ConstructorInfo? IsConstructorAppCore(Expr e)
    {
        e = this.InstantiateMVars(e);
        if (e is NatLitExpr || (e.IsAppOf(MetaNames.OfNatOfNat) && e.GetAppNumArgs() == 3 && e.GetAppArgs() is [ConstExpr { Name: var t }, NatLitExpr, _] && t == MetaNames.Nat))
        {
            return Env.Find(MetaNames.NatSucc) as ConstructorInfo;
        }
        if (e.GetAppFn() is not ConstExpr c || Env.Find(c.Name) is not ConstructorInfo v)
        {
            return null;
        }
        return v.NumParams + v.NumFields == e.GetAppNumArgs() ? v : null;
    }

    /// <summary>Lean's <c>isConstructorApp</c>.</summary>
    public bool IsConstructorApp(Expr e) => IsConstructorAppCore(e) is not null;

    private Expr ToCtorWhenStructure(Name inductName, Expr major)
    {
        if (!UseEtaStruct(inductName) || !IsNonRecStructure(inductName) || IsConstructorAppCore(major) is not null)
        {
            return major;
        }
        var majorType = this.InstantiateMVars(Whnf(InferType(major)));
        if (majorType.GetAppFn() is not ConstExpr d || d.Name != inductName)
        {
            return major;
        }
        if (WhnfD(InferType(majorType)) == Expr.Prop)
        {
            return major; // no eta for propositions, as in the kernel
        }
        if (GetFirstCtor(d.Name) is not { } ctorName || Env.Find(ctorName) is not ConstructorInfo ctorInfo)
        {
            return major;
        }
        var typeArgs = majorType.GetAppArgs();
        var @params = typeArgs.Take(ctorInfo.NumParams).ToArray();
        var result = ExprExtensions.MkAppN(Expr.Const(ctorName, d.Levels), @params);
        for (int i = 0; i < ctorInfo.NumFields; i++)
        {
            result = Expr.App(result, MkProjFn(ctorInfo, d.Levels, @params, i, major));
        }
        return result;
    }

    /// <summary>Lean's <c>isNonRecStructure</c>.</summary>
    public bool IsNonRecStructure(Name constName) =>
        Env.Find(constName) is InductiveInfo { IsRec: false, Constructors.Count: 1, NumIndices: 0 };

    /// <summary>Lean's <c>getNonRecStructureCtor?</c>.</summary>
    private ConstructorInfo? GetNonRecStructureCtor(Name constName) =>
        Env.Find(constName) is InductiveInfo { IsRec: false, Constructors.Count: 1, NumIndices: 0 } ind
            ? Env.Find(ind.Constructors[0]) as ConstructorInfo
            : null;

    // Do not expose Nat.add when reducing Nat.rec (Lean issue #3022).
    private Expr CleanupNatOffsetMajor(Expr e)
    {
        if (IsOffset(e) is not (var s, var k))
        {
            return e;
        }
        if (k.IsZero)
        {
            return s;
        }
        return k.IsOne ? MetaNames.MkNatSucc(s) : MetaNames.MkNatSucc(MetaNames.MkNatAdd(s, MetaNames.MkNatLit(k - 1)));
    }

    private Expr? ReduceRec(RecursorInfo recVal, EquatableArray<Level> recLvls, Expr[] recArgs)
    {
        int majorIdx = recVal.GetMajorIdx();
        if (majorIdx >= recArgs.Length)
        {
            return null;
        }
        var major = recArgs[majorIdx];
        // Acc.rec and WellFounded.rec unfold definitions by well-founded recursion only at `all`.
        major = (recVal.Name == MetaNames.AccRec || recVal.Name == MetaNames.WellFoundedRec) && GetTransparency() == TransparencyMode.Default
            ? WithTransparency(TransparencyMode.All, () => Whnf(major))
            : Whnf(major);
        if (recVal.K)
        {
            major = ToCtorWhenK(recVal, major);
        }
        major = ToCtorIfLit(major);
        major = CleanupNatOffsetMajor(major);
        major = ToCtorWhenStructure(recVal.GetMajorInduct(), major);
        if (GetRecRuleFor(recVal, major) is not { } rule)
        {
            return null;
        }
        var majorArgs = major.GetAppArgs();
        if (recLvls.Count != recVal.LevelParams.Count)
        {
            return null;
        }
        var rhs = ExprOps.InstantiateLevelParams(rule.Rhs, recVal.LevelParams, recLvls);
        rhs = ExprExtensions.MkAppRange(rhs, 0, recVal.NumParams + recVal.NumMotives + recVal.NumMinors, recArgs);
        // A nested inductive's constructor may have more parameters than the recursor.
        int nparams = majorArgs.Length - rule.NumFields;
        if (nparams < 0)
        {
            return null;
        }
        rhs = ExprExtensions.MkAppRange(rhs, nparams, majorArgs.Length, majorArgs);
        return ExprExtensions.MkAppRange(rhs, majorIdx + 1, recArgs.Length, recArgs);
    }

    private Expr? ReduceQuotRec(QuotInfo recVal, Expr[] recArgs)
    {
        int majorPos, argPos;
        switch (recVal.QuotKind)
        {
            case QuotKind.Lift:
                (majorPos, argPos) = (5, 3);
                break;
            case QuotKind.Ind:
                (majorPos, argPos) = (4, 3);
                break;
            default:
                return null;
        }
        if (majorPos >= recArgs.Length)
        {
            return null;
        }
        var major = Whnf(recArgs[majorPos]);
        if (major is not AppExpr { Fn: AppExpr { Fn: AppExpr { Fn: ConstExpr majorFn } } } app
            || Env.Find(majorFn.Name) is not QuotInfo { QuotKind: QuotKind.Ctor })
        {
            return null;
        }
        var r = Expr.App(recArgs[argPos], app.Arg);
        return ExprExtensions.MkAppRange(r, majorPos + 1, recArgs.Length, recArgs);
    }

    // ---------------------------------------------------------------- stuck metavariables

    private MVarId? IsRecStuck(RecursorInfo recVal, Expr[] recArgs)
    {
        if (recVal.K)
        {
            return null;
        }
        int majorIdx = recVal.GetMajorIdx();
        return majorIdx < recArgs.Length ? GetStuckMVar(Whnf(recArgs[majorIdx])) : null;
    }

    private MVarId? IsQuotRecStuck(QuotInfo recVal, Expr[] recArgs)
    {
        int majorPos = recVal.QuotKind switch
        {
            QuotKind.Lift => 5,
            QuotKind.Ind => 4,
            _ => -1,
        };
        return majorPos >= 0 && majorPos < recArgs.Length ? GetStuckMVar(Whnf(recArgs[majorPos])) : null;
    }

    /// <summary>The metavariable blocking the reduction of <paramref name="e"/>, if any (Lean's <c>getStuckMVar?</c>).</summary>
    public MVarId? GetStuckMVar(Expr e)
    {
        ArgumentNullException.ThrowIfNull(e);
        switch (e)
        {
            case MDataExpr m:
                return GetStuckMVar(m.Expr);
            case ProjExpr p:
                return GetStuckMVar(Whnf(p.Struct));
            case MVarExpr:
            {
                var e2 = this.InstantiateMVars(e);
                return e2 is MVarExpr mv ? mv.Id : GetStuckMVar(e2);
            }
            case AppExpr:
            {
                var f = e.GetAppFn();
                switch (f)
                {
                    case MVarExpr:
                    {
                        var e2 = this.InstantiateMVars(e);
                        return e2.GetAppFn() is MVarExpr mv ? mv.Id : GetStuckMVar(e2);
                    }
                    case ConstExpr c:
                        switch (Env.Find(c.Name))
                        {
                            case RecursorInfo recVal:
                                return IsRecStuck(recVal, e.GetAppArgs());
                            case QuotInfo quotVal:
                                return IsQuotRecStuck(quotVal, e.GetAppArgs());
                        }
                        if (!e.HasExprMVar)
                        {
                            return null;
                        }
                        var args = e.GetAppArgs();
                        if (GetProjectionFnInfo(c.Name) is not { } projInfo)
                        {
                            return null;
                        }
                        if (!projInfo.FromClass)
                        {
                            return null;
                        }
                        // A type class projection stuck because its instance is not synthesized yet.
                        if (projInfo.NumParams < args.Length && GetStuckMVar(Whnf(args[projInfo.NumParams])) is { } m1)
                        {
                            return m1;
                        }
                        var info = GetFunInfo(f);
                        for (int i = 0; i < info.ParamInfo.Length && i < args.Length; i++)
                        {
                            if (info.ParamInfo[i].IsExplicit && GetStuckMVar(args[i]) is { } m2)
                            {
                                return m2;
                            }
                        }
                        return null;
                    case ProjExpr p:
                        return GetStuckMVar(Whnf(p.Struct));
                    default:
                        return null;
                }
            }
            default:
                return null;
        }
    }

    // ---------------------------------------------------------------- whnfEasyCases

    /// <summary>Lean's <c>whnfEasyCases</c>: the cases that need no reduction; <paramref name="k"/> handles the rest.</summary>
    private Expr WhnfEasyCases(Expr e, Func<Expr, Expr> k)
    {
        while (true)
        {
            switch (e)
            {
                case ForallExpr or LamExpr or SortExpr or NatLitExpr or StrLitExpr:
                    return e;
                case BVarExpr:
                    throw new MetaException("loose bound variable in expression");
                case LetExpr or ConstExpr or AppExpr or ProjExpr:
                    return k(e);
                case MDataExpr m:
                    e = m.Expr;
                    continue;
                case FVarExpr fv:
                    var decl = GetLocalDecl(fv.Id);
                    if (decl is LDecl { Nondep: false } l)
                    {
                        // Implementation-detail let-variables always unfold.
                        if (!decl.IsImplementationDetail && !Config.ZetaDelta)
                        {
                            return e;
                        }
                        e = l.Value;
                        continue;
                    }
                    return e;
                case MVarExpr mv:
                    if (MCtx.GetExprAssignment(mv.Id) is { } v)
                    {
                        e = v;
                        continue;
                    }
                    return e;
                default:
                    return e;
            }
        }
    }

    private static Expr? DeltaBetaDefinition(ConstantInfo c, EquatableArray<Level> lvls, Expr[] revArgs)
    {
        if (c.LevelParams.Count != lvls.Count)
        {
            return null;
        }
        var val = ExprOps.InstantiateValueLevelParams(c, lvls);
        return val.BetaRev(revArgs);
    }

    // ---------------------------------------------------------------- matchers

    // Eagerly unfold `dite` in a matcher's body (the `match` compiler's auxiliary uses; see the
    // module comment above `unfoldNestedDIte` in WHNF.lean).
    private Expr UnfoldNestedDIte(Expr e)
    {
        if (ExprOps.Find(e, (x, _) => x.IsAppOf(MetaNames.Dite)) is null)
        {
            return e;
        }
        var diteInfo = GetConstInfo(MetaNames.Dite);
        return ExprOps.Replace(e, (x, _) => x is ConstExpr c && c.Name == MetaNames.Dite
            ? ExprOps.InstantiateValueLevelParams(diteInfo, c.Levels)
            : null);
    }

    private Expr WhnfMatcher(Expr e)
    {
        // At reducible, instances and implicit, also unfold the constants canUnfoldAtMatcher allows.
        if (GetTransparency() is TransparencyMode.Reducible or TransparencyMode.Instances or TransparencyMode.Implicit)
        {
            return WithConfig(c => c with { CanUnfoldAtMatcher = true }, () => Whnf(e));
        }
        return Whnf(e);
    }

    /// <summary>
    /// Reduces an application of a compiled <c>match</c> through its matcher info (Lean's
    /// <c>reduceMatcher?</c>).
    /// </summary>
    internal (ReduceMatcherKind Kind, Expr? Value) ReduceMatcher(Expr e)
    {
        e = e.ConsumeMData();
        if (e.GetAppFn() is not ConstExpr fn || GetMatcherInfo(fn.Name) is not { } info)
        {
            return (ReduceMatcherKind.NotMatcher, null);
        }
        var args = e.GetAppArgs();
        int prefixSz = info.NumParams + 1 + info.NumDiscrs;
        if (args.Length < prefixSz + info.NumAlts)
        {
            return (ReduceMatcherKind.PartialApp, null);
        }
        var constInfo = GetConstInfo(fn.Name);
        var f = ExprOps.InstantiateValueLevelParams(constInfo, fn.Levels);
        if (GetTransparency() is TransparencyMode.Reducible or TransparencyMode.Instances or TransparencyMode.Implicit)
        {
            f = UnfoldNestedDIte(f);
        }
        var auxApp = ExprExtensions.MkAppRange(f, 0, prefixSz, args);
        var auxAppType = InferType(auxApp);
        return ForallBoundedTelescope(auxAppType, info.NumAlts, (hs, _) =>
        {
            var reduced = WhnfMatcher(ExprExtensions.MkAppN(auxApp, hs));
            var auxAppFn = reduced.GetAppFn();
            for (int j = 0; j < hs.Length; j++)
            {
                if (auxAppFn.Equals(hs[j]))
                {
                    var result = ExprExtensions.MkAppN(args[prefixSz + j], reduced.GetAppArgs());
                    result = ExprExtensions.MkAppRange(result, prefixSz + info.NumAlts, args.Length, args);
                    return (ReduceMatcherKind.Reduced, (Expr?)result.HeadBeta());
                }
            }
            return (ReduceMatcherKind.Stuck, (Expr?)reduced);
        });
    }

    // ---------------------------------------------------------------- projections

    /// <summary>Field <paramref name="i"/> of a constructor application (Lean's <c>projectCore?</c>).</summary>
    public Expr? ProjectCore(Expr e, int i)
    {
        e = ToCtorIfLit(e);
        if (e.GetAppFn() is not ConstExpr c || Env.Find(c.Name) is not ConstructorInfo ctorVal)
        {
            return null;
        }
        int idx = ctorVal.NumParams + i;
        int numArgs = e.GetAppNumArgs();
        return idx < numArgs ? e.GetAppArgs()[idx] : null;
    }

    /// <summary>Lean's <c>project?</c>.</summary>
    public Expr? Project(Expr e, int i) => ProjectCore(Whnf(e), i);

    /// <summary>Reduces a kernel projection <c>s.i</c> (Lean's <c>reduceProj?</c>).</summary>
    public Expr? ReduceProj(Expr e) => e is ProjExpr p ? Project(p.Struct, p.Index) : null;

    private Expr? WhnfDelayedAssigned(Expr f, Expr e)
    {
        if (f is not MVarExpr mv || MCtx.GetDelayedMVarAssignment(mv.Id) is not { } d)
        {
            return null;
        }
        var args = e.GetAppArgs();
        if (d.FVars.Length > args.Length)
        {
            return null; // not enough arguments to expand the delayed assignment
        }
        var newVal = this.InstantiateMVars(Expr.MVar(d.MVarIdPending));
        if (newVal.HasExprMVar)
        {
            return null; // the pending metavariable is not solved yet
        }
        var result = newVal.Abstract(d.FVars).InstantiateRevRange(0, d.FVars.Length, args);
        return ExprExtensions.MkAppRange(result, d.FVars.Length, args.Length, args);
    }

    // ---------------------------------------------------------------- zeta

    /// <summary>Lean's <c>expandLet</c>: zeta-reduces the <c>let</c>s (and, with <paramref name="zetaHave"/>, <c>have</c>s) at the head.</summary>
    internal static Expr ExpandLet(Expr e, List<Expr> vs, bool zetaHave = true)
    {
        while (e is LetExpr l && (!l.NonDependent || zetaHave))
        {
            vs.Add(l.Value.InstantiateRev(vs));
            e = l.Body;
        }
        return e.InstantiateRev(vs);
    }

    /// <summary>Lean's <c>consumeUnusedLet</c>.</summary>
    internal static Expr ConsumeUnusedLet(Expr e, bool consumeNondep = false)
    {
        while (e is LetExpr l && !l.Body.HasLooseBVars && (!l.NonDependent || consumeNondep))
        {
            e = l.Body;
        }
        return e;
    }

    // ---------------------------------------------------------------- whnfCore

    /// <summary>
    /// Beta, zeta, iota, projection and matcher reduction, expanding assigned metavariables and
    /// auxiliary recursors, but no delta (Lean's <c>whnfCore</c>).
    /// </summary>
    public Expr WhnfCore(Expr e)
    {
        ArgumentNullException.ThrowIfNull(e);
        return WhnfEasyCases(e, WhnfCoreHard);
    }

    private Expr WhnfCoreHard(Expr e)
    {
        Budget.Tick();
        var cfg = Config;
        switch (e)
        {
            case ConstExpr:
                return e;
            case LetExpr l:
                if (cfg.Zeta && (!l.NonDependent || cfg.ZetaHave))
                {
                    return WhnfCore(ExpandLet(l.Body, [l.Value], cfg.ZetaHave));
                }
                if (cfg.ZetaUnused && !l.Body.HasLooseBVars)
                {
                    return WhnfCore(ConsumeUnusedLet(l.Body));
                }
                return e;
            case AppExpr:
            {
                var f = e.GetAppFn();
                var f1 = WhnfCore(f);
                // Beta if enabled, or if the head was reduced to a lambda by this step.
                if (f1 is LamExpr && (cfg.Beta || f is not LamExpr))
                {
                    return WhnfCore(f1.BetaRev(e.GetAppRevArgs()));
                }
                if (WhnfDelayedAssigned(f1, e) is { } eNew)
                {
                    return WhnfCore(eNew);
                }
                var e1 = f.Equals(f1) ? e : e.UpdateFn(f1);
                if (!cfg.Iota)
                {
                    return e1;
                }
                var (kind, reduced) = ReduceMatcher(e1);
                switch (kind)
                {
                    case ReduceMatcherKind.Reduced:
                        return WhnfCore(reduced!);
                    case ReduceMatcherKind.PartialApp:
                    case ReduceMatcherKind.Stuck:
                        return e1;
                }
                if (f1.GetAppFn() is not ConstExpr c || Env.Find(c.Name) is not { } cinfo)
                {
                    return e1;
                }
                switch (cinfo)
                {
                    case RecursorInfo rec:
                        return ReduceRec(rec, c.Levels, e1.GetAppArgs()) is { } r1 ? WhnfCore(r1) : e1;
                    case QuotInfo quot:
                        return ReduceQuotRec(quot, e1.GetAppArgs()) is { } r2 ? WhnfCore(r2) : e1;
                    case DefinitionInfo when IsAuxDef(cinfo.Name):
                        return DeltaBetaDefinition(cinfo, c.Levels, e1.GetAppRevArgs()) is { } r3 ? WhnfCore(r3) : e1;
                    default:
                        return e1;
                }
            }
            case ProjExpr p:
            {
                Expr c;
                switch (cfg.Proj)
                {
                    case ProjReductionKind.No:
                        return e;
                    case ProjReductionKind.Yes:
                        c = WhnfCore(p.Struct);
                        break;
                    case ProjReductionKind.YesWithDelta:
                        c = Whnf(p.Struct);
                        break;
                    default:
                        // At reducible, the structure must not be reduced at instances.
                        c = WhnfAtMostI(p.Struct);
                        break;
                }
                return ProjectCore(c, p.Index) is { } r ? WhnfCore(r) : e;
            }
            default:
                throw new InvalidOperationException("unreachable: whnfEasyCases handles the other kinds");
        }
    }

    // ---------------------------------------------------------------- delta

    /// <summary>
    /// Unfolds a class projection applied to an instance and reduces the instance's projection at
    /// <c>instances</c>, e.g. <c>LE.le Nat instLENat a b</c> to <c>Nat.le a b</c> (Lean's <c>unfoldProjInst?</c>).
    /// </summary>
    public Expr? UnfoldProjInst(Expr e)
    {
        ArgumentNullException.ThrowIfNull(e);
        if (e.GetAppFn() is not ConstExpr c || !IsProjInst(c.Name))
        {
            return null;
        }
        if (WithDefault(() => GetUnfoldableConst(c.Name)) is not { } fInfo)
        {
            return null;
        }
        if (DeltaBetaDefinition(fInfo, c.Levels, e.GetAppRevArgs()) is not { } e1)
        {
            return null;
        }
        if (WithReducibleAndInstances(() => ReduceProj(e1.GetAppFn())) is not { } r)
        {
            return null;
        }
        return ExprExtensions.MkAppN(r, e1.GetAppArgs()).HeadBeta();
    }

    /// <summary>Lean's <c>unfoldProjInstWhenInstances?</c>: <see cref="UnfoldProjInst"/> at <c>instances</c> and <c>implicit</c> only.</summary>
    public Expr? UnfoldProjInstWhenInstances(Expr e) =>
        GetTransparency() is TransparencyMode.Instances or TransparencyMode.Implicit ? UnfoldProjInst(e) : null;

    // Lean's `unfoldDefault`, with `backward.whnf.reducibleClassField` on (its default): unfolding a
    // reducible class field at `reducible` also reduces the instance projection at `instances`.
    private Expr? UnfoldDefault(ConstantInfo fInfo, EquatableArray<Level> us, Expr e)
    {
        if (fInfo.Value is null)
        {
            return null;
        }
        if (DeltaBetaDefinition(fInfo, us, e.GetAppRevArgs()) is not { } e1)
        {
            return null;
        }
        if (GetTransparency() != TransparencyMode.Reducible || !IsProjInst(fInfo.Name))
        {
            return e1;
        }
        if (WithReducibleAndInstances(() => ReduceProj(e1.GetAppFn())) is not { } r)
        {
            return e1;
        }
        return ExprExtensions.MkAppN(r, e1.GetAppArgs()).HeadBeta();
    }

    /// <summary>
    /// Unfolds the definition at the head of <paramref name="e"/> if the transparency allows it (or
    /// regardless, with <paramref name="ignoreTransparency"/>) (Lean's <c>unfoldDefinition?</c>).
    /// Theorems never unfold; matchers reduce only through <see cref="WhnfCore"/>.
    /// </summary>
    public Expr? UnfoldDefinition(Expr e, bool ignoreTransparency = false)
    {
        ArgumentNullException.ThrowIfNull(e);
        switch (e)
        {
            case AppExpr:
            {
                var f = e.GetAppFn();
                ConstantInfo? fInfo = null;
                if (f is ConstExpr fc)
                {
                    fInfo = ignoreTransparency ? Env.Find(fc.Name) : GetUnfoldableConst(fc.Name);
                }
                if (fInfo is null)
                {
                    return UnfoldProjInstWhenInstances(e);
                }
                var fLvls = ((ConstExpr)f).Levels;
                if (fInfo.LevelParams.Count != fLvls.Count)
                {
                    return null;
                }
                // With smart unfolding (Lean's default) and no `_sunfold` declaration, a matcher is
                // left to `reduceMatcher?`.
                if (GetMatcherInfo(fInfo.Name) is not null)
                {
                    return null;
                }
                return UnfoldDefault(fInfo, fLvls, e);
            }
            case ConstExpr c:
            {
                var cinfo = ignoreTransparency ? Env.Find(c.Name) : GetUnfoldableConstNoEx(c.Name);
                if (cinfo?.Value is null || cinfo.LevelParams.Count != c.Levels.Count)
                {
                    return null;
                }
                return ExprOps.InstantiateValueLevelParams(cinfo, c.Levels);
            }
            default:
                return null;
        }
    }

    /// <summary>Like <see cref="UnfoldDefinition"/>, failing if nothing unfolds (Lean's <c>unfoldDefinition</c>).</summary>
    /// <exception cref="MetaException">The head does not unfold.</exception>
    public Expr UnfoldDefinitionOrThrow(Expr e) =>
        UnfoldDefinition(e) ?? throw new MetaException($"failed to unfold definition {e}");

    /// <summary>Lean's <c>whnfHeadPred</c>: <c>whnfCore</c>, then unfold while <paramref name="pred"/> holds.</summary>
    public Expr WhnfHeadPred(Expr e, Func<Expr, bool> pred)
    {
        ArgumentNullException.ThrowIfNull(pred);
        return WhnfEasyCases(e, e1 =>
        {
            var e2 = WhnfCore(e1);
            if (pred(e2) && UnfoldDefinition(e2) is { } e3)
            {
                return WhnfHeadPred(e3, pred);
            }
            return e2;
        });
    }

    /// <summary>Reduces <paramref name="e"/> until its head is <paramref name="declName"/> (Lean's <c>whnfUntil</c>).</summary>
    public Expr? WhnfUntil(Expr e, Name declName)
    {
        var r = WhnfHeadPred(e, x => !x.IsAppOf(declName));
        return r.IsAppOf(declName) ? r : null;
    }

    /// <summary>Reduces a matcher, recursor or quotient application one step (Lean's <c>reduceRecMatcher?</c>).</summary>
    public Expr? ReduceRecMatcher(Expr e)
    {
        e = e.ConsumeMData();
        if (e is not AppExpr)
        {
            return null;
        }
        var (kind, reduced) = ReduceMatcher(e);
        if (kind == ReduceMatcherKind.Reduced)
        {
            return reduced;
        }
        if (e.GetAppFn() is not ConstExpr c || Env.Find(c.Name) is not { } cinfo)
        {
            return null;
        }
        return cinfo switch
        {
            RecursorInfo rec => ReduceRec(rec, c.Levels, e.GetAppArgs()),
            QuotInfo quot => ReduceQuotRec(quot, e.GetAppArgs()),
            DefinitionInfo when IsAuxDef(cinfo.Name) => DeltaBetaDefinition(cinfo, c.Levels, e.GetAppRevArgs()),
            _ => null,
        };
    }

    // ---------------------------------------------------------------- Nat literals

    private BigInteger? WithNatValue(Expr a)
    {
        if (!a.HasExprMVar && a.HasFVar)
        {
            return null;
        }
        a = this.InstantiateMVars(a);
        if (a.HasExprMVar || a.HasFVar)
        {
            return null;
        }
        return Whnf(a) switch
        {
            ConstExpr c when c.Name == MetaNames.NatZero => BigInteger.Zero,
            NatLitExpr n => n.Value,
            _ => null,
        };
    }

    // Lean's `checkExponent` with `exponentiation.threshold` at its default, 256.
    private const int ExponentThreshold = 256;

    /// <summary>
    /// Evaluates <c>Nat.succ</c> and the binary <c>Nat</c> operations on literals (Lean's
    /// <c>reduceNat?</c>), with the kernel's literal semantics.
    /// </summary>
    public Expr? ReduceNat(Expr e)
    {
        ArgumentNullException.ThrowIfNull(e);
        if (e is AppExpr { Fn: ConstExpr f1 } u)
        {
            return f1.Name == MetaNames.NatSucc && WithNatValue(u.Arg) is { } v ? Expr.NatLit(v + 1) : null;
        }
        if (e is not AppExpr { Fn: AppExpr { Fn: ConstExpr f, Arg: var a1 }, Arg: var a2 })
        {
            return null;
        }
        var n = f.Name;
        if (n == MetaNames.NatAdd)
        {
            return Bin(a1, a2, (x, y) => x + y);
        }
        if (n == MetaNames.NatSub)
        {
            return Bin(a1, a2, (x, y) => x > y ? x - y : BigInteger.Zero);
        }
        if (n == MetaNames.NatMul)
        {
            return Bin(a1, a2, (x, y) => x * y);
        }
        if (n == MetaNames.NatDiv)
        {
            return Bin(a1, a2, (x, y) => y.IsZero ? BigInteger.Zero : x / y);
        }
        if (n == MetaNames.NatMod)
        {
            return Bin(a1, a2, (x, y) => y.IsZero ? x : x % y);
        }
        if (n == MetaNames.NatPow)
        {
            if (WithNatValue(a1) is not { } b || WithNatValue(a2) is not { } x || x > ExponentThreshold)
            {
                return null;
            }
            return Expr.NatLit(BigInteger.Pow(b, (int)x));
        }
        if (n == MetaNames.NatGcd)
        {
            return Bin(a1, a2, BigInteger.GreatestCommonDivisor);
        }
        if (n == MetaNames.NatBeq)
        {
            return Pred(a1, a2, (x, y) => x == y);
        }
        if (n == MetaNames.NatBle)
        {
            return Pred(a1, a2, (x, y) => x <= y);
        }
        if (n == MetaNames.NatLand)
        {
            return Bin(a1, a2, (x, y) => x & y);
        }
        if (n == MetaNames.NatLor)
        {
            return Bin(a1, a2, (x, y) => x | y);
        }
        if (n == MetaNames.NatXor)
        {
            return Bin(a1, a2, (x, y) => x ^ y);
        }
        if (n == MetaNames.NatShiftLeft)
        {
            if (WithNatValue(a1) is not { } x || WithNatValue(a2) is not { } y || y > int.MaxValue)
            {
                return null;
            }
            return Expr.NatLit(x << (int)y);
        }
        if (n == MetaNames.NatShiftRight)
        {
            return Bin(a1, a2, (x, y) => y >= int.MaxValue ? BigInteger.Zero : x >> (int)y);
        }
        return null;

        Expr? Bin(Expr a, Expr b, Func<BigInteger, BigInteger, BigInteger> op) =>
            WithNatValue(a) is { } x && WithNatValue(b) is { } y ? Expr.NatLit(op(x, y)) : null;

        Expr? Pred(Expr a, Expr b, Func<BigInteger, BigInteger, bool> op) =>
            WithNatValue(a) is { } x && WithNatValue(b) is { } y ? MetaNames.MkBool(op(x, y)) : null;
    }

    // ---------------------------------------------------------------- whnf

    /// <summary>
    /// The weak head normal form of <paramref name="e"/> at the current transparency (Lean's
    /// <c>whnfImp</c>). Results for terms without free variables or metavariables are cached per
    /// configuration.
    /// </summary>
    public Expr Whnf(Expr e)
    {
        ArgumentNullException.ThrowIfNull(e);
        return WhnfEasyCases(e, e1 =>
        {
            Budget.Tick();
            bool useCache = !e1.HasFVar && !e1.HasExprMVar;
            var key = (Config.Key, e1);
            if (useCache && _whnfCache.TryGetValue(key, out var cached))
            {
                return cached;
            }
            var e2 = WhnfCore(e1);
            Expr r;
            if (ReduceNat(e2) is { } v)
            {
                r = v;
            }
            else if (UnfoldDefinition(e2) is { } e3)
            {
                r = Whnf(e3);
            }
            else
            {
                r = e2;
            }
            if (useCache)
            {
                _whnfCache[key] = r;
            }
            return r;
        });
    }

    /// <summary><see cref="Whnf"/> at <c>reducible</c> (Lean's <c>whnfR</c>).</summary>
    public Expr WhnfR(Expr e) => WithTransparency(TransparencyMode.Reducible, () => Whnf(e));

    /// <summary><see cref="Whnf"/> at <c>default</c> (Lean's <c>whnfD</c>).</summary>
    public Expr WhnfD(Expr e) => WithTransparency(TransparencyMode.Default, () => Whnf(e));

    /// <summary><see cref="Whnf"/> at <c>instances</c> (Lean's <c>whnfI</c>).</summary>
    public Expr WhnfI(Expr e) => WithTransparency(TransparencyMode.Instances, () => Whnf(e));

    /// <summary><see cref="Whnf"/> at a transparency of at most <c>instances</c> (Lean's <c>whnfAtMostI</c>).</summary>
    public Expr WhnfAtMostI(Expr e) =>
        GetTransparency() is TransparencyMode.All or TransparencyMode.Default or TransparencyMode.Implicit
            ? WithTransparency(TransparencyMode.Instances, () => Whnf(e))
            : Whnf(e);
}
