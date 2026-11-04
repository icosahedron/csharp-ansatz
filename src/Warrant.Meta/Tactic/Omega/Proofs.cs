using System.Numerics;
using Warrant.Cic;
using Warrant.Kernel;

namespace Warrant.Meta.Omega;

/// <summary>
/// Every Init constant <c>omega</c> puts into a proof (KTD12, KTD29). The names are those Lean 4.35.0's
/// Lean/Elab/Tactic/Omega/*.lean and FalseOrByContra.lean quote, resolved against Init through each file's open
/// namespaces (so <c>``Int.add_congr</c> in Frontend.lean is <c>Lean.Omega.Int.add_congr</c>), together with the
/// instances <c>mkDecideProof</c> synthesizes, the literals <c>toExpr</c> builds, and Warrant's <c>Int32.toInt</c> and
/// <c>Int64.toInt</c> range lemmas. Each is a root of the semantics bundle (<c>lean/bundle-roots.txt</c>).
/// </summary>
public static class OmegaNames
{
    private static Name N(string s) => Name.Parse(s);

    // Types, literals and logic.
    internal static readonly Name Int = N("Int");
    internal static readonly Name Nat = N("Nat");
    internal static readonly Name Bool = N("Bool");
    internal static readonly Name BoolTrue = N("Bool.true");
    internal static readonly Name False = N("False");
    internal static readonly Name Eq = N("Eq");
    internal static readonly Name EqRefl = N("Eq.refl");
    internal static readonly Name EqSymm = N("Eq.symm");
    internal static readonly Name EqTrans = N("Eq.trans");
    internal static readonly Name Ne = N("Ne");
    internal static readonly Name Not = N("Not");
    internal static readonly Name And = N("And");
    internal static readonly Name Or = N("Or");
    internal static readonly Name Iff = N("Iff");
    internal static readonly Name Exists = N("Exists");
    internal static readonly Name Subtype = N("Subtype");
    internal static readonly Name Id = N("id");
    internal static readonly Name OfNat = N("OfNat.ofNat");
    internal static readonly Name InstOfNatNat = N("instOfNatNat");
    internal static readonly Name InstOfNat = N("instOfNat");
    internal static readonly Name NegNeg = N("Neg.neg");
    internal static readonly Name IntInstNeg = N("Int.instNegInt");
    internal static readonly Name ListCons = N("List.cons");
    internal static readonly Name ListNil = N("List.nil");
    internal static readonly Name OptionSome = N("Option.some");
    internal static readonly Name OptionNone = N("Option.none");
    internal static readonly Name HAdd = N("HAdd.hAdd");
    internal static readonly Name HSub = N("HSub.hSub");
    internal static readonly Name HMul = N("HMul.hMul");
    internal static readonly Name HDiv = N("HDiv.hDiv");
    internal static readonly Name HMod = N("HMod.hMod");
    internal static readonly Name HPow = N("HPow.hPow");
    internal static readonly Name InstHDiv = N("instHDiv");
    internal static readonly Name IntInstDiv = N("Int.instDiv");
    internal static readonly Name LE = N("LE.le");
    internal static readonly Name LT = N("LT.lt");
    internal static readonly Name GE = N("GE.ge");
    internal static readonly Name GT = N("GT.gt");
    internal static readonly Name Dvd = N("Dvd.dvd");
    internal static readonly Name Min = N("Min.min");
    internal static readonly Name Max = N("Max.max");
    internal static readonly Name NatCast = N("Nat.cast");
    internal static readonly Name NatSucc = N("Nat.succ");
    internal static readonly Name IntToNat = N("Int.toNat");
    internal static readonly Name IntNatAbs = N("Int.natAbs");
    internal static readonly Name IntNegSucc = N("Int.negSucc");
    internal static readonly Name Ite = N("ite");
    internal static readonly Name InstLENat = N("instLENat");
    internal static readonly Name InstLTNat = N("instLTNat");
    internal static readonly Name IntInstLT = N("Int.instLTInt");
    internal static readonly Name OrElim = N("Or.elim");
    internal static readonly Name AndLeft = N("And.left");
    internal static readonly Name AndRight = N("And.right");
    internal static readonly Name ExistsChooseSpec = N("Exists.choose_spec");
    internal static readonly Name SubtypeProperty = N("Subtype.property");
    internal static readonly Name ClassicalPropDecidable = N("Classical.propDecidable");
    internal static readonly Name LeOfLeOfEq = N("le_of_le_of_eq");

    // Decidability, for decide proofs (mkDecideProof's instances) and FalseOrByContra.
    internal static readonly Name DecidableDecide = N("Decidable.decide");
    internal static readonly Name OfDecideEqTrue = N("of_decide_eq_true");
    internal static readonly Name Decidable = N("Decidable");
    internal static readonly Name NatDecLe = N("Nat.decLe");
    internal static readonly Name NatDecLt = N("Nat.decLt");
    internal static readonly Name IntDecLt = N("Int.decLt");
    internal static readonly Name IntInstDecidableEq = N("Int.instDecidableEq");
    internal static readonly Name InstDecidableNot = N("instDecidableNot");
    internal static readonly Name InstDecidableOr = N("instDecidableOr");
    internal static readonly Name InstDecidableEqBool = N("instDecidableEqBool");
    internal static readonly Name ListDecidableBAll = N("List.decidableBAll");
    internal static readonly Name DecidableByContradiction = N("Decidable.byContradiction");
    internal static readonly Name ClassicalByContradiction = N("Classical.byContradiction");
    internal static readonly Name FalseElim = N("False.elim");

    // Lean.Omega data and its soundness lemmas (Init/Omega).
    internal static readonly Name CoeffsOfList = N("Lean.Omega.Coeffs.ofList");
    internal static readonly Name CoeffsGet = N("Lean.Omega.Coeffs.get");
    internal static readonly Name CoeffsLength = N("Lean.Omega.Coeffs.length");
    internal static readonly Name CoeffsIsZero = N("Lean.Omega.Coeffs.isZero");
    internal static readonly Name ConstraintMk = N("Lean.Omega.Constraint.mk");
    internal static readonly Name ConstraintIsImpossible = N("Lean.Omega.Constraint.isImpossible");
    internal static readonly Name ConstraintCombineSat = N("Lean.Omega.Constraint.combine_sat'");
    internal static readonly Name ConstraintNotSatOfIsImpossible = N("Lean.Omega.Constraint.not_sat'_of_isImpossible");
    internal static readonly Name ConstraintAddInequalitySat = N("Lean.Omega.Constraint.addInequality_sat");
    internal static readonly Name ConstraintAddEqualitySat = N("Lean.Omega.Constraint.addEquality_sat");
    internal static readonly Name TidySat = N("Lean.Omega.tidy_sat");
    internal static readonly Name ComboSat = N("Lean.Omega.combo_sat'");
    internal static readonly Name BmodSat = N("Lean.Omega.bmod_sat");
    internal static readonly Name BmodDivTerm = N("Lean.Omega.bmod_div_term");
    internal static readonly Name LinearComboMk = N("Lean.Omega.LinearCombo.mk");
    internal static readonly Name LinearComboEval = N("Lean.Omega.LinearCombo.eval");
    internal static readonly Name LinearComboAddEval = N("Lean.Omega.LinearCombo.add_eval");
    internal static readonly Name LinearComboSubEval = N("Lean.Omega.LinearCombo.sub_eval");
    internal static readonly Name LinearComboNegEval = N("Lean.Omega.LinearCombo.neg_eval");
    internal static readonly Name LinearComboMulEval = N("Lean.Omega.LinearCombo.mul_eval");
    internal static readonly Name LinearComboCoordinateEval = N("Lean.Omega.LinearCombo.coordinate_eval");
    internal static readonly Name IteDisjunction = N("Lean.Omega.ite_disjunction");

    // asLinearCombo's congruences and rewrites.
    internal static readonly Name IntAddCongr = N("Lean.Omega.Int.add_congr");
    internal static readonly Name IntSubCongr = N("Lean.Omega.Int.sub_congr");
    internal static readonly Name IntNegCongr = N("Lean.Omega.Int.neg_congr");
    internal static readonly Name IntMulCongr = N("Lean.Omega.Int.mul_congr");
    internal static readonly Name IntEmodDef = N("Int.emod_def");
    internal static readonly Name IntEdivZero = N("Int.ediv_zero");
    internal static readonly Name IntEdivNeg = N("Int.ediv_neg");
    internal static readonly Name IntMinDef = N("Int.min_def");
    internal static readonly Name IntMaxDef = N("Int.max_def");
    internal static readonly Name IntPowSucc = N("Int.pow_succ");
    internal static readonly Name IntNegSuccEq = N("Int.negSucc_eq");
    internal static readonly Name IntNatCastSucc = N("Int.natCast_succ");
    internal static readonly Name IntNatCastAdd = N("Int.natCast_add");
    internal static readonly Name IntNatCastMul = N("Int.natCast_mul");
    internal static readonly Name IntNatCastEdiv = N("Int.natCast_ediv");
    internal static readonly Name IntNatCastEmod = N("Int.natCast_emod");
    internal static readonly Name IntNatCastOfNat = N("Lean.Omega.Int.natCast_ofNat");
    internal static readonly Name IntOfNatMulNonneg = N("Lean.Omega.Int.ofNat_mul_nonneg");
    internal static readonly Name IntOfNatSubSub = N("Lean.Omega.Int.ofNat_sub_sub");
    internal static readonly Name IntOfNatPow = N("Lean.Omega.Int.ofNat_pow");
    internal static readonly Name IntOfNatMin = N("Lean.Omega.Int.ofNat_min");
    internal static readonly Name IntOfNatMax = N("Lean.Omega.Int.ofNat_max");
    internal static readonly Name IntToNatEqMax = N("Int.toNat_eq_max");
    internal static readonly Name IntOfNatNatAbs = N("Lean.Omega.Int.ofNat_natAbs");

    // analyzeAtom's facts.
    internal static readonly Name IntNatCastNonneg = N("Int.natCast_nonneg");
    internal static readonly Name IntOfNatSubDichotomy = N("Lean.Omega.Int.ofNat_sub_dichotomy");
    internal static readonly Name IntLeNatAbs = N("Int.le_natAbs");
    internal static readonly Name IntNegLeNatAbs = N("Lean.Omega.Int.neg_le_natAbs");
    internal static readonly Name IntMulEdivSelfLe = N("Int.mul_ediv_self_le");
    internal static readonly Name IntLtMulEdivSelfAdd = N("Int.lt_mul_ediv_self_add");
    internal static readonly Name IntPosPowOfPos = N("Lean.Omega.Int.pos_pow_of_pos");
    internal static readonly Name IntEmodNonneg = N("Int.emod_nonneg");
    internal static readonly Name IntNeOfGt = N("Int.ne_of_gt");
    internal static readonly Name IntEmodLtOfPos = N("Int.emod_lt_of_pos");
    internal static readonly Name NatPowPos = N("Nat.pow_pos");
    internal static readonly Name IntOfNatPosOfPos = N("Lean.Omega.Int.ofNat_pos_of_pos");
    internal static readonly Name IntEmodOfNatNonneg = N("Lean.Omega.Int.emod_ofNat_nonneg");
    internal static readonly Name IntMinLeLeft = N("Int.min_le_left");
    internal static readonly Name IntMinLeRight = N("Int.min_le_right");
    internal static readonly Name IntLeMaxLeft = N("Int.le_max_left");
    internal static readonly Name IntLeMaxRight = N("Int.le_max_right");

    // Warrant's atom rule (KTD12): the range of Int32.toInt and Int64.toInt.
    internal static readonly Name Int32ToInt = N("Int32.toInt");
    internal static readonly Name Int32LeToInt = N("Int32.le_toInt");
    internal static readonly Name Int32ToIntLt = N("Int32.toInt_lt");
    internal static readonly Name Int64ToInt = N("Int64.toInt");
    internal static readonly Name Int64LeToInt = N("Int64.le_toInt");
    internal static readonly Name Int64ToIntLt = N("Int64.toInt_lt");

    // addFact and pushNot.
    internal static readonly Name DecidableNotOrOfImp = N("Decidable.not_or_of_imp");
    internal static readonly Name DecidableAndNotOfNotImp = N("Lean.Omega.Decidable.and_not_of_not_imp");
    internal static readonly Name DecidableOfNotNot = N("Decidable.of_not_not");
    internal static readonly Name DecidableOrNotNotOfNotAnd = N("Lean.Omega.Decidable.or_not_not_of_not_and");
    internal static readonly Name AndNotNotOfNotOr = N("Lean.Omega.and_not_not_of_not_or");
    internal static readonly Name DecidableAndNotOrNotAndOfNotIff = N("Lean.Omega.Decidable.and_not_or_not_and_of_not_iff");
    internal static readonly Name DecidableAndOrNotAndNotOfIff = N("Lean.Omega.Decidable.and_or_not_and_not_of_iff");
    internal static readonly Name IntSubEqZeroOfEq = N("Int.sub_eq_zero_of_eq");
    internal static readonly Name IntOfNatCongr = N("Lean.Omega.Int.ofNat_congr");
    internal static readonly Name IntSubNonnegOfLe = N("Int.sub_nonneg_of_le");
    internal static readonly Name IntOfNatLeOfLe = N("Lean.Omega.Int.ofNat_le_of_le");
    internal static readonly Name IntAddOneLeOfLt = N("Int.add_one_le_of_lt");
    internal static readonly Name IntOfNatLtOfLt = N("Lean.Omega.Int.ofNat_lt_of_lt");
    internal static readonly Name IntLtOfGt = N("Lean.Omega.Int.lt_of_gt");
    internal static readonly Name NatLtOfGt = N("Lean.Omega.Nat.lt_of_gt");
    internal static readonly Name IntLeOfGe = N("Lean.Omega.Int.le_of_ge");
    internal static readonly Name NatLeOfGe = N("Lean.Omega.Nat.le_of_ge");
    internal static readonly Name IntLtOrGtOfNe = N("Int.lt_or_gt_of_ne");
    internal static readonly Name NatLtOrGtOfNe = N("Nat.lt_or_gt_of_ne");
    internal static readonly Name IntEmodEqZeroOfDvd = N("Int.emod_eq_zero_of_dvd");
    internal static readonly Name NatModEqZeroOfDvd = N("Nat.mod_eq_zero_of_dvd");
    internal static readonly Name NatLeOfNotLt = N("Nat.le_of_not_lt");
    internal static readonly Name IntLeOfNotLt = N("Lean.Omega.Int.le_of_not_lt");
    internal static readonly Name NatLtOfNotLe = N("Nat.lt_of_not_le");
    internal static readonly Name IntLtOfNotLe = N("Lean.Omega.Int.lt_of_not_le");
    internal static readonly Name NatEmodPosOfNotDvd = N("Nat.emod_pos_of_not_dvd");
    internal static readonly Name IntEmodPosOfNotDvd = N("Int.emod_pos_of_not_dvd");

    /// <summary>
    /// <c>Lean.Omega.LinearCombo.coordinate_eval_n</c> for <c>n &lt; 10</c>. These are not bundle roots: the bundle has
    /// those Init's own proofs depend on (not <c>coordinate_eval_6</c>), and <c>omega</c> uses one only when the bundle
    /// has it, else the general <c>coordinate_eval</c>, as Lean does from the tenth atom on.
    /// </summary>
    internal static Name CoordinateEval(int n) => N($"Lean.Omega.LinearCombo.coordinate_eval_{n}");

    /// <summary>The constants above, for the bundle check (KTD29).</summary>
    public static IReadOnlyList<Name> All { get; } =
    [
        .. typeof(OmegaNames).GetFields(System.Reflection.BindingFlags.Static | System.Reflection.BindingFlags.NonPublic)
            .Where(f => f.FieldType == typeof(Name))
            .Select(f => (Name)f.GetValue(null)!),
    ];
}

/// <summary>
/// The terms <c>omega</c>'s proofs are made of: Lean's <c>toExpr</c> for the reflected data (Lean/ToExpr.lean and
/// Omega/Core.lean 22-31), and the <c>AppBuilder</c> functions it calls (<c>mkEqSymm</c>, <c>mkEqTrans</c>,
/// <c>mkDecideProof</c>, <c>mkAppM</c>, Lean/Meta/AppBuilder.lean).
/// </summary>
internal static class OmegaExprs
{
    public static readonly Expr IntType = Expr.Const(OmegaNames.Int);
    public static readonly Expr NatType = Expr.Const(OmegaNames.Nat);
    public static readonly Expr BoolTrue = Expr.Const(OmegaNames.BoolTrue);
    public static readonly Expr False = Expr.Const(OmegaNames.False);

    /// <summary><c>mkNatLit n</c>: <c>@OfNat.ofNat Nat n (instOfNatNat n)</c>.</summary>
    public static Expr NatLit(BigInteger n)
    {
        var r = Expr.NatLit(n);
        return Expr.App(Expr.Const(OmegaNames.OfNat, Level.Zero), NatType, r, Expr.App(Expr.Const(OmegaNames.InstOfNatNat), r));
    }

    /// <summary><c>toExpr (i : Int)</c>: <c>@OfNat.ofNat Int n (@instOfNat n)</c>, under <c>Neg.neg</c> when negative.</summary>
    public static Expr IntLit(BigInteger i)
    {
        if (i.Sign >= 0)
        {
            return NonNeg(i);
        }
        return Expr.App(Expr.Const(OmegaNames.NegNeg, Level.Zero), IntType, Expr.Const(OmegaNames.IntInstNeg), NonNeg(-i));

        static Expr NonNeg(BigInteger n)
        {
            var r = Expr.NatLit(n);
            return Expr.App(Expr.Const(OmegaNames.OfNat, Level.Zero), IntType, r, Expr.App(Expr.Const(OmegaNames.InstOfNat), r));
        }
    }

    /// <summary><c>toExpr</c> of a <c>List Int</c> of terms.</summary>
    public static Expr IntList(IEnumerable<Expr> items)
    {
        var list = items.ToList();
        Expr result = Expr.App(Expr.Const(OmegaNames.ListNil, Level.Zero), IntType);
        for (int i = list.Count - 1; i >= 0; i--)
        {
            result = Expr.App(Expr.Const(OmegaNames.ListCons, Level.Zero), IntType, list[i], result);
        }
        return result;
    }

    /// <summary><c>toExpr</c> of coefficients: a list literal.</summary>
    public static Expr ToExpr(Coeffs x) => IntList(x.Values.Select(IntLit));

    /// <summary><c>toExpr</c> of an <c>Option Int</c>.</summary>
    public static Expr ToExpr(BigInteger? o) => o is { } v
        ? Expr.App(Expr.Const(OmegaNames.OptionSome, Level.Zero), IntType, IntLit(v))
        : Expr.App(Expr.Const(OmegaNames.OptionNone, Level.Zero), IntType);

    /// <summary><c>toExpr</c> of a constraint: <c>Constraint.mk lower upper</c>.</summary>
    public static Expr ToExpr(Constraint s) => Expr.App(Expr.Const(OmegaNames.ConstraintMk), ToExpr(s.Lower), ToExpr(s.Upper));

    /// <summary><c>toExpr</c> of a linear combination: <c>LinearCombo.mk const coeffs</c>.</summary>
    public static Expr ToExpr(LinearCombo lc) => Expr.App(Expr.Const(OmegaNames.LinearComboMk), IntLit(lc.Const), ToExpr(lc.Coeffs));

    /// <summary><c>@Eq.{1} type a b</c>; every type <c>omega</c> states an equation at is in <c>Type</c>.</summary>
    public static Expr MkEq(Expr type, Expr a, Expr b) => Expr.App(Expr.Const(OmegaNames.Eq, Level.One), type, a, b);

    /// <summary><c>@LE.le Nat instLENat a b</c>.</summary>
    public static Expr NatLe(Expr a, Expr b) => Expr.App(Expr.Const(OmegaNames.LE, Level.Zero), NatType, Expr.Const(OmegaNames.InstLENat), a, b);

    /// <summary><c>@LT.lt Int Int.instLTInt a b</c>.</summary>
    public static Expr IntLt(Expr a, Expr b) => Expr.App(Expr.Const(OmegaNames.LT, Level.Zero), IntType, Expr.Const(OmegaNames.IntInstLT), a, b);

    /// <summary><c>@LT.lt Nat instLTNat a b</c>.</summary>
    public static Expr NatLt(Expr a, Expr b) => Expr.App(Expr.Const(OmegaNames.LT, Level.Zero), NatType, Expr.Const(OmegaNames.InstLTNat), a, b);

    /// <summary><c>@Ne.{1} Int a b</c>.</summary>
    public static Expr IntNe(Expr a, Expr b) => Expr.App(Expr.Const(OmegaNames.Ne, Level.One), IntType, a, b);

    /// <summary><c>@HDiv.hDiv Int Int Int (@instHDiv Int Int.instDiv) a b</c>, as <c>mkAppM ``HDiv.hDiv</c> builds it.</summary>
    public static Expr IntDiv(Expr a, Expr b) =>
        Expr.App(Expr.Const(OmegaNames.HDiv, Level.Zero, Level.Zero, Level.Zero), IntType, IntType, IntType,
            Expr.App(Expr.Const(OmegaNames.InstHDiv, Level.Zero), IntType, Expr.Const(OmegaNames.IntInstDiv)), a, b);

    /// <summary><c>Classical.propDecidable p</c>.</summary>
    public static Expr PropDecidable(Expr p) => Expr.App(Expr.Const(OmegaNames.ClassicalPropDecidable), p);

    /// <summary>Lean's <c>Expr.nat?</c>: <c>OfNat.ofNat _ n _</c> with a raw literal <c>n</c>.</summary>
    public static BigInteger? Nat(Expr e) =>
        e.GetAppFn() is ConstExpr { Name: var n } && n == OmegaNames.OfNat && e.GetAppNumArgs() == 3 && e.GetAppArgs()[1] is NatLitExpr lit
            ? lit.Value
            : null;

    /// <summary>Lean's <c>Expr.int?</c>: a <see cref="Nat"/> numeral, or <c>Neg.neg</c> of a positive one.</summary>
    public static BigInteger? Int(Expr e)
    {
        if (e.GetAppFn() is ConstExpr { Name: var n } && n == OmegaNames.NegNeg && e.GetAppNumArgs() == 3)
        {
            return Nat(e.GetAppArgs()[2]) is { } v && !v.IsZero ? -v : null;
        }
        return Nat(e);
    }

    /// <summary><c>e.getAppFnArgs</c> when the head is a constant named <paramref name="name"/> applied to exactly
    /// <paramref name="arity"/> arguments; null otherwise.</summary>
    public static Expr[]? AppOf(Expr e, Name name, int arity) =>
        e.GetAppFn() is ConstExpr c && c.Name == name && e.GetAppNumArgs() == arity ? e.GetAppArgs() : null;

    /// <summary>Whether <paramref name="e"/> is an application of the constant <paramref name="name"/> (Lean's <c>isAppOf</c>).</summary>
    public static bool IsAppOf(Expr e, Name name) => e.GetAppFn() is ConstExpr c && c.Name == name;
}

/// <summary>The <c>AppBuilder</c> functions <c>omega</c> uses, over a <see cref="MetaM"/>.</summary>
internal static class OmegaAppBuilder
{
    /// <summary><c>mkExpectedPropHint proof p</c>: <c>@id.{0} p proof</c>.</summary>
    public static Expr MkExpectedPropHint(Expr proof, Expr p) => Expr.App(Expr.Const(OmegaNames.Id, Level.Zero), p, proof);

    /// <summary><c>mkEqRefl a</c> at a type in <c>Type</c>: <c>@Eq.refl.{1} type a</c>.</summary>
    public static Expr MkEqRefl(Expr type, Expr a) => Expr.App(Expr.Const(OmegaNames.EqRefl, Level.One), type, a);

    /// <summary><c>mkEqReflWithExpectedType a b</c> (OmegaM.lean 159): <c>(Eq.refl a : a = b)</c>.</summary>
    public static Expr MkEqReflWithExpectedType(MetaM m, Expr a, Expr b)
    {
        var type = m.InferType(a);
        return MkExpectedPropHint(MkEqRefl(type, a), OmegaExprs.MkEq(type, a, b));
    }

    /// <summary>The <c>(α, a, b)</c> and universe of an equation's type, inferred as AppBuilder's <c>infer</c> does.</summary>
    private static (Level U, Expr Type, Expr Lhs, Expr Rhs) EqOf(MetaM m, Expr h, string fn)
    {
        var type = m.InstantiateMVars(m.InferType(h));
        if (OmegaExprs.AppOf(type, OmegaNames.Eq, 3) is null)
        {
            type = m.WhnfD(type);
        }
        if (OmegaExprs.AppOf(type, OmegaNames.Eq, 3) is not { } args)
        {
            throw new MetaException($"AppBuilder for '{fn}', equality proof expected\n  {m.Pp(h)}\nhas type\n  {m.Pp(type)}");
        }
        var u = ((ConstExpr)type.GetAppFn()).Levels[0];
        return (u, args[0], args[1], args[2]);
    }

    /// <summary><c>mkEqSymm h</c>: <c>h</c> itself when it is <c>Eq.refl</c>.</summary>
    public static Expr MkEqSymm(MetaM m, Expr h)
    {
        if (OmegaExprs.IsAppOf(h, OmegaNames.EqRefl))
        {
            return h;
        }
        var (u, type, a, b) = EqOf(m, h, "Eq.symm");
        return Expr.App(Expr.Const(OmegaNames.EqSymm, u), type, a, b, h);
    }

    /// <summary><c>mkEqTrans h₁ h₂</c>: drops a side that is <c>Eq.refl</c>.</summary>
    public static Expr MkEqTrans(MetaM m, Expr h1, Expr h2)
    {
        if (OmegaExprs.IsAppOf(h1, OmegaNames.EqRefl))
        {
            return h2;
        }
        if (OmegaExprs.IsAppOf(h2, OmegaNames.EqRefl))
        {
            return h1;
        }
        var (u, type, a, b) = EqOf(m, h1, "Eq.trans");
        var (_, _, _, c) = EqOf(m, h2, "Eq.trans");
        return Expr.App(Expr.Const(OmegaNames.EqTrans, u), type, a, b, c, h1, h2);
    }

    /// <summary>
    /// <c>mkAppM c args</c>: applies the constant to the explicit <paramref name="args"/>, finding the implicit arguments
    /// by unifying the explicit arguments' types with the binders', and instance arguments by unification or else by
    /// instance synthesis.
    /// </summary>
    public static Expr MkAppM(MetaM m, Name c, params Expr[] args)
    {
        var f = m.MkConstWithFreshMVarLevels(c);
        var type = m.InferType(f);
        var applied = new List<Expr>();
        var instMVars = new List<MVarExpr>();
        int next = 0;
        while (true)
        {
            if (type is not ForallExpr)
            {
                type = m.WhnfD(type);
            }
            if (type is not ForallExpr pi || (pi.BinderInfo == BinderInfo.Default && next == args.Length))
            {
                break;
            }
            Expr arg;
            if (pi.BinderInfo == BinderInfo.Default)
            {
                arg = args[next++];
                var argType = m.InferType(arg);
                if (!m.IsDefEq(pi.BinderType, argType))
                {
                    throw new MetaException($"AppBuilder for '{c}', application type mismatch\n  {m.Pp(arg)}\nhas type\n  {m.Pp(argType)}\nbut is expected to have type\n  {m.Pp(pi.BinderType)}");
                }
            }
            else
            {
                var mvar = m.MkFreshExprMVar(pi.BinderType, pi.BinderInfo == BinderInfo.InstImplicit ? MetavarKind.Synthetic : MetavarKind.Natural);
                if (pi.BinderInfo == BinderInfo.InstImplicit)
                {
                    instMVars.Add(mvar);
                }
                arg = mvar;
            }
            applied.Add(arg);
            type = ExprOps.Instantiate(pi.Body, arg);
        }
        if (next != args.Length)
        {
            throw new MetaException($"AppBuilder for '{c}', too many explicit arguments");
        }
        foreach (var inst in instMVars)
        {
            if (!m.MCtx.IsAssigned(inst.Id))
            {
                var instType = m.InstantiateMVars(m.GetMVarType(inst.Id));
                var val = m.SynthInstance(instType) ?? throw new MetaException($"AppBuilder for '{c}', failed to synthesize\n  {m.Pp(instType)}");
                if (!m.IsDefEq(inst, val))
                {
                    throw new MetaException($"AppBuilder for '{c}', failed to assign the instance\n  {m.Pp(instType)}");
                }
            }
        }
        var result = m.InstantiateMVars(ExprExtensions.MkAppN(f, applied));
        if (result.HasExprMVar || result.HasLevelMVar)
        {
            throw new MetaException($"AppBuilder for '{c}', result contains metavariables\n  {m.Pp(result)}");
        }
        return result;
    }

    /// <summary>
    /// <c>mkDecideProof p</c>: <c>of_decide_eq_true (Eq.refl true : decide p = true)</c>. The instance is the one Lean
    /// synthesizes for each proposition <c>omega</c> decides; any other is looked up by instance synthesis.
    /// </summary>
    public static Expr MkDecideProof(MetaM m, Expr p)
    {
        var inst = DecidableInstance(p) ?? m.SynthInstance(Expr.App(Expr.Const(OmegaNames.Decidable), p))
            ?? throw new MetaException($"failed to synthesize\n  Decidable ({m.Pp(p)})");
        var decide = Expr.App(Expr.Const(OmegaNames.DecidableDecide), p, inst);
        var h = MkExpectedPropHint(MkEqRefl(Expr.Const(OmegaNames.Bool), OmegaExprs.BoolTrue), OmegaExprs.MkEq(Expr.Const(OmegaNames.Bool), decide, OmegaExprs.BoolTrue));
        return Expr.App(Expr.Const(OmegaNames.OfDecideEqTrue), p, inst, h);
    }

    /// <summary>The instances Lean 4.35.0 synthesizes for the propositions <c>omega</c> decides.</summary>
    private static Expr? DecidableInstance(Expr p)
    {
        if (OmegaExprs.AppOf(p, OmegaNames.LE, 4) is { } le && le[0] == OmegaExprs.NatType)
        {
            return Expr.App(Expr.Const(OmegaNames.NatDecLe), le[2], le[3]);
        }
        if (OmegaExprs.AppOf(p, OmegaNames.LT, 4) is { } lt)
        {
            if (lt[0] == OmegaExprs.NatType)
            {
                return Expr.App(Expr.Const(OmegaNames.NatDecLt), lt[2], lt[3]);
            }
            if (lt[0] == OmegaExprs.IntType)
            {
                return Expr.App(Expr.Const(OmegaNames.IntDecLt), lt[2], lt[3]);
            }
        }
        if (OmegaExprs.AppOf(p, OmegaNames.Ne, 3) is { } ne && ne[0] == OmegaExprs.IntType)
        {
            return Expr.App(Expr.Const(OmegaNames.InstDecidableNot), OmegaExprs.MkEq(OmegaExprs.IntType, ne[1], ne[2]),
                Expr.App(Expr.Const(OmegaNames.IntInstDecidableEq), ne[1], ne[2]));
        }
        if (OmegaExprs.AppOf(p, OmegaNames.Eq, 3) is { } eq && eq[0] == Expr.Const(OmegaNames.Bool))
        {
            return Expr.App(Expr.Const(OmegaNames.InstDecidableEqBool), eq[1], eq[2]);
        }
        if (OmegaExprs.AppOf(p, OmegaNames.Or, 2) is { } or
            && OmegaExprs.AppOf(or[0], OmegaNames.CoeffsIsZero, 1) is { } x
            && OmegaExprs.AppOf(or[1], OmegaNames.CoeffsIsZero, 1) is { } y)
        {
            return Expr.App(Expr.Const(OmegaNames.InstDecidableOr), or[0], or[1], AllZero(x[0]), AllZero(y[0]));
        }
        return null;

        // @List.decidableBAll Int (fun x => x = 0) (fun a => Int.instDecidableEq a 0) xs
        static Expr AllZero(Expr xs)
        {
            var zero = OmegaExprs.IntLit(0);
            var pred = Expr.Lam(Name.From("x"), OmegaExprs.IntType, OmegaExprs.MkEq(OmegaExprs.IntType, Expr.BVar(0), zero));
            var dec = Expr.Lam(Name.From("a"), OmegaExprs.IntType, Expr.App(Expr.Const(OmegaNames.IntInstDecidableEq), Expr.BVar(0), zero));
            return Expr.App(Expr.Const(OmegaNames.ListDecidableBAll, Level.Zero), OmegaExprs.IntType, pred, dec, xs);
        }
    }
}
