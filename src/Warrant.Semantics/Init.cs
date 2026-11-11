using Warrant.Cic;

namespace Warrant.Semantics;

/// <summary>
/// The Init constants translation emits, with the universe levels Lean 4.35.0's elaborator gives them
/// (<c>pp.all</c>: <c>Eq.{1}</c>, <c>ite.{1}</c>, <c>OfNat.ofNat.{0}</c>, …). Every name here is in
/// <c>lean/bundle-roots.txt</c>; a test checks it.
/// </summary>
internal static class Init
{
    public static readonly Expr Int32 = C("Int32");
    public static readonly Expr Int64 = C("Int64");
    public static readonly Expr Bool = C("Bool");
    public static readonly Expr Nat = C("Nat");
    public static readonly Expr True = C("Bool.true");
    public static readonly Expr False = C("Bool.false");

    public static readonly Expr Eq = C("Eq", Level.One);
    public static readonly Expr Not = C("Not");
    public static readonly Expr And = C("And");
    public static readonly Expr Or = C("Or");
    public static readonly Expr Ite = C("ite", Level.One);
    public static readonly Expr Decide = C("Decidable.decide");
    public static readonly Expr ForallPropDecidable = C("forall_prop_decidable");
    public static readonly Expr DecidableNot = C("instDecidableNot");
    public static readonly Expr DecidableAnd = C("instDecidableAnd");
    public static readonly Expr DecidableOr = C("instDecidableOr");
    public static readonly Expr DecidableEqBool = C("instDecidableEqBool");
    public static readonly Expr DecidableEqInt32 = C("instDecidableEqInt32");
    public static readonly Expr DecidableEqInt64 = C("instDecidableEqInt64");

    public static readonly Expr OfNat = C("OfNat.ofNat", Level.Zero);
    public static readonly Expr Int32OfNat = C("Int32.instOfNat");
    public static readonly Expr Int64OfNat = C("Int64.instOfNat");
    public static readonly Expr Neg = C("Neg.neg", Level.Zero);
    public static readonly Expr Int32Neg = C("Int32.instNeg");
    public static readonly Expr Int64Neg = C("Int64.instNeg");

    public static readonly Expr HAdd = C("HAdd.hAdd", Level.Zero, Level.Zero, Level.Zero);
    public static readonly Expr HSub = C("HSub.hSub", Level.Zero, Level.Zero, Level.Zero);
    public static readonly Expr HMul = C("HMul.hMul", Level.Zero, Level.Zero, Level.Zero);
    public static readonly Expr InstHAdd = C("instHAdd", Level.Zero);
    public static readonly Expr InstHSub = C("instHSub", Level.Zero);
    public static readonly Expr InstHMul = C("instHMul", Level.Zero);
    public static readonly Expr AddInt32 = C("instAddInt32");
    public static readonly Expr SubInt32 = C("instSubInt32");
    public static readonly Expr MulInt32 = C("instMulInt32");
    public static readonly Expr AddInt64 = C("instAddInt64");
    public static readonly Expr SubInt64 = C("instSubInt64");
    public static readonly Expr MulInt64 = C("instMulInt64");

    public static readonly Expr Lt = C("LT.lt", Level.Zero);
    public static readonly Expr Le = C("LE.le", Level.Zero);
    public static readonly Expr LtInt32 = C("instLTInt32");
    public static readonly Expr LeInt32 = C("instLEInt32");
    public static readonly Expr LtInt64 = C("instLTInt64");
    public static readonly Expr LeInt64 = C("instLEInt64");
    public static readonly Expr Int32DecLt = C("Int32.decLt");
    public static readonly Expr Int32DecLe = C("Int32.decLe");
    public static readonly Expr Int64DecLt = C("Int64.decLt");
    public static readonly Expr Int64DecLe = C("Int64.decLe");
    public static readonly Expr Gt = C("GT.gt", Level.Zero);
    public static readonly Expr Ge = C("GE.ge", Level.Zero);

    public static readonly Expr Exists = C("Exists", Level.One);

    public static readonly Expr Int32ToInt64 = C("Int32.toInt64");
    public static readonly Expr Int64ToInt32 = C("Int64.toInt32");

    // Well-founded recursion (M5a KTD14): every recursive method's types live in Type, so each level is 1.
    public static readonly Expr Dite = C("dite", Level.One);
    public static readonly Expr NatFix = C("WellFounded.Nat.fix", Level.One, Level.One);
    public static readonly Expr NatFixEq = C("WellFounded.Nat.fix_eq", Level.One, Level.One);
    public static readonly Expr InvImage = C("InvImage", Level.One, Level.One);
    public static readonly Expr PSigma = C("PSigma", Level.One, Level.One);
    public static readonly Expr PSigmaMk = C("PSigma.mk", Level.One, Level.One);
    public static readonly Name PSigmaName = Name.Parse("PSigma");
    public static readonly Expr IntToNat = C("Int.toNat");
    public static readonly Expr Int32ToInt = C("Int32.toInt");
    public static readonly Expr Int64ToInt = C("Int64.toInt");
    public static readonly Expr LtNat = C("instLTNat");

    public static readonly Expr BoolAnd = C("Bool.and");
    public static readonly Expr BoolOr = C("Bool.or");
    public static readonly Expr BoolNot = C("Bool.not");
    public static readonly Expr BoolXor = C("Bool.xor");
    public static readonly Expr NatBeq = C("Nat.beq");

    // The effect core (M6 U3; plan M6 KTD4, KTD6, lean/Warrant/Effect.lean and Checked.lean): the effect monad, its
    // exceptions and throw, and the raising integer models, which the monadic translation (M6 U9) emits. None is universe
    // polymorphic: the world and every value live in Type.
    public static readonly Expr ClrM = C("Warrant.ClrM");
    public static readonly Expr ClrExn = C("Warrant.ClrExn");
    public static readonly Expr ClrMThrow = C("Warrant.ClrM.throw");
    public static readonly Expr ClrExnOverflow = C("Warrant.ClrExn.overflow");
    public static readonly Expr ClrExnDivideByZero = C("Warrant.ClrExn.divideByZero");
    public static readonly Expr ClrExnNullReference = C("Warrant.ClrExn.nullReference");
    public static readonly Expr ClrExnInvalidOperation = C("Warrant.ClrExn.invalidOperation");
    public static readonly Expr ClrExnAssertFailed = C("Warrant.ClrExn.assertFailed");
    public static readonly Expr ClrExnThrown = C("Warrant.ClrExn.thrown");
    public static readonly Expr ClrExnExternal = C("Warrant.ClrExn.external");
    public static readonly Expr Int32AddChecked = C("Warrant.Int32.addChecked");
    public static readonly Expr Int32SubChecked = C("Warrant.Int32.subChecked");
    public static readonly Expr Int32MulChecked = C("Warrant.Int32.mulChecked");
    public static readonly Expr Int32NegChecked = C("Warrant.Int32.negChecked");
    public static readonly Expr Int32Div = C("Warrant.Int32.div");
    public static readonly Expr Int32Rem = C("Warrant.Int32.rem");
    public static readonly Expr Int64AddChecked = C("Warrant.Int64.addChecked");
    public static readonly Expr Int64SubChecked = C("Warrant.Int64.subChecked");
    public static readonly Expr Int64MulChecked = C("Warrant.Int64.mulChecked");
    public static readonly Expr Int64NegChecked = C("Warrant.Int64.negChecked");
    public static readonly Expr Int64Div = C("Warrant.Int64.div");
    public static readonly Expr Int64Rem = C("Warrant.Int64.rem");
    public static readonly Expr Int64ToInt32Checked = C("Warrant.Int64.toInt32Checked");

    /// <summary>The binder name of a constant function's or an implication's unused argument.</summary>
    public static readonly Name Unused = Name.From("x");

    private static ConstExpr C(string name, params Level[] levels) => Expr.Const(Name.Parse(name), levels);
}
