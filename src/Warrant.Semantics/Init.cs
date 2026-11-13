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

    // An implicit operation's exact value (#244): `(a + b).toInt = a.toInt + b.toInt` over Int.
    public static readonly Expr Int = C("Int");
    public static readonly Expr IntAdd = C("Int.instAdd");
    public static readonly Expr IntSub = C("Int.instSub");
    public static readonly Expr IntMul = C("Int.instMul");
    public static readonly Expr IntNeg = C("Int.instNegInt");
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
    // The ClrExn names come from ClrExnNames, which the VC walker shares (#232); only the constructors translation emits
    // have a constant here (overflow, divideByZero, nullReference and invalidOperation are raised inside the Lean models).
    public static readonly Expr ClrExn = Expr.Const(ClrExnNames.Type);
    public static readonly Expr ClrMThrow = C("Warrant.ClrM.throw");
    public static readonly Expr ClrExnAssertFailed = Expr.Const(ClrExnNames.AssertFailed);
    public static readonly Expr ClrExnThrown = Expr.Const(ClrExnNames.Thrown);
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

    // Default-context arithmetic in a verified method that can raise (#244): assertFailed where the CLR would wrap.
    public static readonly Expr Int32AddImplicit = C("Warrant.Int32.addImplicit");
    public static readonly Expr Int32SubImplicit = C("Warrant.Int32.subImplicit");
    public static readonly Expr Int32MulImplicit = C("Warrant.Int32.mulImplicit");
    public static readonly Expr Int32NegImplicit = C("Warrant.Int32.negImplicit");
    public static readonly Expr Int64AddImplicit = C("Warrant.Int64.addImplicit");
    public static readonly Expr Int64SubImplicit = C("Warrant.Int64.subImplicit");
    public static readonly Expr Int64MulImplicit = C("Warrant.Int64.mulImplicit");
    public static readonly Expr Int64NegImplicit = C("Warrant.Int64.negImplicit");

    // Nullable values and Math on int and long (M6 U16; plan M6 KTD5, KTD23, lean/Warrant/Nullable.lean and Math.lean):
    // T? is Option T at level 0, null is none and a T converted to T? is some. The Nullable models take the world and the
    // value type; coalesce (?? and GetValueOrDefault) takes the value type.
    public static readonly Expr Option = C("Option", Level.Zero);
    public static readonly Expr OptionSome = C("Option.some", Level.Zero);
    public static readonly Expr OptionNone = C("Option.none", Level.Zero);
    public static readonly Expr NullableValue = C("Warrant.Nullable.value");
    public static readonly Expr NullableNonNull = C("Warrant.Nullable.nonNull");
    public static readonly Expr NullableCoalesce = C("Warrant.Nullable.coalesce");
    public static readonly Expr Int32Min = C("Warrant.Int32.min");
    public static readonly Expr Int32Max = C("Warrant.Int32.max");
    public static readonly Expr Int32Abs = C("Warrant.Int32.abs");
    public static readonly Expr Int64Min = C("Warrant.Int64.min");
    public static readonly Expr Int64Max = C("Warrant.Int64.max");
    public static readonly Expr Int64Abs = C("Warrant.Int64.abs");

    // decimal (M6 U4; plan M6 KTD7, lean/Warrant/Decimal.lean and Math.lean): the type, the literal constructor, equality
    // and order by value with their decision procedures, unary minus, the raising + and -, and Math.Min, Max and Abs.
    // None is universe polymorphic.
    public static readonly Expr EqRefl = C("Eq.refl", Level.One);
    public static readonly Expr Decimal = C("Warrant.Decimal");
    public static readonly Expr DecimalLit = C("Warrant.Decimal.lit");
    public static readonly Expr DecimalEq = C("Warrant.Decimal.eq");
    public static readonly Expr DecimalDecEq = C("Warrant.Decimal.decEq");
    public static readonly Expr DecimalLt = C("Warrant.Decimal.instLT");
    public static readonly Expr DecimalLe = C("Warrant.Decimal.instLE");
    public static readonly Expr DecimalDecLt = C("Warrant.Decimal.decLt");
    public static readonly Expr DecimalDecLe = C("Warrant.Decimal.decLe");
    public static readonly Expr DecimalNeg = C("Warrant.Decimal.neg");
    public static readonly Expr DecimalAdd = C("Warrant.Decimal.add");
    public static readonly Expr DecimalSub = C("Warrant.Decimal.sub");
    public static readonly Expr DecimalMin = C("Warrant.Decimal.min");
    public static readonly Expr DecimalMax = C("Warrant.Decimal.max");
    public static readonly Expr DecimalAbs = C("Warrant.Decimal.abs");

    // The monadic translation (M6 U9; plan M6 KTD4, KTD11), in the shapes Lean 4.35.0 elaborates `pure`, `>>=` and `/` to
    // in lean/Warrant/Checked.lean: ClrM σ's Monad instance is ExceptT.instMonad over StateT.instMonad over Id.instMonad,
    // pure and bind go through its Applicative and Bind projections, a null test is Option.isNone, a match on a nullable
    // value is Option.rec, and Spec.Assert's check returns Unit. Every value and world lives in Type.
    public static readonly Expr PurePure = C("Pure.pure", Level.Zero, Level.Zero);
    public static readonly Expr BindBind = C("Bind.bind", Level.Zero, Level.Zero);
    public static readonly Expr ApplicativeToPure = C("Applicative.toPure", Level.Zero, Level.Zero);
    public static readonly Expr MonadToApplicative = C("Monad.toApplicative", Level.Zero, Level.Zero);
    public static readonly Expr MonadToBind = C("Monad.toBind", Level.Zero, Level.Zero);
    public static readonly Expr ExceptTMonad = C("ExceptT.instMonad", Level.Zero, Level.Zero);
    public static readonly Expr StateTMonad = C("StateT.instMonad", Level.Zero, Level.Zero);
    public static readonly Expr StateM = C("StateM", Level.Zero);
    public static readonly Expr Id = C("Id", Level.Zero);
    public static readonly Expr IdMonad = C("Id.instMonad", Level.Zero);
    public static readonly Expr Unit = C("Unit");
    public static readonly Expr UnitUnit = C("Unit.unit");
    public static readonly Expr OptionIsNone = C("Option.isNone", Level.Zero);
    public static readonly Expr OptionRec = C("Option.rec", Level.One, Level.Zero);

    // C#'s / and % by a constant other than 0 and -1, which cannot raise and so stay pure (KTD11): Lean's truncating
    // Int32/Int64 division and remainder, which agree with C#'s there.
    public static readonly Expr HDiv = C("HDiv.hDiv", Level.Zero, Level.Zero, Level.Zero);
    public static readonly Expr HMod = C("HMod.hMod", Level.Zero, Level.Zero, Level.Zero);
    public static readonly Expr InstHDiv = C("instHDiv", Level.Zero);
    public static readonly Expr InstHMod = C("instHMod", Level.Zero);
    public static readonly Expr DivInt32 = C("instDivInt32");
    public static readonly Expr ModInt32 = C("instModInt32");
    public static readonly Expr DivInt64 = C("instDivInt64");
    public static readonly Expr ModInt64 = C("instModInt64");

    // Contract obligations (M6 U10; plan M6 KTD12, lean/Warrant/Effect.lean): Std.Do triples over ClrM σ, whose post-shape is
    // .except ClrExn (.arg σ .pure), with the WP instance instance resolution finds for ClrM σ (ExceptT.instWP over
    // State.instWP), one-state assertions ⌜p⌝ as SPred.pure at PostShape.args, and the postcondition as the pair Prod.mk
    // of the normal return's assertion and the exception conditions, whose exception half is ClrExn.Allowed. Every
    // level is 0 except PUnit.unit's (the end of the exception conditions, at level 1) and True/False's (none).
    public static readonly Expr Triple = C("Std.Do.Triple", Level.Zero, Level.Zero);
    public static readonly Expr ExceptTInstWP = C("Std.Do.ExceptT.instWP", Level.Zero, Level.Zero);
    public static readonly Expr StateInstWP = C("Std.Do.State.instWP", Level.Zero);
    public static readonly Expr PostShapeExcept = C("Std.Do.PostShape.except", Level.Zero);
    public static readonly Expr PostShapeArg = C("Std.Do.PostShape.arg", Level.Zero);
    public static readonly Expr PostShapePure = C("Std.Do.PostShape.pure", Level.Zero);
    public static readonly Expr PostShapeArgs = C("Std.Do.PostShape.args", Level.Zero);
    public static readonly Expr SPredPure = C("Std.Do.SPred.pure", Level.Zero);
    public static readonly Expr Assertion = C("Std.Do.Assertion", Level.Zero);
    public static readonly Expr ExceptConds = C("Std.Do.ExceptConds", Level.Zero);
    public static readonly Expr ProdMk = C("Prod.mk", Level.Zero, Level.Zero);
    public static readonly Expr PUnitUnit = C("PUnit.unit", Level.One);
    public static readonly Expr ClrExnAllowed = Expr.Const(ClrExnNames.Allowed);
    public static readonly Expr PropTrue = C("True");
    public static readonly Expr PropFalse = C("False");

    // The exception half of a Spec.NoThrow contract in place of ClrExn.Allowed (#182): only an exception propagated from a
    // dependency.
    public static readonly Expr ClrExnIsExternal = Expr.Const(ClrExnNames.External);

    /// <summary>The binder name of a constant function's or an implication's unused argument.</summary>
    public static readonly Name Unused = Name.From("x");

    private static ConstExpr C(string name, params Level[] levels) => Expr.Const(Name.Parse(name), levels);
}
