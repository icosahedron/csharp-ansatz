using System.Numerics;
using Warrant.Cic;
using Warrant.Vir;

namespace Warrant.Semantics;

/// <summary>
/// A C# condition as Lean's <c>ite</c> takes it: a proposition and a <c>Decidable</c> instance for it (KTD8). A quantified
/// claim (M5a KTD17) has no instance: a <c>∀</c> or <c>∃</c> is not decidable in general, and neither is a condition
/// built from one.
/// </summary>
/// <param name="Prop">The proposition <c>P</c>.</param>
/// <param name="Instance">A term of type <c>Decidable P</c>, or null when the proposition has none.</param>
public sealed record Condition(Expr Prop, Expr? Instance)
{
    /// <summary>The instance, for a rule that needs one: <c>decide</c> and <c>ite</c> take only a decidable condition.</summary>
    internal Expr DecidableInstance =>
        Instance ?? throw new TranslationException(null, "a quantified claim is not a bool value.");
}

/// <summary>
/// The literal encodings of docs/m4/05 ("Literals and the operator table"), in the shapes Lean 4.35.0 elaborates.
/// Literals are range-checked here, because Lean's <c>OfNat</c> instances wrap silently (docs/m4/01).
/// </summary>
public static class Literals
{
    /// <summary>The CIC type of a primitive: <c>Int32</c>, <c>Int64</c> or <c>Bool</c>.</summary>
    /// <param name="type">The primitive.</param>
    /// <returns>The type.</returns>
    public static Expr Type(VirPrimitive type) => type switch
    {
        VirPrimitive.Int32 => Init.Int32,
        VirPrimitive.Int64 => Init.Int64,
        VirPrimitive.Bool => Init.Bool,
        VirPrimitive.Decimal or VirPrimitive.Unit => throw new TranslationException(null, $"{type} is not translated until M6 U9."),
        _ => throw new ArgumentOutOfRangeException(nameof(type)),
    };

    /// <summary><c>true</c> or <c>false</c>: <c>Bool.true</c> or <c>Bool.false</c>.</summary>
    /// <param name="value">The value.</param>
    /// <returns>The constant.</returns>
    public static Expr Bool(bool value) => value ? Init.True : Init.False;

    /// <summary>An <c>int</c> literal: <c>@OfNat.ofNat Int32 n (@Int32.instOfNat n)</c>, under <c>Neg.neg</c> when negative.</summary>
    /// <param name="value">The value.</param>
    /// <returns>The term.</returns>
    public static Expr Int32(int value) => Integer(VirPrimitive.Int32, value);

    /// <summary>A <c>long</c> literal, as <see cref="Int32(int)"/> with <c>Int64</c>.</summary>
    /// <param name="value">The value.</param>
    /// <returns>The term.</returns>
    public static Expr Int64(long value) => Integer(VirPrimitive.Int64, value);

    /// <summary>A literal of a primitive type, as VIR stores it (a <c>bool</c> is 0 or 1).</summary>
    /// <param name="type">The primitive.</param>
    /// <param name="value">The value.</param>
    /// <returns>The term.</returns>
    /// <exception cref="TranslationException">The value is out of range for the type.</exception>
    public static Expr Of(VirPrimitive type, long value)
    {
        switch (type)
        {
            case VirPrimitive.Bool when value is 0 or 1:
                return Bool(value == 1);
            case VirPrimitive.Int32 when value is >= int.MinValue and <= int.MaxValue:
            case VirPrimitive.Int64:
                return Integer(type, value);
            default:
                throw new TranslationException(null, $"the literal {value} is out of range for {type}.");
        }
    }

    private static Expr Integer(VirPrimitive type, BigInteger value)
    {
        var (cic, ofNat, neg) = type == VirPrimitive.Int32
            ? (Init.Int32, Init.Int32OfNat, Init.Int32Neg)
            : (Init.Int64, Init.Int64OfNat, Init.Int64Neg);
        var magnitude = BigInteger.Abs(value);
        var natural = Expr.App(Init.OfNat, cic, Expr.NatLit(magnitude), Expr.App(ofNat, Expr.NatLit(magnitude)));
        return value.Sign < 0 ? Expr.App(Init.Neg, cic, neg, natural) : natural;
    }
}

/// <summary>
/// The operator table of docs/m4/05: every arithmetic, conversion and Boolean operation M4 translates, one fixed term
/// each (KTD8). The CLR-agreement tests check each row (KTD19).
/// </summary>
public static class Operators
{
    /// <summary><c>a + b</c>, <c>a - b</c> or <c>a * b</c>: <c>@HAdd.hAdd T T T (@instHAdd T instAddT) a b</c> and likewise.</summary>
    /// <param name="op">The operator.</param>
    /// <param name="type"><c>Int32</c> or <c>Int64</c>.</param>
    /// <param name="a">The left operand.</param>
    /// <param name="b">The right operand.</param>
    /// <returns>The term.</returns>
    public static Expr Binary(BinaryOp op, VirPrimitive type, Expr a, Expr b)
    {
        var t = Integer(type);
        bool is32 = type == VirPrimitive.Int32;
        var (head, inst, impl) = op switch
        {
            BinaryOp.Add => (Init.HAdd, Init.InstHAdd, is32 ? Init.AddInt32 : Init.AddInt64),
            BinaryOp.Sub => (Init.HSub, Init.InstHSub, is32 ? Init.SubInt32 : Init.SubInt64),
            BinaryOp.Mul => (Init.HMul, Init.InstHMul, is32 ? Init.MulInt32 : Init.MulInt64),
            BinaryOp.Div or BinaryOp.Rem => throw new TranslationException(null, $"{op} is not translated until M6 U9."),
            _ => throw new ArgumentOutOfRangeException(nameof(op)),
        };
        return Expr.App(head, t, t, t, Expr.App(inst, t, impl), a, b);
    }

    /// <summary><c>-a</c>: <c>@Neg.neg T T.instNeg a</c>.</summary>
    /// <param name="type"><c>Int32</c> or <c>Int64</c>.</param>
    /// <param name="a">The operand.</param>
    /// <returns>The term.</returns>
    public static Expr Neg(VirPrimitive type, Expr a) =>
        Expr.App(Init.Neg, Integer(type), type == VirPrimitive.Int32 ? Init.Int32Neg : Init.Int64Neg, a);

    /// <summary>
    /// An integer conversion: <c>Int32.toInt64 a</c> for <c>(long)a</c>, <c>Int64.toInt32 a</c> for <c>(int)a</c> on a
    /// <c>long</c>, and <c>a</c> itself between equal types (an open enum and its underlying type).
    /// </summary>
    /// <param name="from">The operand's (underlying) type.</param>
    /// <param name="to">The result's (underlying) type.</param>
    /// <param name="a">The operand.</param>
    /// <returns>The term.</returns>
    public static Expr Convert(VirPrimitive from, VirPrimitive to, Expr a) => (from, to) switch
    {
        _ when from == to => a,
        (VirPrimitive.Int32, VirPrimitive.Int64) => Expr.App(Init.Int32ToInt64, a),
        (VirPrimitive.Int64, VirPrimitive.Int32) => Expr.App(Init.Int64ToInt32, a),
        _ => throw new TranslationException(null, $"there is no conversion from {from} to {to}."),
    };

    /// <summary><c>x &amp;&amp; y</c> and <c>x &amp; y</c> as a value: <c>Bool.and x y</c>.</summary>
    /// <param name="x">The left operand.</param>
    /// <param name="y">The right operand.</param>
    /// <returns>The term.</returns>
    public static Expr And(Expr x, Expr y) => Expr.App(Init.BoolAnd, x, y);

    /// <summary><c>x || y</c> and <c>x | y</c> as a value: <c>Bool.or x y</c>.</summary>
    /// <param name="x">The left operand.</param>
    /// <param name="y">The right operand.</param>
    /// <returns>The term.</returns>
    public static Expr Or(Expr x, Expr y) => Expr.App(Init.BoolOr, x, y);

    /// <summary><c>x ^ y</c> on <c>bool</c>: <c>Bool.xor x y</c>.</summary>
    /// <param name="x">The left operand.</param>
    /// <param name="y">The right operand.</param>
    /// <returns>The term.</returns>
    public static Expr Xor(Expr x, Expr y) => Expr.App(Init.BoolXor, x, y);

    /// <summary><c>!x</c> as a value: <c>Bool.not x</c>.</summary>
    /// <param name="x">The operand.</param>
    /// <returns>The term.</returns>
    public static Expr Not(Expr x) => Expr.App(Init.BoolNot, x);

    /// <summary>A condition as a value: <c>@Decidable.decide P D</c>.</summary>
    /// <param name="condition">The condition.</param>
    /// <returns>The term.</returns>
    public static Expr Decide(Condition condition)
    {
        ArgumentNullException.ThrowIfNull(condition);
        return Expr.App(Init.Decide, condition.Prop, condition.DecidableInstance);
    }

    /// <summary><c>c ? t : e</c>, and every branch: <c>@ite T P D t e</c>.</summary>
    /// <param name="type">The result type.</param>
    /// <param name="condition">The condition.</param>
    /// <param name="then">The value when it holds.</param>
    /// <param name="else">The value when it does not.</param>
    /// <returns>The term.</returns>
    public static Expr Ite(Expr type, Condition condition, Expr then, Expr @else)
    {
        ArgumentNullException.ThrowIfNull(condition);
        return Expr.App(Init.Ite, type, condition.Prop, condition.DecidableInstance, then, @else);
    }

    /// <summary><c>Nat.beq a b</c>, which compares two closed-type indexes.</summary>
    /// <param name="a">The left index.</param>
    /// <param name="b">The right index.</param>
    /// <returns>The term.</returns>
    public static Expr NatBeq(Expr a, Expr b) => Expr.App(Init.NatBeq, a, b);

    private static Expr Integer(VirPrimitive type) => type switch
    {
        VirPrimitive.Int32 => Init.Int32,
        VirPrimitive.Int64 => Init.Int64,
        _ => throw new TranslationException(null, $"{type} is not an integer type."),
    };
}

/// <summary>
/// The condition table of docs/m4/05 ("Conditions and Boolean values"): each C# condition as a proposition and its
/// fixed <c>Decidable</c> instance.
/// </summary>
public static class Conditions
{
    /// <summary><c>a == b</c>: <c>@Eq T a b</c> with <c>instDecidableEqT a b</c>.</summary>
    /// <param name="type"><c>Int32</c>, <c>Int64</c> or <c>Bool</c>.</param>
    /// <param name="a">The left operand.</param>
    /// <param name="b">The right operand.</param>
    /// <returns>The condition.</returns>
    public static Condition Eq(VirPrimitive type, Expr a, Expr b)
    {
        var inst = type switch
        {
            VirPrimitive.Int32 => Init.DecidableEqInt32,
            VirPrimitive.Int64 => Init.DecidableEqInt64,
            VirPrimitive.Bool => Init.DecidableEqBool,
            _ => throw new TranslationException(null, $"== on {type} is not translated until M6 U9."),
        };
        return new Condition(Expr.App(Init.Eq, Literals.Type(type), a, b), Expr.App(inst, a, b));
    }

    /// <summary><c>a &lt; b</c>: <c>@LT.lt T instLTT a b</c> with <c>T.decLt a b</c>. For <c>a &gt; b</c>, swap the operands.</summary>
    /// <param name="type"><c>Int32</c> or <c>Int64</c>.</param>
    /// <param name="a">The left operand.</param>
    /// <param name="b">The right operand.</param>
    /// <returns>The condition.</returns>
    public static Condition Lt(VirPrimitive type, Expr a, Expr b) => type switch
    {
        VirPrimitive.Int32 => new(Expr.App(Init.Lt, Init.Int32, Init.LtInt32, a, b), Expr.App(Init.Int32DecLt, a, b)),
        VirPrimitive.Int64 => new(Expr.App(Init.Lt, Init.Int64, Init.LtInt64, a, b), Expr.App(Init.Int64DecLt, a, b)),
        _ => throw new TranslationException(null, $"< is not defined on {type}."),
    };

    /// <summary><c>a &lt;= b</c>: <c>@LE.le T instLET a b</c> with <c>T.decLe a b</c>. For <c>a &gt;= b</c>, swap the operands.</summary>
    /// <param name="type"><c>Int32</c> or <c>Int64</c>.</param>
    /// <param name="a">The left operand.</param>
    /// <param name="b">The right operand.</param>
    /// <returns>The condition.</returns>
    public static Condition Le(VirPrimitive type, Expr a, Expr b) => type switch
    {
        VirPrimitive.Int32 => new(Expr.App(Init.Le, Init.Int32, Init.LeInt32, a, b), Expr.App(Init.Int32DecLe, a, b)),
        VirPrimitive.Int64 => new(Expr.App(Init.Le, Init.Int64, Init.LeInt64, a, b), Expr.App(Init.Int64DecLe, a, b)),
        _ => throw new TranslationException(null, $"<= is not defined on {type}."),
    };

    /// <summary>
    /// <c>a &gt; b</c> in a quantified statement, as Lean elaborates it: <c>@GT.gt T instLTT a b</c> with <c>T.decLt b a</c>
    /// (M5a KTD17). A closed statement and a function body keep M4's swapped <see cref="Lt"/>.
    /// </summary>
    /// <param name="type"><c>Int32</c> or <c>Int64</c>.</param>
    /// <param name="a">The left operand.</param>
    /// <param name="b">The right operand.</param>
    /// <returns>The condition.</returns>
    public static Condition Gt(VirPrimitive type, Expr a, Expr b) => type switch
    {
        VirPrimitive.Int32 => new(Expr.App(Init.Gt, Init.Int32, Init.LtInt32, a, b), Expr.App(Init.Int32DecLt, b, a)),
        VirPrimitive.Int64 => new(Expr.App(Init.Gt, Init.Int64, Init.LtInt64, a, b), Expr.App(Init.Int64DecLt, b, a)),
        _ => throw new TranslationException(null, $"> is not defined on {type}."),
    };

    /// <summary><c>a &gt;= b</c> in a quantified statement: <c>@GE.ge T instLET a b</c> with <c>T.decLe b a</c>, as <see cref="Gt"/>.</summary>
    /// <param name="type"><c>Int32</c> or <c>Int64</c>.</param>
    /// <param name="a">The left operand.</param>
    /// <param name="b">The right operand.</param>
    /// <returns>The condition.</returns>
    public static Condition Ge(VirPrimitive type, Expr a, Expr b) => type switch
    {
        VirPrimitive.Int32 => new(Expr.App(Init.Ge, Init.Int32, Init.LeInt32, a, b), Expr.App(Init.Int32DecLe, b, a)),
        VirPrimitive.Int64 => new(Expr.App(Init.Ge, Init.Int64, Init.LeInt64, a, b), Expr.App(Init.Int64DecLe, b, a)),
        _ => throw new TranslationException(null, $">= is not defined on {type}."),
    };

    /// <summary><c>!x</c>: <c>Not P</c> with <c>@instDecidableNot P D</c>, and no instance when <c>P</c> has none.</summary>
    /// <param name="x">The operand.</param>
    /// <returns>The condition.</returns>
    public static Condition Not(Condition x)
    {
        ArgumentNullException.ThrowIfNull(x);
        return new(Expr.App(Init.Not, x.Prop), x.Instance is { } d ? Expr.App(Init.DecidableNot, x.Prop, d) : null);
    }

    /// <summary><c>x &amp;&amp; y</c>: <c>And Px Py</c> with <c>@instDecidableAnd Px Py Dx Dy</c>, and no instance when either has none.</summary>
    /// <param name="x">The left operand.</param>
    /// <param name="y">The right operand.</param>
    /// <returns>The condition.</returns>
    public static Condition And(Condition x, Condition y)
    {
        ArgumentNullException.ThrowIfNull(x);
        ArgumentNullException.ThrowIfNull(y);
        return new(
            Expr.App(Init.And, x.Prop, y.Prop),
            x.Instance is { } dx && y.Instance is { } dy ? Expr.App(Init.DecidableAnd, x.Prop, y.Prop, dx, dy) : null);
    }

    /// <summary><c>x || y</c>: <c>Or Px Py</c> with <c>@instDecidableOr Px Py Dx Dy</c>, and no instance when either has none.</summary>
    /// <param name="x">The left operand.</param>
    /// <param name="y">The right operand.</param>
    /// <returns>The condition.</returns>
    public static Condition Or(Condition x, Condition y)
    {
        ArgumentNullException.ThrowIfNull(x);
        ArgumentNullException.ThrowIfNull(y);
        return new(
            Expr.App(Init.Or, x.Prop, y.Prop),
            x.Instance is { } dx && y.Instance is { } dy ? Expr.App(Init.DecidableOr, x.Prop, y.Prop, dx, dy) : null);
    }

    /// <summary>A <c>bool</c> value <c>b</c> as a condition: <c>@Eq Bool b Bool.true</c> with <c>instDecidableEqBool b Bool.true</c>.</summary>
    /// <param name="b">The value.</param>
    /// <returns>The condition.</returns>
    public static Condition IsTrue(Expr b) => Eq(VirPrimitive.Bool, b, Init.True);

    /// <summary>
    /// <c>Spec.Implies(x, y)</c>: <c>∀ (_ : Px), Py</c> with <c>@forall_prop_decidable Px (fun _ =&gt; Py) Dx (fun _ =&gt; Dy)</c>,
    /// and no instance when either has none.
    /// </summary>
    /// <param name="x">The hypothesis.</param>
    /// <param name="y">The conclusion.</param>
    /// <returns>The condition.</returns>
    public static Condition Implies(Condition x, Condition y)
    {
        ArgumentNullException.ThrowIfNull(x);
        ArgumentNullException.ThrowIfNull(y);
        return new(
            Expr.Forall(Init.Unused, x.Prop, Closed(y.Prop)),
            x.Instance is { } dx && y.Instance is { } dy
                ? Expr.App(Init.ForallPropDecidable, x.Prop, Expr.Lam(Init.Unused, x.Prop, Closed(y.Prop)), dx, Expr.Lam(Init.Unused, x.Prop, Closed(dy)))
                : null);
    }

    /// <summary>
    /// A term placed under a binder it does not use. Translation builds terms with free variables and no loose bound
    /// variables, so placing one under a binder needs no lifting.
    /// </summary>
    internal static Expr Closed(Expr e) =>
        e.HasLooseBVars ? throw new InvalidOperationException("a translated term has loose bound variables") : e;
}
