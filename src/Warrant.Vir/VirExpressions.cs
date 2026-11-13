using System.Numerics;

namespace Warrant.Vir;

/// <summary>
/// <c>lit{type, value}</c>: a <c>bool</c>, <c>int32</c> or <c>int64</c> constant, or the <c>unit</c> value that <c>return;</c>
/// returns (#215).
/// </summary>
/// <param name="Type">The literal's type.</param>
/// <param name="Value">The value; for <c>bool</c>, 0 or 1; for <c>unit</c>, 0.</param>
public sealed record LitExpr(VirType Type, long Value) : VirExpr(Type)
{
    /// <summary>A <c>bool</c> literal.</summary>
    /// <param name="value">The value.</param>
    /// <returns>The literal.</returns>
    public static LitExpr Bool(bool value) => new(VirType.Bool, value ? 1 : 0);

    /// <summary>An <c>int32</c> literal.</summary>
    /// <param name="value">The value.</param>
    /// <returns>The literal.</returns>
    public static LitExpr Int32(int value) => new(VirType.Int32, value);

    /// <summary>An <c>int64</c> literal.</summary>
    /// <param name="value">The value.</param>
    /// <returns>The literal.</returns>
    public static LitExpr Int64(long value) => new(VirType.Int64, value);
}

/// <summary><c>param{index}</c>: a parameter of the unit.</summary>
/// <param name="Type">The parameter's type.</param>
/// <param name="Index">Zero-based index into the unit's <c>params</c>.</param>
public sealed record ParamExpr(VirType Type, int Index) : VirExpr(Type);

/// <summary><c>local{id}</c>: a local declared by a <see cref="DeclStmt"/>.</summary>
/// <param name="Type">The local's type.</param>
/// <param name="Id">The local's ID.</param>
public sealed record LocalExpr(VirType Type, int Id) : VirExpr(Type);

/// <summary><c>self</c>: the receiver of an instance member of a record.</summary>
/// <param name="Type">The record type.</param>
public sealed record SelfExpr(VirType Type) : VirExpr(Type);

/// <summary><c>unary{op, overflow}</c>.</summary>
/// <param name="Type">The result type, equal to the operand's.</param>
/// <param name="Op">The operator.</param>
/// <param name="Overflow">Overflow behaviour (<see cref="VirOverflow"/>); always <see cref="VirOverflow.Wrap"/> in M4 and M5a.</param>
/// <param name="Operand">The operand.</param>
public sealed record UnaryExpr(VirType Type, UnaryOp Op, VirOverflow Overflow, VirExpr Operand) : VirExpr(Type);

/// <summary><c>binary{op, overflow}</c>.</summary>
/// <param name="Type">The result type, equal to the operands'.</param>
/// <param name="Op">The operator.</param>
/// <param name="Overflow">Overflow behaviour (<see cref="VirOverflow"/>); always <see cref="VirOverflow.Wrap"/> in M4 and M5a.</param>
/// <param name="L">The left operand.</param>
/// <param name="R">The right operand.</param>
public sealed record BinaryExpr(VirType Type, BinaryOp Op, VirOverflow Overflow, VirExpr L, VirExpr R) : VirExpr(Type);

/// <summary><c>logical{op}</c> on <c>bool</c>; its type is <c>bool</c>.</summary>
/// <param name="Op">The operator.</param>
/// <param name="L">The left operand.</param>
/// <param name="R">The right operand.</param>
public sealed record LogicalExpr(LogicalOp Op, VirExpr L, VirExpr R) : VirExpr(VirType.Bool);

/// <summary><c>not</c> on <c>bool</c>; its type is <c>bool</c>.</summary>
/// <param name="Operand">The operand.</param>
public sealed record NotExpr(VirExpr Operand) : VirExpr(VirType.Bool);

/// <summary><c>compare{op, kind}</c>; its type is <c>bool</c>.</summary>
/// <param name="Op">The operator.</param>
/// <param name="Kind">What the comparison means.</param>
/// <param name="L">The left operand.</param>
/// <param name="R">The right operand.</param>
public sealed record CompareExpr(CompareOp Op, CompareKind Kind, VirExpr L, VirExpr R) : VirExpr(VirType.Bool);

/// <summary><c>convert{from, to, overflow}</c>; its type is <paramref name="To"/>.</summary>
/// <param name="From">The operand's type.</param>
/// <param name="To">The result type.</param>
/// <param name="Overflow">Overflow behaviour of a narrowing conversion.</param>
/// <param name="Operand">The operand.</param>
public sealed record ConvertExpr(VirType From, VirType To, VirOverflow Overflow, VirExpr Operand) : VirExpr(To);

/// <summary><c>cond{c, then, else}</c>: <c>c ? then : else</c>.</summary>
/// <param name="Type">The result type.</param>
/// <param name="C">The condition.</param>
/// <param name="Then">The value when true.</param>
/// <param name="Else">The value when false.</param>
public sealed record CondExpr(VirType Type, VirExpr C, VirExpr Then, VirExpr Else) : VirExpr(Type);

/// <summary><c>call{target, args}</c>. For an instance member of a record, <c>Args[0]</c> is the receiver.</summary>
/// <param name="Type">The callee's return type.</param>
/// <param name="Target">The callee's unit key.</param>
/// <param name="Args">The arguments, in parameter order.</param>
public sealed record CallExpr(VirType Type, string Target, VirList<VirExpr> Args) : VirExpr(Type);

/// <summary><c>new{type, args}</c>: record construction.</summary>
/// <param name="Type">The record type.</param>
/// <param name="Args">The field values, in primary-constructor order.</param>
public sealed record NewExpr(VirType Type, VirList<VirExpr> Args) : VirExpr(Type);

/// <summary><c>get{type, field}</c>: a record field read.</summary>
/// <param name="Type">The field's type.</param>
/// <param name="Field">The field name.</param>
/// <param name="Target">The record value.</param>
public sealed record GetExpr(VirType Type, string Field, VirExpr Target) : VirExpr(Type);

/// <summary><c>with{base, updates}</c>: non-destructive record update.</summary>
/// <param name="Type">The record type.</param>
/// <param name="Base">The record value updated.</param>
/// <param name="Updates">The fields set, in source order.</param>
public sealed record WithExpr(VirType Type, VirExpr Base, VirList<WithUpdate> Updates) : VirExpr(Type);

/// <summary>One field assignment in a <see cref="WithExpr"/>.</summary>
/// <param name="Field">The field name.</param>
/// <param name="Value">The new value.</param>
public sealed record WithUpdate(string Field, VirExpr Value);

/// <summary><c>member{type, name}</c>: an enum member or a closed-class instance.</summary>
/// <param name="Type">The enum or closed type.</param>
/// <param name="Name">The member's name.</param>
public sealed record MemberExpr(VirType Type, string Name) : VirExpr(Type);

/// <summary><c>switch{scrutinee, arms}</c>: a switch expression.</summary>
/// <param name="Type">The result type.</param>
/// <param name="Scrutinee">The value switched on.</param>
/// <param name="Arms">The arms, in source order.</param>
public sealed record SwitchExpr(VirType Type, VirExpr Scrutinee, VirList<SwitchArm> Arms) : VirExpr(Type);

/// <summary>One arm of a <see cref="SwitchExpr"/>.</summary>
/// <param name="Pattern">The arm's pattern.</param>
/// <param name="Value">The arm's value.</param>
public sealed record SwitchArm(VirPattern Pattern, VirExpr Value);

/// <summary><c>implies{a, b}</c>, for theorem statements only; its type is <c>bool</c>.</summary>
/// <param name="A">The hypothesis.</param>
/// <param name="B">The conclusion.</param>
public sealed record ImpliesExpr(VirExpr A, VirExpr B) : VirExpr(VirType.Bool);

/// <summary>
/// <c>forall{local, name, domain, body}</c>: <c>Spec.ForAll&lt;T&gt;(x =&gt; body)</c>, for theorem statements only; its type
/// is <c>bool</c>. The bound variable is a local, read in the body by a <see cref="LocalExpr"/> with ID <paramref name="Local"/>.
/// </summary>
/// <param name="Local">The bound variable's local ID, unique within the unit.</param>
/// <param name="Name">The bound variable's source name.</param>
/// <param name="Domain">The type quantified over.</param>
/// <param name="Body">The claim.</param>
public sealed record ForAllExpr(int Local, string Name, VirType Domain, VirExpr Body) : VirExpr(VirType.Bool);

/// <summary>
/// <c>exists{local, name, domain, body}</c>: <c>Spec.Exists&lt;T&gt;(x =&gt; body)</c>, for theorem statements only; its type
/// is <c>bool</c>. The bound variable is a local, as in <see cref="ForAllExpr"/>.
/// </summary>
/// <param name="Local">The bound variable's local ID, unique within the unit.</param>
/// <param name="Name">The bound variable's source name.</param>
/// <param name="Domain">The type quantified over.</param>
/// <param name="Body">The claim.</param>
public sealed record ExistsExpr(int Local, string Name, VirType Domain, VirExpr Body) : VirExpr(VirType.Bool);

/// <summary>
/// <c>decimal{type, negative, mantissa, scale}</c>: a <c>decimal</c> constant, exactly as the CLR stores it (M6, KTD7):
/// <c>(-1)^negative × mantissa × 10^-scale</c>, so <c>1.0m</c> and <c>1.00m</c> are different literals of equal value.
/// Its type is <c>decimal</c>.
/// </summary>
/// <param name="Negative">The sign bit, which a negative zero also sets.</param>
/// <param name="Mantissa">The 96-bit unsigned mantissa, below 2^96.</param>
/// <param name="Scale">The power of ten the mantissa is divided by, 0 to 28.</param>
public sealed record DecimalLitExpr(bool Negative, BigInteger Mantissa, int Scale) : VirExpr(VirType.Decimal)
{
    /// <summary>The largest scale a <c>decimal</c> has.</summary>
    public const int MaxScale = 28;

    /// <summary>One more than the largest mantissa: 2^96.</summary>
    public static BigInteger MantissaLimit { get; } = BigInteger.One << 96;

    /// <summary>Whether the mantissa and scale are in the ranges a <c>decimal</c> has.</summary>
    public bool IsValid => Mantissa.Sign >= 0 && Mantissa < MantissaLimit && Scale >= 0 && Scale <= MaxScale;

    /// <summary>The literal of a <c>decimal</c> value, keeping its sign, mantissa and scale.</summary>
    /// <param name="value">The value.</param>
    /// <returns>The literal.</returns>
    public static DecimalLitExpr Of(decimal value)
    {
        var bits = decimal.GetBits(value);
        var mantissa = (new BigInteger((uint)bits[2]) << 64) | (new BigInteger((uint)bits[1]) << 32) | new BigInteger((uint)bits[0]);
        return new DecimalLitExpr(bits[3] < 0, mantissa, (bits[3] >> 16) & 0xFF);
    }

    /// <summary>The <c>decimal</c> value with this sign, mantissa and scale.</summary>
    /// <returns>The value.</returns>
    /// <exception cref="InvalidOperationException">The literal is not <see cref="IsValid"/>.</exception>
    public decimal ToDecimal()
    {
        if (!IsValid)
        {
            throw new InvalidOperationException($"Not a decimal: mantissa {Mantissa}, scale {Scale}.");
        }
        int Word(int i) => unchecked((int)(uint)((Mantissa >> (32 * i)) & uint.MaxValue));
        return new decimal(Word(0), Word(1), Word(2), Negative, (byte)Scale);
    }
}

/// <summary><c>null{type}</c>: the null value of a nullable type (M6, KTD5).</summary>
/// <param name="Type">The nullable type, a <see cref="NullableType"/>.</param>
public sealed record NullExpr(VirType Type) : VirExpr(Type);

/// <summary>
/// <c>isnull{operand}</c>: whether a nullable value is null (M6, KTD5): <c>x is null</c> and <c>x == null</c>, and, under a
/// <see cref="NotExpr"/>, <c>x is not null</c>, <c>x != null</c> and <c>x.HasValue</c>. Its type is <c>bool</c>.
/// </summary>
/// <param name="Operand">The nullable value.</param>
public sealed record IsNullExpr(VirExpr Operand) : VirExpr(VirType.Bool);

/// <summary>
/// <c>unwrap{type, kind, operand}</c>: the value inside a nullable value, which throws on null (M6, KTD5). The walker must
/// prove the operand non-null where the node stands.
/// </summary>
/// <param name="Type">The value's type: the operand's type without the nullable.</param>
/// <param name="Kind">What is read, which decides the exception.</param>
/// <param name="Operand">The nullable value.</param>
public sealed record UnwrapExpr(VirType Type, UnwrapKind Kind, VirExpr Operand) : VirExpr(Type);

/// <summary>
/// <c>coalesce{type, l, r}</c>: <c>l ?? r</c>, the value inside <paramref name="L"/> or, when it is null, <paramref name="R"/>,
/// which is evaluated only then (M6, KTD5). <c>x.GetValueOrDefault()</c> is this with the default value as
/// <paramref name="R"/>. It never throws itself.
/// </summary>
/// <param name="Type">The result type.</param>
/// <param name="L">The nullable value.</param>
/// <param name="R">The value when <paramref name="L"/> is null.</param>
public sealed record CoalesceExpr(VirType Type, VirExpr L, VirExpr R) : VirExpr(Type);

/// <summary>
/// <c>throw{type, exception}</c>: a throw expression, as in <c>x ?? throw new ArgumentException()</c> (M6, KTD4). It never
/// produces a value; its type is the one the context expects.
/// </summary>
/// <param name="Type">The type the context expects.</param>
/// <param name="Exception">The thrown exception type's key, e.g. <c>T:System.ArgumentException</c>.</param>
public sealed record ThrowExpr(VirType Type, string Exception) : VirExpr(Type);

/// <summary><c>await{type, operand}</c>: <c>await</c> of a call that returns a task (M6, KTD22).</summary>
/// <param name="Type">The awaited type; <c>unit</c> for a non-generic task.</param>
/// <param name="Operand">The awaited call, an <see cref="ExternalCallExpr"/> or a <see cref="CallExpr"/> of a <see cref="TaskType"/>.</param>
public sealed record AwaitExpr(VirType Type, VirExpr Operand) : VirExpr(Type);

/// <summary>
/// <c>external{type, dependency, member, args}</c>: a call to a member of a contracted interface through one of the unit's
/// dependencies (M6, KTD9). Its contract is the contract unit whose key is <paramref name="Member"/>.
/// </summary>
/// <param name="Type">The member's return type.</param>
/// <param name="Dependency">Zero-based index into the unit's <c>dependencies</c>.</param>
/// <param name="Member">The interface member's key, e.g. <c>M:Payments.IPaymentStore.GetPayment(System.Int32)</c>.</param>
/// <param name="Args">The arguments, in parameter order.</param>
public sealed record ExternalCallExpr(VirType Type, int Dependency, string Member, VirList<VirExpr> Args) : VirExpr(Type);

/// <summary>
/// <c>modelled{type, member, args}</c>: a call to a modelled BCL member, such as <c>Math.Max</c>, which translates to a
/// Warrant library definition (M6, KTD23).
/// </summary>
/// <param name="Type">The member's return type.</param>
/// <param name="Member">The member's key, e.g. <c>M:System.Math.Max(System.Int32,System.Int32)</c>.</param>
/// <param name="Args">The arguments, in parameter order.</param>
public sealed record ModelledCallExpr(VirType Type, string Member, VirList<VirExpr> Args) : VirExpr(Type);
