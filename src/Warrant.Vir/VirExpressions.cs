namespace Warrant.Vir;

/// <summary><c>lit{type, value}</c>: a <c>bool</c>, <c>int32</c> or <c>int64</c> constant.</summary>
/// <param name="Type">The literal's type.</param>
/// <param name="Value">The value; for <c>bool</c>, 0 or 1.</param>
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
/// <param name="Overflow">Overflow behaviour; always <see cref="VirOverflow.Wrap"/> in M4.</param>
/// <param name="Operand">The operand.</param>
public sealed record UnaryExpr(VirType Type, UnaryOp Op, VirOverflow Overflow, VirExpr Operand) : VirExpr(Type);

/// <summary><c>binary{op, overflow}</c>.</summary>
/// <param name="Type">The result type, equal to the operands'.</param>
/// <param name="Op">The operator.</param>
/// <param name="Overflow">Overflow behaviour; always <see cref="VirOverflow.Wrap"/> in M4.</param>
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
