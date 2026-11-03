namespace Warrant.Vir;

/// <summary><c>const</c>: matches one constant (a <see cref="LitExpr"/> or a <see cref="MemberExpr"/>).</summary>
/// <param name="Value">The constant.</param>
public sealed record ConstPattern(VirExpr Value) : VirPattern;

/// <summary><c>discard</c>: <c>_</c> or <c>default</c>; matches anything.</summary>
public sealed record DiscardPattern : VirPattern;

/// <summary><c>relational{op, value}</c>, e.g. <c>&lt; 5</c>.</summary>
/// <param name="Op">The operator.</param>
/// <param name="Value">The constant compared against.</param>
public sealed record RelationalPattern(RelationalOp Op, VirExpr Value) : VirPattern;

/// <summary><c>and</c> of two patterns.</summary>
/// <param name="L">The left pattern.</param>
/// <param name="R">The right pattern.</param>
public sealed record AndPattern(VirPattern L, VirPattern R) : VirPattern;

/// <summary><c>or</c> of two patterns.</summary>
/// <param name="L">The left pattern.</param>
/// <param name="R">The right pattern.</param>
public sealed record OrPattern(VirPattern L, VirPattern R) : VirPattern;

/// <summary><c>not</c> of a pattern.</summary>
/// <param name="Operand">The negated pattern.</param>
public sealed record NotPattern(VirPattern Operand) : VirPattern;
