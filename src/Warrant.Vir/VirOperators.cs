namespace Warrant.Vir;

/// <summary>Overflow behaviour of an arithmetic node or a unit (<c>wrap</c> or <c>checked</c>).</summary>
public enum VirOverflow
{
    /// <summary><c>wrap</c>: two's-complement wrapping, as in <c>unchecked</c> C#.</summary>
    Wrap,

    /// <summary><c>checked</c>: overflow throws. Never on a node in M4.</summary>
    Checked,
}

/// <summary>Operator of a <see cref="UnaryExpr"/>.</summary>
public enum UnaryOp
{
    /// <summary><c>neg</c>: unary minus.</summary>
    Neg,

    /// <summary><c>plus</c>: unary plus.</summary>
    Plus,
}

/// <summary>Operator of a <see cref="BinaryExpr"/>.</summary>
public enum BinaryOp
{
    /// <summary><c>add</c>.</summary>
    Add,

    /// <summary><c>sub</c>.</summary>
    Sub,

    /// <summary><c>mul</c>.</summary>
    Mul,
}

/// <summary>Operator of a <see cref="LogicalExpr"/>.</summary>
public enum LogicalOp
{
    /// <summary><c>and</c>: short-circuit <c>&amp;&amp;</c>.</summary>
    And,

    /// <summary><c>or</c>: short-circuit <c>||</c>.</summary>
    Or,

    /// <summary><c>and-eager</c>: <c>&amp;</c> on <c>bool</c>.</summary>
    AndEager,

    /// <summary><c>or-eager</c>: <c>|</c> on <c>bool</c>.</summary>
    OrEager,

    /// <summary><c>xor</c>: <c>^</c> on <c>bool</c>.</summary>
    Xor,
}

/// <summary>Operator of a <see cref="CompareExpr"/>.</summary>
public enum CompareOp
{
    /// <summary><c>eq</c>.</summary>
    Eq,

    /// <summary><c>ne</c>.</summary>
    Ne,

    /// <summary><c>lt</c>.</summary>
    Lt,

    /// <summary><c>le</c>.</summary>
    Le,

    /// <summary><c>gt</c>.</summary>
    Gt,

    /// <summary><c>ge</c>.</summary>
    Ge,
}

/// <summary>What <c>==</c> means for a <see cref="CompareExpr"/>, so translation never re-derives it.</summary>
public enum CompareKind
{
    /// <summary><c>int</c>: integer comparison.</summary>
    Int,

    /// <summary><c>enum</c>: open-enum comparison on the underlying value.</summary>
    Enum,

    /// <summary><c>bool</c>.</summary>
    Bool,

    /// <summary><c>record</c>: field-by-field equality.</summary>
    Record,

    /// <summary><c>closed</c>: same member.</summary>
    Closed,
}

/// <summary>Operator of a <see cref="RelationalPattern"/>.</summary>
public enum RelationalOp
{
    /// <summary><c>lt</c>.</summary>
    Lt,

    /// <summary><c>le</c>.</summary>
    Le,

    /// <summary><c>gt</c>.</summary>
    Gt,

    /// <summary><c>ge</c>.</summary>
    Ge,
}
