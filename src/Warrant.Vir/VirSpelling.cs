namespace Warrant.Vir;

/// <summary>The encoding's names for enum values, shared by the writer and the reader.</summary>
internal static class VirSpelling
{
    public static string Of(VirUnitKind kind) => kind switch
    {
        VirUnitKind.Function => "function",
        VirUnitKind.Theorem => "theorem",
        VirUnitKind.Type => "type",
        _ => throw Bad(kind),
    };

    public static string Of(VirPrimitive primitive) => primitive switch
    {
        VirPrimitive.Bool => "bool",
        VirPrimitive.Int32 => "int32",
        VirPrimitive.Int64 => "int64",
        _ => throw Bad(primitive),
    };

    public static string Of(VirOverflow overflow) => overflow switch
    {
        VirOverflow.Wrap => "wrap",
        VirOverflow.Checked => "checked",
        _ => throw Bad(overflow),
    };

    public static string Of(UnaryOp op) => op switch
    {
        UnaryOp.Neg => "neg",
        UnaryOp.Plus => "plus",
        _ => throw Bad(op),
    };

    public static string Of(BinaryOp op) => op switch
    {
        BinaryOp.Add => "add",
        BinaryOp.Sub => "sub",
        BinaryOp.Mul => "mul",
        _ => throw Bad(op),
    };

    public static string Of(LogicalOp op) => op switch
    {
        LogicalOp.And => "and",
        LogicalOp.Or => "or",
        LogicalOp.AndEager => "and-eager",
        LogicalOp.OrEager => "or-eager",
        LogicalOp.Xor => "xor",
        _ => throw Bad(op),
    };

    public static string Of(CompareOp op) => op switch
    {
        CompareOp.Eq => "eq",
        CompareOp.Ne => "ne",
        CompareOp.Lt => "lt",
        CompareOp.Le => "le",
        CompareOp.Gt => "gt",
        CompareOp.Ge => "ge",
        _ => throw Bad(op),
    };

    public static string Of(CompareKind kind) => kind switch
    {
        CompareKind.Int => "int",
        CompareKind.Enum => "enum",
        CompareKind.Bool => "bool",
        CompareKind.Record => "record",
        CompareKind.Closed => "closed",
        _ => throw Bad(kind),
    };

    public static string Of(RelationalOp op) => op switch
    {
        RelationalOp.Lt => "lt",
        RelationalOp.Le => "le",
        RelationalOp.Gt => "gt",
        RelationalOp.Ge => "ge",
        _ => throw Bad(op),
    };

    public static string Of(VirAssumptionKind kind) => kind switch
    {
        VirAssumptionKind.NonNull => "non-null",
        VirAssumptionKind.Closed => "closed",
        VirAssumptionKind.ClosedEquality => "closed-equality",
        _ => throw Bad(kind),
    };

    private static ArgumentOutOfRangeException Bad<T>(T value) => new(nameof(value), value, $"Not a {typeof(T).Name}.");
}
