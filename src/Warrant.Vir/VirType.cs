namespace Warrant.Vir;

/// <summary>A VIR type (docs/m4/04, "Types").</summary>
public abstract record VirType
{
    private protected VirType()
    {
    }

    /// <summary><c>bool</c>.</summary>
    public static PrimitiveType Bool { get; } = new(VirPrimitive.Bool);

    /// <summary><c>int32</c>.</summary>
    public static PrimitiveType Int32 { get; } = new(VirPrimitive.Int32);

    /// <summary><c>int64</c>.</summary>
    public static PrimitiveType Int64 { get; } = new(VirPrimitive.Int64);

    /// <summary>A reference to a type unit.</summary>
    /// <param name="key">The type unit's key, e.g. <c>T:Payouts.Payment</c>.</param>
    /// <returns>The type <c>ref{key}</c>.</returns>
    public static RefType Ref(string key) => new(key);
}

/// <summary>The primitive VIR types.</summary>
public enum VirPrimitive
{
    /// <summary><c>bool</c>.</summary>
    Bool,

    /// <summary><c>int32</c>.</summary>
    Int32,

    /// <summary><c>int64</c>.</summary>
    Int64,
}

/// <summary>A primitive type, encoded as its name.</summary>
/// <param name="Kind">Which primitive.</param>
public sealed record PrimitiveType(VirPrimitive Kind) : VirType;

/// <summary>A record, open enum or closed type, by its type unit's key; encoded as <c>{"ref":key}</c>.</summary>
/// <param name="Key">The type unit's key.</param>
public sealed record RefType(string Key) : VirType;
