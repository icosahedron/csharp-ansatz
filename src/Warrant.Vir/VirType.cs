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

    /// <summary><c>decimal</c> (M6, KTD7).</summary>
    public static PrimitiveType Decimal { get; } = new(VirPrimitive.Decimal);

    /// <summary><c>unit</c>: the result of a <c>void</c> method, and what a non-generic <c>Task</c> or <c>ValueTask</c> carries (M6).</summary>
    public static PrimitiveType Unit { get; } = new(VirPrimitive.Unit);

    /// <summary>A reference to a type unit.</summary>
    /// <param name="key">The type unit's key, e.g. <c>T:Payouts.Payment</c>.</param>
    /// <returns>The type <c>ref{key}</c>.</returns>
    public static RefType Ref(string key) => new(key);

    /// <summary>A nullable type (M6, KTD5).</summary>
    /// <param name="value">The type of the value when there is one.</param>
    /// <returns>The type <c>nullable{value}</c>.</returns>
    public static NullableType Nullable(VirType value) => new(value);

    /// <summary>A task type (M6, KTD22).</summary>
    /// <param name="result">The awaited type; <see cref="Unit"/> for a non-generic <c>Task</c> or <c>ValueTask</c>.</param>
    /// <returns>The type <c>task{result}</c>.</returns>
    public static TaskType Task(VirType result) => new(result);

    /// <summary>The key of <c>System.Threading.CancellationToken</c>, the one opaque type (#215, #253).</summary>
    public const string CancellationTokenKey = "T:System.Threading.CancellationToken";

    /// <summary>An opaque type: a parameter the method only passes on, never reads (#215).</summary>
    /// <param name="key">
    /// The CLR type's key; only <see cref="CancellationTokenKey"/> is extracted, and the VIR reader reads no other.
    /// </param>
    /// <returns>The type <c>opaque{key}</c>.</returns>
    public static OpaqueType Opaque(string key) => new(key);
}

/// <summary>The primitive VIR types. New members are added at the end, so the existing values keep their numbers.</summary>
public enum VirPrimitive
{
    /// <summary><c>bool</c>.</summary>
    Bool,

    /// <summary><c>int32</c>.</summary>
    Int32,

    /// <summary><c>int64</c>.</summary>
    Int64,

    /// <summary><c>decimal</c>: <c>System.Decimal</c> (M6, KTD7).</summary>
    Decimal,

    /// <summary><c>unit</c>: no value, for <c>void</c> and a non-generic <c>Task</c> or <c>ValueTask</c> (M6, KTD22).</summary>
    Unit,
}

/// <summary>A primitive type, encoded as its name.</summary>
/// <param name="Kind">Which primitive.</param>
public sealed record PrimitiveType(VirPrimitive Kind) : VirType;

/// <summary>A record, open enum or closed type, by its type unit's key; encoded as <c>{"ref":key}</c>.</summary>
/// <param name="Key">The type unit's key.</param>
public sealed record RefType(string Key) : VirType;

/// <summary>
/// <c>T?</c>: <c>int?</c>, <c>long?</c>, <c>decimal?</c>, or a nullable reference to a record or closed class (M6, KTD5);
/// encoded as <c>{"nullable":value}</c>.
/// </summary>
/// <param name="Value">The type of the value when there is one.</param>
public sealed record NullableType(VirType Value) : VirType;

/// <summary>
/// <c>Task&lt;T&gt;</c> or <c>ValueTask&lt;T&gt;</c>, and with <see cref="VirType.Unit"/> the non-generic forms (M6, KTD22);
/// encoded as <c>{"task":result}</c>. Both map to the same effect, so VIR does not tell them apart.
/// </summary>
/// <param name="Result">The awaited type.</param>
public sealed record TaskType(VirType Result) : VirType;

/// <summary>
/// An opaque type (#215), encoded as <c>{"opaque":key}</c>: a <c>CancellationToken</c> parameter of a verified method or a
/// contract member. Its only use is to be passed on as an argument; nothing reads, compares, builds or stores it, so a
/// model that cannot tell its values apart (translation binds it as <c>Unit</c>) loses nothing a proof could depend on.
/// </summary>
/// <param name="Key">The CLR type's key, e.g. <c>T:System.Threading.CancellationToken</c>.</param>
public sealed record OpaqueType(string Key) : VirType;
