using Warrant.Cic;
using Warrant.Vir;

namespace Warrant.Semantics;

/// <summary>
/// The type units being translated, by key, and the mapping of VIR types to CIC (docs/m4/05, "Types"):
/// <c>int</c>, <c>long</c> and <c>bool</c> are Init's types, a type unit is its own constant, and <c>T?</c> is
/// <c>Option T</c> (M6 KTD5).
/// </summary>
internal sealed class TypeTable
{
    private readonly Dictionary<string, VirDefinition> _definitions;

    public TypeTable(IEnumerable<VirUnit> units)
    {
        _definitions = units
            .Where(u => u.Kind == VirUnitKind.Type)
            .ToDictionary(u => u.Key, u => u.Definition ?? throw new TranslationException(u.Key, "a type unit has no definition."), StringComparer.Ordinal);
    }

    /// <summary>The CIC type of a VIR type.</summary>
    public Expr Cic(VirType type) => type switch
    {
        PrimitiveType p => Literals.Type(p.Kind),
        RefType r => Expr.Const(LeanNames.ForKey(Known(r.Key))),
        // T? is Option T (M6 KTD5).
        NullableType n => Nullables.Option(Cic(n.Value)),
        _ => throw new TranslationException(null, $"unknown type {type}."),
    };

    /// <summary>The primitive a value of the type is represented by: itself, or an open enum's underlying type.</summary>
    public VirPrimitive Underlying(VirType type) => type switch
    {
        PrimitiveType p => p.Kind,
        RefType r when Definition(r.Key) is EnumDefinition e => Underlying(e.Underlying),
        _ => throw new TranslationException(null, $"{Describe(type)} is not an integer, a bool or an open enum."),
    };

    public RecordDefinition Record(VirType type) =>
        type is RefType r && Definition(r.Key) is RecordDefinition d
            ? d
            : throw new TranslationException(null, $"{Describe(type)} is not a record.");

    public ClosedDefinition Closed(VirType type) =>
        type is RefType r && Definition(r.Key) is ClosedDefinition d
            ? d
            : throw new TranslationException(null, $"{Describe(type)} is not a closed type.");

    public bool IsClosed(VirType type) => type is RefType r && Definition(r.Key) is ClosedDefinition;

    public bool IsRecord(VirType type) => type is RefType r && Definition(r.Key) is RecordDefinition;

    /// <summary>A record field's 0-based position, which is its primitive projection index.</summary>
    public int FieldIndex(VirType record, string field)
    {
        var fields = Record(record).Fields;
        for (int i = 0; i < fields.Count; i++)
        {
            if (string.Equals(fields[i].Name, field, StringComparison.Ordinal))
            {
                return i;
            }
        }
        throw new TranslationException(null, $"{Describe(record)} has no field {field}.");
    }

    private string Known(string key)
    {
        Definition(key);
        return key;
    }

    private VirDefinition Definition(string key) =>
        _definitions.TryGetValue(key, out var d) ? d : throw new TranslationException(null, $"the type {key} is not being translated.");

    private static string Describe(VirType type) => type is RefType r ? r.Key : type.ToString();
}
