namespace Warrant.Vir;

/// <summary>What a unit is (docs/m4/04, "Units").</summary>
public enum VirUnitKind
{
    /// <summary><c>function</c>: a <c>[Verified]</c> method or property.</summary>
    Function,

    /// <summary><c>theorem</c>: a <c>[Theorem]</c>.</summary>
    Theorem,

    /// <summary><c>type</c>: a record, open enum or closed type.</summary>
    Type,
}

/// <summary>
/// A VIR unit: a member, a theorem or a type (KTD21). Fields are in encoding order.
/// Prefer the factories <see cref="Function"/>, <see cref="Theorem"/> and <see cref="TypeUnit"/>,
/// which fill the fields each kind has and leave the others null.
/// </summary>
/// <param name="Vir">The schema version; <see cref="CurrentVersion"/> for units written now.</param>
/// <param name="Key">The documentation-comment ID.</param>
/// <param name="Kind">The unit kind.</param>
/// <param name="Self">For an instance member of a record, the record's type key; otherwise null.</param>
/// <param name="Params">Parameters (functions and theorems); null for type units.</param>
/// <param name="Returns">Return type (functions); otherwise null.</param>
/// <param name="Body">A function's body: a <see cref="BlockStmt"/>, or a <see cref="VirExpr"/> for an expression-bodied member.</param>
/// <param name="Statement">A theorem's claim; otherwise null.</param>
/// <param name="Script">A theorem's proof script, from <c>.By(...)</c>; null when it has none, and for other kinds.</param>
/// <param name="Budget">A theorem's budget overrides, from <c>[Theorem(...)]</c>; null when it has none, and for other kinds.</param>
/// <param name="Definition">A type unit's definition; otherwise null.</param>
/// <param name="Assumptions">The assumptions the translation relies on (docs/m4/03).</param>
/// <param name="Facts">What changes the unit's meaning beyond its text.</param>
/// <param name="Deps">Keys of the units this one calls or whose types it mentions; stored sorted ordinally, without duplicates.</param>
public sealed record VirUnit(
    int Vir,
    string Key,
    VirUnitKind Kind,
    string? Self,
    VirList<VirParam>? Params,
    VirType? Returns,
    VirNode? Body,
    VirExpr? Statement,
    VirList<TacticNode>? Script,
    VirBudget? Budget,
    VirDefinition? Definition,
    VirList<VirAssumption> Assumptions,
    VirFacts Facts,
    VirList<string> Deps)
{
    /// <summary>
    /// The VIR schema version this library writes. Version 2 (M5a) added theorem parameters, quantifiers, measures,
    /// scripts and budgets; a unit that uses none of them encodes as in version 1 apart from this field (plan KTD18).
    /// </summary>
    public const int CurrentVersion = 2;

    private readonly VirList<string> _deps = Normalize(Deps);

    /// <summary>Keys of the units this one calls or whose types it mentions, sorted ordinally, without duplicates.</summary>
    public VirList<string> Deps
    {
        get => _deps;
        init => _deps = Normalize(value);
    }

    /// <summary>A function unit.</summary>
    /// <param name="key">The documentation-comment ID.</param>
    /// <param name="parameters">The parameters.</param>
    /// <param name="returns">The return type.</param>
    /// <param name="body">A <see cref="BlockStmt"/>, or a <see cref="VirExpr"/> for an expression-bodied member.</param>
    /// <param name="assumptions">The assumptions.</param>
    /// <param name="facts">The facts.</param>
    /// <param name="deps">The dependency keys, in any order.</param>
    /// <param name="self">For an instance member of a record, the record's type key.</param>
    /// <returns>The unit.</returns>
    public static VirUnit Function(
        string key,
        VirList<VirParam> parameters,
        VirType returns,
        VirNode body,
        VirList<VirAssumption> assumptions,
        VirFacts facts,
        VirList<string> deps,
        string? self = null) =>
        new(CurrentVersion, key, VirUnitKind.Function, self, parameters, returns, body, null, null, null, null, assumptions, facts, deps);

    /// <summary>A theorem unit. Its parameters are universally quantified.</summary>
    /// <param name="key">The documentation-comment ID.</param>
    /// <param name="statement">The claim.</param>
    /// <param name="assumptions">The assumptions.</param>
    /// <param name="facts">The facts.</param>
    /// <param name="deps">The dependency keys, in any order.</param>
    /// <param name="parameters">The parameters; none when null.</param>
    /// <param name="script">The proof script, if it has one.</param>
    /// <param name="budget">The budget overrides, if it has any.</param>
    /// <returns>The unit.</returns>
    public static VirUnit Theorem(
        string key,
        VirExpr statement,
        VirList<VirAssumption> assumptions,
        VirFacts facts,
        VirList<string> deps,
        VirList<VirParam>? parameters = null,
        VirList<TacticNode>? script = null,
        VirBudget? budget = null) =>
        new(CurrentVersion, key, VirUnitKind.Theorem, null, parameters ?? VirList<VirParam>.Empty, null, null, statement, script, budget, null, assumptions, facts, deps);

    /// <summary>A type unit.</summary>
    /// <param name="key">The documentation-comment ID, e.g. <c>T:Payouts.Payment</c>.</param>
    /// <param name="definition">The type's definition.</param>
    /// <param name="assumptions">The assumptions.</param>
    /// <param name="facts">The facts.</param>
    /// <param name="deps">The keys of the types its fields mention, in any order.</param>
    /// <returns>The unit.</returns>
    public static VirUnit TypeUnit(
        string key,
        VirDefinition definition,
        VirList<VirAssumption> assumptions,
        VirFacts facts,
        VirList<string> deps) =>
        new(CurrentVersion, key, VirUnitKind.Type, null, null, null, null, null, null, null, definition, assumptions, facts, deps);

    private static VirList<string> Normalize(VirList<string> deps)
    {
        var sorted = deps.Distinct(StringComparer.Ordinal).ToList();
        sorted.Sort(StringComparer.Ordinal);
        return new VirList<string>(sorted);
    }
}

/// <summary>A parameter: name and type.</summary>
/// <param name="Name">The source name.</param>
/// <param name="Type">The type.</param>
public sealed record VirParam(string Name, VirType Type);

/// <summary>An assumption the translation relies on (docs/m4/03, "Assumptions").</summary>
/// <param name="Kind">What is assumed.</param>
/// <param name="Subject">What it is assumed of: a parameter name for <see cref="VirAssumptionKind.NonNull"/>, a type key otherwise.</param>
public sealed record VirAssumption(VirAssumptionKind Kind, string Subject);

/// <summary>Kinds of assumption.</summary>
public enum VirAssumptionKind
{
    /// <summary><c>non-null</c>: the parameter, and every record or closed-class field reachable from it, is not null.</summary>
    NonNull,

    /// <summary><c>closed</c>: only the closed type's named members exist.</summary>
    Closed,

    /// <summary><c>closed-equality</c>: the closed class's own equality agrees with identity on its instances.</summary>
    ClosedEquality,
}

/// <summary>The <c>facts</c> of a unit.</summary>
/// <param name="Overflow">The project's overflow setting.</param>
/// <param name="Language">The C# language version, e.g. <c>14</c>.</param>
/// <param name="Extractor">The extractor version.</param>
/// <param name="Roslyn">The Roslyn version.</param>
public sealed record VirFacts(VirOverflow Overflow, string Language, string Extractor, string Roslyn);

/// <summary>A type unit's definition.</summary>
public abstract record VirDefinition
{
    private protected VirDefinition()
    {
    }
}

/// <summary><c>record{fields}</c>.</summary>
/// <param name="Fields">The fields, in primary-constructor order.</param>
public sealed record RecordDefinition(VirList<VirField> Fields) : VirDefinition;

/// <summary>A record field: name and type.</summary>
/// <param name="Name">The property name.</param>
/// <param name="Type">The type.</param>
public sealed record VirField(string Name, VirType Type);

/// <summary><c>enum{underlying, members}</c>: an open enum.</summary>
/// <param name="Underlying">The underlying type.</param>
/// <param name="Members">The members, in declaration order.</param>
public sealed record EnumDefinition(VirType Underlying, VirList<VirEnumMember> Members) : VirDefinition;

/// <summary>A member of an open enum.</summary>
/// <param name="Name">The member name.</param>
/// <param name="Value">The member value.</param>
public sealed record VirEnumMember(string Name, long Value);

/// <summary><c>closed{members}</c>: a <c>[Closed]</c> enum or class.</summary>
/// <param name="Members">The members, in declaration order.</param>
public sealed record ClosedDefinition(VirList<VirClosedMember> Members) : VirDefinition;

/// <summary>A member of a closed type.</summary>
/// <param name="Name">The member name.</param>
/// <param name="Value">The value for a closed enum; null for a closed class.</param>
public sealed record VirClosedMember(string Name, long? Value);
