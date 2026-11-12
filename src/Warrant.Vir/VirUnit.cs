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

    /// <summary>
    /// <c>contract</c>: what a member of a contracted interface is assumed to do, from its <c>[ContractFor]</c> class (M6,
    /// KTD10). Its key is the interface member's key, its body the member's leading <c>Spec</c> statements.
    /// </summary>
    Contract,
}

/// <summary>
/// A VIR unit: a member, a theorem, a type or a contract (KTD21). Fields are in encoding order, except
/// <paramref name="Dependencies"/>, which is encoded after <paramref name="Params"/>.
/// Prefer the factories <see cref="Function"/>, <see cref="Theorem"/>, <see cref="TypeUnit"/> and <see cref="Contract"/>,
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
/// <param name="Dependencies">
/// A function's external dependencies, the fields and primary-constructor parameters it calls contracted interfaces through
/// (M6, KTD9), kept apart from <paramref name="Params"/> so parameter indices do not change; null when it has none.
/// </param>
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
    VirList<string> Deps,
    VirList<VirDependency>? Dependencies = null)
{
    /// <summary>
    /// The VIR schema version this library writes. Version 2 (M5a) added theorem parameters, quantifiers, measures,
    /// scripts and budgets; a unit that uses none of them encodes as in version 1 apart from this field (plan KTD18).
    /// Version 3 (M6, KTD19) added decimal, nullable, task and unit types, division and remainder, checked nodes, effect,
    /// nullable and contract nodes, dependencies, contract units and four assumption kinds; a unit that uses none of them
    /// encodes as in version 2 apart from this field.
    /// </summary>
    public const int CurrentVersion = 3;

    private readonly VirList<VirDependency>? _dependencies = Dependencies;

    private readonly VirList<string> _deps = Normalize(Deps, Dependencies);

    /// <summary>
    /// Keys of the units this one calls or whose types it mentions, sorted ordinally, without duplicates. They always
    /// include every member key of <see cref="Dependencies"/>, the keys of the contract units those members name, so the
    /// closure hash covers each contract the unit relies on (#166).
    /// </summary>
    public VirList<string> Deps
    {
        get => _deps;
        init => _deps = Normalize(value, _dependencies);
    }

    /// <summary>
    /// A function's external dependencies (M6, KTD9); null when it has none. Setting it adds its member keys to
    /// <see cref="Deps"/>.
    /// </summary>
    public VirList<VirDependency>? Dependencies
    {
        get => _dependencies;
        init
        {
            _dependencies = value;
            _deps = Normalize(_deps, value);
        }
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
    /// <param name="dependencies">The external dependencies (M6), if it has any.</param>
    /// <returns>The unit.</returns>
    public static VirUnit Function(
        string key,
        VirList<VirParam> parameters,
        VirType returns,
        VirNode body,
        VirList<VirAssumption> assumptions,
        VirFacts facts,
        VirList<string> deps,
        string? self = null,
        VirList<VirDependency>? dependencies = null) =>
        new(CurrentVersion, key, VirUnitKind.Function, self, parameters, returns, body, null, null, null, null, assumptions, facts, deps, dependencies);

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

    /// <summary>A contract unit (M6, KTD10): what an interface member is assumed to do.</summary>
    /// <param name="key">The interface member's documentation-comment ID.</param>
    /// <param name="parameters">The member's parameters.</param>
    /// <param name="returns">The member's return type.</param>
    /// <param name="body">The member's leading <see cref="RequiresStmt"/> and <see cref="EnsuresStmt"/>; empty when it assumes nothing.</param>
    /// <param name="assumptions">The assumptions.</param>
    /// <param name="facts">The facts.</param>
    /// <param name="deps">The dependency keys, in any order.</param>
    /// <returns>The unit.</returns>
    public static VirUnit Contract(
        string key,
        VirList<VirParam> parameters,
        VirType returns,
        BlockStmt body,
        VirList<VirAssumption> assumptions,
        VirFacts facts,
        VirList<string> deps) =>
        new(CurrentVersion, key, VirUnitKind.Contract, null, parameters, returns, body, null, null, null, null, assumptions, facts, deps);

    private static VirList<string> Normalize(VirList<string> deps, VirList<VirDependency>? dependencies)
    {
        var all = dependencies is null ? deps : deps.Concat(dependencies.SelectMany(d => d.Members));
        var sorted = all.Distinct(StringComparer.Ordinal).ToList();
        sorted.Sort(StringComparer.Ordinal);
        return new VirList<string>(sorted);
    }
}

/// <summary>
/// An external dependency of a function (M6, KTD9): a <c>readonly</c> field or never-assigned primary-constructor
/// parameter of a contracted interface type, and the interface members the function calls through it.
/// </summary>
/// <param name="Name">The field's or parameter's source name.</param>
/// <param name="Interface">The interface's type key, e.g. <c>T:Payments.IPaymentStore</c>.</param>
/// <param name="Members">
/// The keys of the members the function calls, which are also the keys of their contract units; stored sorted ordinally,
/// without duplicates.
/// </param>
public sealed record VirDependency(string Name, string Interface, VirList<string> Members)
{
    private readonly VirList<string> _members = Sorted(Members);

    /// <summary>The keys of the members the function calls, sorted ordinally, without duplicates.</summary>
    public VirList<string> Members
    {
        get => _members;
        init => _members = Sorted(value);
    }

    private static VirList<string> Sorted(VirList<string> members)
    {
        var sorted = members.Distinct(StringComparer.Ordinal).ToList();
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
/// <param name="Subject">
/// What it is assumed of: a parameter, field or dependency name for <see cref="VirAssumptionKind.NonNull"/>, a type key for
/// the type kinds, and for the M6 kinds the contract, callee, thrown type or method key the kind names.
/// </param>
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

    /// <summary>
    /// <c>referenced-source</c>: the closed class comes from a referenced assembly, whose shape and construction were
    /// checked from the source its project's build recorded; that assembly is assumed to be built from that source (#32).
    /// </summary>
    ReferencedSource,

    /// <summary><c>external-contract</c>: a dependency member does what its contract unit says (M6, KTD20); the subject is the member's key.</summary>
    ExternalContract,

    /// <summary><c>callee-contract</c>: a verified callee's proved contract, used at a call site (M6, KTD20); the subject is the callee's key.</summary>
    CalleeContract,

    /// <summary>
    /// <c>may-throw</c>: an explicit <c>throw</c> or a propagated external exception that the contract allows, so
    /// <c>Ensures</c> is not claimed on that path (M6, KTD20).
    /// </summary>
    MayThrow,

    /// <summary>
    /// <c>caller-precondition</c>: the method's own <c>Requires</c>, which nothing checks at run time or at unverified call
    /// sites (M6, KTD20); the subject is the method's key.
    /// </summary>
    CallerPrecondition,
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
