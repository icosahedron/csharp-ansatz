namespace LeanSharp.Cic;

/// <summary>The kinds of entries in an environment.</summary>
public enum ConstantKind : byte
{
    /// <summary>An axiom.</summary>
    Axiom,

    /// <summary>A definition.</summary>
    Definition,

    /// <summary>A theorem.</summary>
    Theorem,

    /// <summary>An opaque definition (its value is never unfolded).</summary>
    Opaque,

    /// <summary>One of the four built-in quotient constants.</summary>
    Quot,

    /// <summary>An inductive type.</summary>
    Inductive,

    /// <summary>A constructor of an inductive type.</summary>
    Constructor,

    /// <summary>A recursor (eliminator) of an inductive type.</summary>
    Recursor,
}

/// <summary>How eagerly the kernel unfolds a definition, mirroring Lean's <c>ReducibilityHints</c>.</summary>
public enum ReducibilityHintsKind : byte
{
    /// <summary>Never unfold during lazy delta reduction unless forced.</summary>
    Opaque,

    /// <summary>Always unfold first.</summary>
    Abbrev,

    /// <summary>Unfold by definitional height: higher definitions unfold first.</summary>
    Regular,
}

/// <summary>Reducibility hints of a definition.</summary>
/// <param name="Kind">The kind of hint.</param>
/// <param name="Height">The definitional height (meaningful only for <see cref="ReducibilityHintsKind.Regular"/>).</param>
public readonly record struct ReducibilityHints(ReducibilityHintsKind Kind, uint Height)
{
    /// <summary>The <c>opaque</c> hint.</summary>
    public static ReducibilityHints Opaque => new(ReducibilityHintsKind.Opaque, 0);

    /// <summary>The <c>abbrev</c> hint.</summary>
    public static ReducibilityHints Abbrev => new(ReducibilityHintsKind.Abbrev, 0);

    /// <summary>The <c>regular h</c> hint.</summary>
    public static ReducibilityHints Regular(uint height) => new(ReducibilityHintsKind.Regular, height);

    /// <inheritdoc/>
    public override string ToString() => Kind == ReducibilityHintsKind.Regular ? $"regular {Height}" : Kind.ToString().ToLowerInvariant();
}

/// <summary>The safety level of a definition, mirroring Lean's <c>DefinitionSafety</c>.</summary>
public enum DefinitionSafety : byte
{
    /// <summary>An ordinary, checked definition.</summary>
    Safe,

    /// <summary>An <c>unsafe</c> definition: not checked, may not be used by safe declarations.</summary>
    Unsafe,

    /// <summary>A <c>partial</c> definition, implemented by an opaque safe wrapper.</summary>
    Partial,
}

/// <summary>Which of the four quotient constants, mirroring Lean's <c>QuotKind</c>.</summary>
public enum QuotKind : byte
{
    /// <summary><c>Quot</c>.</summary>
    Type,

    /// <summary><c>Quot.mk</c>.</summary>
    Ctor,

    /// <summary><c>Quot.lift</c>.</summary>
    Lift,

    /// <summary><c>Quot.ind</c>.</summary>
    Ind,
}

/// <summary>
/// An entry of the environment, mirroring Lean 4's <c>ConstantInfo</c>. Every constant has a
/// name, universe parameters and a type; the subclasses add kind-specific data.
/// </summary>
/// <param name="Name">The constant's name.</param>
/// <param name="LevelParams">The universe parameter names.</param>
/// <param name="Type">The constant's type.</param>
public abstract record ConstantInfo(Name Name, EquatableArray<Name> LevelParams, Expr Type)
{
    /// <summary>Which kind of constant this is.</summary>
    public abstract ConstantKind Kind { get; }

    /// <summary>Whether the constant is marked <c>unsafe</c>.</summary>
    public abstract bool IsUnsafe { get; }

    /// <summary>The value of a definition, theorem or opaque; otherwise <see langword="null"/>.</summary>
    public virtual Expr? Value => null;
}

/// <summary>An axiom.</summary>
public sealed record AxiomInfo(Name Name, EquatableArray<Name> LevelParams, Expr Type, bool IsUnsafeFlag)
    : ConstantInfo(Name, LevelParams, Type)
{
    /// <inheritdoc/>
    public override ConstantKind Kind => ConstantKind.Axiom;

    /// <inheritdoc/>
    public override bool IsUnsafe => IsUnsafeFlag;
}

/// <summary>A definition.</summary>
/// <param name="Name">The constant's name.</param>
/// <param name="LevelParams">The universe parameter names.</param>
/// <param name="Type">The constant's type.</param>
/// <param name="DefinitionValue">The definition's body.</param>
/// <param name="Hints">How eagerly the kernel unfolds it.</param>
/// <param name="Safety">Whether it is safe, unsafe or partial.</param>
/// <param name="All">All names in its mutual block (including itself).</param>
public sealed record DefinitionInfo(
    Name Name,
    EquatableArray<Name> LevelParams,
    Expr Type,
    Expr DefinitionValue,
    ReducibilityHints Hints,
    DefinitionSafety Safety,
    EquatableArray<Name> All)
    : ConstantInfo(Name, LevelParams, Type)
{
    /// <inheritdoc/>
    public override ConstantKind Kind => ConstantKind.Definition;

    /// <inheritdoc/>
    public override bool IsUnsafe => Safety == DefinitionSafety.Unsafe;

    /// <inheritdoc/>
    public override Expr Value => DefinitionValue;
}

/// <summary>A theorem.</summary>
/// <param name="Name">The constant's name.</param>
/// <param name="LevelParams">The universe parameter names.</param>
/// <param name="Type">The proposition.</param>
/// <param name="Proof">The proof term.</param>
/// <param name="All">All names in its mutual block (including itself).</param>
public sealed record TheoremInfo(Name Name, EquatableArray<Name> LevelParams, Expr Type, Expr Proof, EquatableArray<Name> All)
    : ConstantInfo(Name, LevelParams, Type)
{
    /// <inheritdoc/>
    public override ConstantKind Kind => ConstantKind.Theorem;

    /// <inheritdoc/>
    public override bool IsUnsafe => false;

    /// <inheritdoc/>
    public override Expr Value => Proof;
}

/// <summary>An opaque definition.</summary>
/// <param name="Name">The constant's name.</param>
/// <param name="LevelParams">The universe parameter names.</param>
/// <param name="Type">The constant's type.</param>
/// <param name="OpaqueValue">The (never unfolded) value.</param>
/// <param name="IsUnsafeFlag">Whether it is marked <c>unsafe</c>.</param>
/// <param name="All">All names in its mutual block (including itself).</param>
public sealed record OpaqueInfo(Name Name, EquatableArray<Name> LevelParams, Expr Type, Expr OpaqueValue, bool IsUnsafeFlag, EquatableArray<Name> All)
    : ConstantInfo(Name, LevelParams, Type)
{
    /// <inheritdoc/>
    public override ConstantKind Kind => ConstantKind.Opaque;

    /// <inheritdoc/>
    public override bool IsUnsafe => IsUnsafeFlag;

    /// <inheritdoc/>
    public override Expr Value => OpaqueValue;
}

/// <summary>One of the built-in quotient constants.</summary>
public sealed record QuotInfo(Name Name, EquatableArray<Name> LevelParams, Expr Type, QuotKind QuotKind)
    : ConstantInfo(Name, LevelParams, Type)
{
    /// <inheritdoc/>
    public override ConstantKind Kind => ConstantKind.Quot;

    /// <inheritdoc/>
    public override bool IsUnsafe => false;
}

/// <summary>An inductive type.</summary>
/// <param name="Name">The type's name.</param>
/// <param name="LevelParams">The universe parameter names.</param>
/// <param name="Type">The type's type (its arity).</param>
/// <param name="NumParams">The number of parameters (uniform across constructors).</param>
/// <param name="NumIndices">The number of indices.</param>
/// <param name="All">All types in the mutual block.</param>
/// <param name="Constructors">The constructor names, in order.</param>
/// <param name="NumNested">The number of auxiliary types introduced for nested occurrences.</param>
/// <param name="IsRec">Whether the type is recursive.</param>
/// <param name="IsUnsafeFlag">Whether it is marked <c>unsafe</c>.</param>
/// <param name="IsReflexive">Whether a constructor takes a function returning the type.</param>
public sealed record InductiveInfo(
    Name Name,
    EquatableArray<Name> LevelParams,
    Expr Type,
    int NumParams,
    int NumIndices,
    EquatableArray<Name> All,
    EquatableArray<Name> Constructors,
    int NumNested,
    bool IsRec,
    bool IsUnsafeFlag,
    bool IsReflexive)
    : ConstantInfo(Name, LevelParams, Type)
{
    /// <inheritdoc/>
    public override ConstantKind Kind => ConstantKind.Inductive;

    /// <inheritdoc/>
    public override bool IsUnsafe => IsUnsafeFlag;
}

/// <summary>A constructor of an inductive type.</summary>
/// <param name="Name">The constructor's name.</param>
/// <param name="LevelParams">The universe parameter names.</param>
/// <param name="Type">The constructor's type.</param>
/// <param name="Inductive">The inductive type it constructs.</param>
/// <param name="Index">Its position among the type's constructors.</param>
/// <param name="NumParams">The number of type parameters.</param>
/// <param name="NumFields">The number of fields.</param>
/// <param name="IsUnsafeFlag">Whether it is marked <c>unsafe</c>.</param>
public sealed record ConstructorInfo(
    Name Name,
    EquatableArray<Name> LevelParams,
    Expr Type,
    Name Inductive,
    int Index,
    int NumParams,
    int NumFields,
    bool IsUnsafeFlag)
    : ConstantInfo(Name, LevelParams, Type)
{
    /// <inheritdoc/>
    public override ConstantKind Kind => ConstantKind.Constructor;

    /// <inheritdoc/>
    public override bool IsUnsafe => IsUnsafeFlag;
}

/// <summary>A computation rule of a recursor: how it reduces on one constructor.</summary>
/// <param name="Constructor">The constructor.</param>
/// <param name="NumFields">The constructor's number of fields.</param>
/// <param name="Rhs">The right-hand side, abstracted over parameters, motives, minors and fields.</param>
public sealed record RecursorRule(Name Constructor, int NumFields, Expr Rhs);

/// <summary>A recursor (eliminator).</summary>
/// <param name="Name">The recursor's name.</param>
/// <param name="LevelParams">The universe parameter names.</param>
/// <param name="Type">The recursor's type.</param>
/// <param name="All">The inductive types of the mutual block.</param>
/// <param name="NumParams">The number of parameters.</param>
/// <param name="NumIndices">The number of indices.</param>
/// <param name="NumMotives">The number of motives.</param>
/// <param name="NumMinors">The number of minor premises.</param>
/// <param name="Rules">The computation rules, one per constructor.</param>
/// <param name="K">Whether K-like reduction applies.</param>
/// <param name="IsUnsafeFlag">Whether it is marked <c>unsafe</c>.</param>
public sealed record RecursorInfo(
    Name Name,
    EquatableArray<Name> LevelParams,
    Expr Type,
    EquatableArray<Name> All,
    int NumParams,
    int NumIndices,
    int NumMotives,
    int NumMinors,
    EquatableArray<RecursorRule> Rules,
    bool K,
    bool IsUnsafeFlag)
    : ConstantInfo(Name, LevelParams, Type)
{
    /// <inheritdoc/>
    public override ConstantKind Kind => ConstantKind.Recursor;

    /// <inheritdoc/>
    public override bool IsUnsafe => IsUnsafeFlag;
}
