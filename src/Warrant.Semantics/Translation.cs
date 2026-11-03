using System.Collections.Immutable;
using Warrant.Cic;
using Warrant.Kernel;
using Warrant.Vir;

namespace Warrant.Semantics;

/// <summary>A unit could not be translated: a name collision, a missing dependency, or a VIR shape outside docs/m4/05.</summary>
public sealed class TranslationException : Exception
{
    /// <summary>Creates the exception.</summary>
    public TranslationException()
    {
    }

    /// <summary>Creates the exception with a message.</summary>
    /// <param name="message">The message.</param>
    public TranslationException(string message)
        : base(message)
    {
    }

    /// <summary>Creates the exception with a message and inner exception.</summary>
    /// <param name="message">The message.</param>
    /// <param name="innerException">The cause.</param>
    public TranslationException(string message, Exception innerException)
        : base(message, innerException)
    {
    }

    /// <summary>Creates the exception for a unit.</summary>
    /// <param name="key">The unit's key, or null when it is not known yet.</param>
    /// <param name="message">The message.</param>
    public TranslationException(string? key, string message)
        : base(key is null ? message : $"{key}: {message}")
    {
        Key = key;
    }

    /// <summary>The key of the unit that failed, when known.</summary>
    public string? Key { get; }
}

/// <summary>
/// A theorem's statement, built whole by trusted code (KTD22): its name and type are fixed here, and the engine supplies
/// only a proof through <see cref="WithProof"/>.
/// </summary>
public sealed class TheoremShell
{
    internal TheoremShell(Name name, Condition statement, VirList<TacticNode>? script, VirBudget? budget)
    {
        Name = name;
        Statement = statement;
        Script = script;
        Budget = budget;
    }

    /// <summary>The theorem's name.</summary>
    public Name Name { get; }

    /// <summary>The theorem's type: the statement's proposition <c>P</c>, closed over the theorem's parameters by <c>∀</c>.</summary>
    public Expr Type => Statement.Prop;

    /// <summary>
    /// The statement: the proposition <c>P</c> and its <c>Decidable P</c> instance <c>D</c>, for the <c>decide</c> proof; a
    /// quantified statement has no instance (M5a KTD17).
    /// </summary>
    public Condition Statement { get; }

    /// <summary>The proof script from <c>.By(...)</c>, which the engine runs to find a proof; null when the theorem has none.</summary>
    public VirList<TacticNode>? Script { get; }

    /// <summary>The theorem's budget overrides from <c>[Theorem(...)]</c>; null when it has none.</summary>
    public VirBudget? Budget { get; }

    /// <summary>The theorem declaration with this exact name and type, and <paramref name="proof"/> as its value.</summary>
    /// <param name="proof">The proof term; the kernel decides whether it proves <see cref="Type"/>.</param>
    /// <returns>The declaration to admit.</returns>
    public TheoremDecl WithProof(Expr proof)
    {
        ArgumentNullException.ThrowIfNull(proof);
        return new TheoremDecl(new TheoremInfo(Name, EquatableArray<Name>.Empty, Type, proof, EquatableArray.Create(Name)));
    }
}

/// <summary>One translated VIR unit.</summary>
public sealed class TranslatedUnit
{
    internal TranslatedUnit(string key, VirUnitKind kind, Name name, string displayName, IReadOnlyList<KernelDeclaration> declarations, TheoremShell? theorem)
    {
        Key = key;
        Kind = kind;
        Name = name;
        DisplayName = displayName;
        Declarations = [.. declarations];
        Theorem = theorem;
    }

    /// <summary>The unit's documentation-comment ID.</summary>
    public string Key { get; }

    /// <summary>What the unit is.</summary>
    public VirUnitKind Kind { get; }

    /// <summary>The Lean name of the unit's main constant.</summary>
    public Name Name { get; }

    /// <summary>The C# display name.</summary>
    public string DisplayName { get; }

    /// <summary>
    /// The declarations to admit, in order: one <see cref="DefinitionDecl"/> for a function; for a type, its
    /// <see cref="InductiveDecl"/> and then <c>$eq</c> or <c>$index</c>, or an open enum's definitions; empty for a theorem.
    /// </summary>
    public ImmutableArray<KernelDeclaration> Declarations { get; }

    /// <summary>A theorem's statement; null for other units.</summary>
    public TheoremShell? Theorem { get; }
}

/// <summary>The translation of a set of units (docs/m4/05): declarations in dependency order, and a display-name table.</summary>
public sealed class Translation
{
    internal Translation(IReadOnlyList<TranslatedUnit> units, IReadOnlyDictionary<Name, string> displayNames)
    {
        Units = [.. units];
        DisplayNames = displayNames.ToImmutableDictionary();
    }

    /// <summary>The units, every dependency before its users, ties broken by key (ordinal).</summary>
    public ImmutableArray<TranslatedUnit> Units { get; }

    /// <summary>The C# display name of every constant translation generated (KTD6).</summary>
    public ImmutableDictionary<Name, string> DisplayNames { get; }

    /// <summary>Finds a unit by key.</summary>
    /// <param name="key">The documentation-comment ID.</param>
    /// <returns>The unit, or null.</returns>
    public TranslatedUnit? Find(string key) => Units.FirstOrDefault(u => string.Equals(u.Key, key, StringComparison.Ordinal));

    /// <summary>The C# display name of a constant, or its Lean name when translation did not generate it.</summary>
    /// <param name="name">The constant's name.</param>
    /// <returns>The display name.</returns>
    public string Display(Name name)
    {
        ArgumentNullException.ThrowIfNull(name);
        return DisplayNames.TryGetValue(name, out var d) ? d : name.ToString();
    }
}
