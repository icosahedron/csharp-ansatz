namespace Warrant.Cic;

/// <summary>
/// A unit of admission into an environment: a single constant, or an inductive block (its types,
/// constructors and recursors, which are checked together).
/// </summary>
public abstract record Declaration
{
    /// <summary>The constants this declaration introduces, in order.</summary>
    public abstract IReadOnlyList<ConstantInfo> Constants { get; }
}

/// <summary>A declaration of one axiom, definition, theorem, opaque or quotient constant.</summary>
/// <param name="Constant">The constant.</param>
public sealed record ConstantDeclaration(ConstantInfo Constant) : Declaration
{
    /// <inheritdoc/>
    public override IReadOnlyList<ConstantInfo> Constants => [Constant];
}

/// <summary>
/// A (possibly mutual) block of inductive types with their constructors and recursors.
/// </summary>
/// <remarks>
/// Lean's kernel derives recursors from the types and constructors itself. lean4export includes
/// them anyway, and the Warrant kernel will check that they match what it derives.
/// </remarks>
/// <param name="Types">The inductive types.</param>
/// <param name="Constructors">The constructors of all types, in order.</param>
/// <param name="Recursors">The recursors.</param>
public sealed record InductiveDeclaration(
    EquatableArray<InductiveInfo> Types,
    EquatableArray<ConstructorInfo> Constructors,
    EquatableArray<RecursorInfo> Recursors) : Declaration
{
    /// <inheritdoc/>
    public override IReadOnlyList<ConstantInfo> Constants =>
        [.. Types, .. Constructors, .. Recursors];
}
