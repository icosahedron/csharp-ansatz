namespace Warrant;

/// <summary>References to Lean declarations, for proof scripts.</summary>
public static class Lean
{
    /// <summary>A declaration in the semantics bundle, such as <c>Lean.Const("Nat.add_comm")</c>.</summary>
    /// <param name="name">The declaration's full Lean name, as a string literal.</param>
    /// <returns>The reference.</returns>
    public static LeanConstant Const(string name) => new(name);
}

/// <summary>A reference to a Lean declaration, made by <see cref="Lean.Const(string)"/>.</summary>
public sealed class LeanConstant
{
    internal LeanConstant(string name) => Name = name;

    /// <summary>The declaration's full Lean name.</summary>
    public string Name { get; }
}
