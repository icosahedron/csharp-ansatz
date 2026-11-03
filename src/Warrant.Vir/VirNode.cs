namespace Warrant.Vir;

/// <summary>
/// A VIR node: an expression, a statement or a pattern.
/// Nodes carry no ID; a node's ID is its index in <see cref="VirTree.PreOrder(VirUnit)"/>.
/// </summary>
public abstract record VirNode
{
    private protected VirNode()
    {
    }
}

/// <summary>An expression node (docs/m4/04, "Expressions"). Every expression has a type.</summary>
/// <param name="Type">The expression's type.</param>
public abstract record VirExpr(VirType Type) : VirNode;

/// <summary>A statement node (docs/m4/04, "Statements").</summary>
public abstract record VirStmt : VirNode;

/// <summary>A pattern node, in a switch arm or section label.</summary>
public abstract record VirPattern : VirNode;
