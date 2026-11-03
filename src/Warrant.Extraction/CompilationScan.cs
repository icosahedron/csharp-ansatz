using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.Operations;
using Warrant.Vir;

namespace Warrant.Extraction;

/// <summary>Shared state for one extraction: the compilation, its semantic models, and the type units in use.</summary>
internal sealed class ExtractionContext
{
    private readonly Dictionary<SyntaxTree, SemanticModel> _models = new();
    private readonly Dictionary<string, INamedTypeSymbol> _used = new(StringComparer.Ordinal);
    private readonly Queue<INamedTypeSymbol> _pending = new();

    public ExtractionContext(Compilation compilation, VirFacts facts)
    {
        Compilation = compilation;
        Facts = facts;
    }

    public Compilation Compilation { get; }

    public VirFacts Facts { get; }

    public SemanticModel Model(SyntaxTree tree)
    {
        if (!_models.TryGetValue(tree, out var model))
        {
            model = Compilation.GetSemanticModel(tree);
            _models.Add(tree, model);
        }
        return model;
    }

    /// <summary>Records that a unit uses a record, enum or closed type, so it gets a type unit.</summary>
    public void UseType(INamedTypeSymbol type)
    {
        var key = Symbols.Key(type);
        if (!_used.ContainsKey(key))
        {
            _used.Add(key, type);
            _pending.Enqueue(type);
        }
    }

    public bool TryNextType(out INamedTypeSymbol type)
    {
        if (_pending.Count > 0)
        {
            type = _pending.Dequeue();
            return true;
        }
        type = null!;
        return false;
    }

    public bool IsUsed(string key) => _used.ContainsKey(key);

    public INamedTypeSymbol? UsedType(string key) => _used.TryGetValue(key, out var t) ? t : null;
}

/// <summary>
/// One pass over every operation in the compilation, verified or not: casts and unboxing to <c>[Closed]</c> enums
/// (WRT0008, KTD18), and every object creation, for the closed shape's fourth step.
/// </summary>
internal sealed class CompilationScan
{
    private CompilationScan()
    {
    }

    /// <summary>Conversions that can give a <c>[Closed]</c> enum an unnamed value, with their construct, in source order.</summary>
    public List<(IConversionOperation Conversion, string Construct, ISymbol Member)> ClosedEnumConversions { get; } = [];

    /// <summary>Every object creation, in source order.</summary>
    public List<IObjectCreationOperation> Creations { get; } = [];

    /// <summary>
    /// The construct for a conversion that can give a <c>[Closed]</c> enum a value it does not name, or null:
    /// an integer (or other enum) cast, or unboxing. <c>default</c> is checked separately.
    /// </summary>
    public static string? Classify(IConversionOperation conversion)
    {
        var target = Symbols.UnwrapNullable(conversion.Type);
        if (!Symbols.IsClosedEnum(target) || conversion.Operand is IDefaultValueOperation)
        {
            return null;
        }
        var source = Symbols.UnwrapNullable(conversion.Operand.Type);
        if (source is null || SymbolEqualityComparer.Default.Equals(source, target))
        {
            return null;
        }
        if (source.IsReferenceType)
        {
            return "unboxing to a closed enum";
        }
        if (Symbols.IsIntegral(source) || source.TypeKind == TypeKind.Enum)
        {
            return "integer cast to a closed enum";
        }
        return null;
    }

    public static CompilationScan Run(ExtractionContext context, CancellationToken cancellationToken)
    {
        var scan = new CompilationScan();
        foreach (var tree in context.Compilation.SyntaxTrees.OrderBy(t => t.FilePath, StringComparer.Ordinal))
        {
            var model = context.Model(tree);
            var seen = new HashSet<IOperation>();
            foreach (var node in tree.GetRoot(cancellationToken).DescendantNodesAndSelf())
            {
                cancellationToken.ThrowIfCancellationRequested();
                var op = model.GetOperation(node, cancellationToken);
                if (op is null || op.Parent is not null || !seen.Add(op))
                {
                    continue;
                }
                foreach (var d in op.DescendantsAndSelf())
                {
                    switch (d)
                    {
                        case IConversionOperation conversion when Classify(conversion) is { } construct:
                            scan.ClosedEnumConversions.Add((conversion, construct, EnclosingMember(model, d.Syntax)));
                            break;
                        case IObjectCreationOperation creation:
                            scan.Creations.Add(creation);
                            break;
                    }
                }
            }
        }
        scan.ClosedEnumConversions.Sort((a, b) => CompareSyntax(a.Conversion.Syntax, b.Conversion.Syntax));
        scan.Creations.Sort((a, b) => CompareSyntax(a.Syntax, b.Syntax));
        return scan;
    }

    private static int CompareSyntax(SyntaxNode a, SyntaxNode b)
    {
        int c = string.CompareOrdinal(a.SyntaxTree.FilePath, b.SyntaxTree.FilePath);
        if (c != 0)
        {
            return c;
        }
        c = a.SpanStart.CompareTo(b.SpanStart);
        return c != 0 ? c : a.Span.Length.CompareTo(b.Span.Length);
    }

    /// <summary>The member a node is in, as a diagnostic names it: lambdas and local functions belong to their member, accessors to their property.</summary>
    private static ISymbol EnclosingMember(SemanticModel model, SyntaxNode node)
    {
        var symbol = model.GetEnclosingSymbol(node.SpanStart)!;
        while (symbol is IMethodSymbol { MethodKind: MethodKind.LambdaMethod or MethodKind.LocalFunction or MethodKind.AnonymousFunction })
        {
            symbol = symbol.ContainingSymbol;
        }
        if (symbol is IMethodSymbol { AssociatedSymbol: { } associated })
        {
            symbol = associated;
        }
        return symbol;
    }
}
