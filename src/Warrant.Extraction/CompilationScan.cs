using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.Operations;
using Warrant.Vir;

namespace Warrant.Extraction;

/// <summary>
/// Shared state for one extraction: the compilation, the referenced projects' compilations (#32), their semantic models,
/// and the type units in use.
/// </summary>
internal sealed class ExtractionContext
{
    private readonly Dictionary<SyntaxTree, SemanticModel> _models = new();
    private readonly Dictionary<string, INamedTypeSymbol> _used = new(StringComparer.Ordinal);
    private readonly Queue<INamedTypeSymbol> _pending = new();
    private readonly Func<string, Compilation?>? _referencedSource;
    private readonly List<Compilation> _referenced = [];

    public ExtractionContext(Compilation compilation, VirFacts facts, Func<string, Compilation?>? referencedSource = null, bool deferReferenced = false)
    {
        Compilation = compilation;
        Facts = facts;
        _referencedSource = referencedSource;
        DeferReferenced = deferReferenced;
    }

    public Compilation Compilation { get; }

    public VirFacts Facts { get; }

    /// <summary>Whether a closed class from another assembly is accepted without its source or a type unit (the analyzer).</summary>
    public bool DeferReferenced { get; }

    public SemanticModel Model(SyntaxTree tree)
    {
        if (!_models.TryGetValue(tree, out var model))
        {
            var owner = Compilation.ContainsSyntaxTree(tree) ? Compilation : _referenced.First(c => c.ContainsSyntaxTree(tree));
            model = owner.GetSemanticModel(tree);
            _models.Add(tree, model);
        }
        return model;
    }

    /// <summary>Whether a symbol is declared in the compilation itself, rather than in a reference.</summary>
    public bool IsOwn(ISymbol symbol) => SymbolEqualityComparer.Default.Equals(symbol.ContainingAssembly, Compilation.Assembly);

    /// <summary>
    /// A type from a referenced assembly as its project's recorded source declares it, or null if that source was not
    /// given. The two have the same documentation-comment ID, so the same key.
    /// </summary>
    public INamedTypeSymbol? FromReferencedSource(INamedTypeSymbol type)
    {
        // Type units are keyed by documentation-comment ID, which does not name the assembly, so the type's full name must
        // name only it among the compilation and its references (no extern-aliased twin, no type of the compilation's own).
        var metadataName = MetadataName(type);
        if (!SymbolEqualityComparer.Default.Equals(Compilation.GetTypeByMetadataName(metadataName), type))
        {
            return null;
        }

        // A referenced compilation stands for the reference with its assembly identity, and only for that one.
        if (type.ContainingAssembly is not { } assembly || type.IsGenericType || _referencedSource?.Invoke(assembly.Name) is not { } source
            || !source.Assembly.Identity.Equals(assembly.Identity))
        {
            return null;
        }
        if (!_referenced.Contains(source))
        {
            _referenced.Add(source);
        }
        var declared = source.GetTypeByMetadataName(metadataName);
        return declared is not null && string.Equals(Symbols.Key(declared), Symbols.Key(type), StringComparison.Ordinal) ? declared : null;
    }

    private static string MetadataName(INamedTypeSymbol type) =>
        type.ContainingType is { } outer
            ? MetadataName(outer) + "+" + type.MetadataName
            : type.ContainingNamespace is { IsGlobalNamespace: false } ns ? ns.ToDisplayString() + "." + type.MetadataName : type.MetadataName;

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
/// One pass over every operation in the compilation, verified or not: casts, unboxing and arithmetic that can give a
/// <c>[Closed]</c> enum an unnamed value (WRT0008, KTD18), and every object creation, for the closed shape's fourth step.
/// </summary>
internal sealed class CompilationScan
{
    private CompilationScan()
    {
    }

    /// <summary>Operations that can give a <c>[Closed]</c> enum an unnamed value, with their construct, in source order.</summary>
    public List<(IOperation Operation, string Construct, ISymbol Member)> UnnamedClosedValues { get; } = [];

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

    public static CompilationScan Run(ExtractionContext context, CancellationToken cancellationToken) =>
        Run(context, context.Compilation.SyntaxTrees.OrderBy(t => t.FilePath, StringComparer.Ordinal).Select(t => t.GetRoot(cancellationToken)), cancellationToken);

    /// <summary>
    /// The scan of a referenced project's closed class (#32): its own declarations only. Its instance constructors are
    /// private, so they can be called only from inside those declarations; WRT0008 is not reported for it.
    /// </summary>
    public static CompilationScan OfDeclarations(ExtractionContext context, INamedTypeSymbol type, CancellationToken cancellationToken) =>
        Run(
            context,
            type.DeclaringSyntaxReferences.Select(r => r.GetSyntax(cancellationToken)).OrderBy(n => n.SyntaxTree.FilePath, StringComparer.Ordinal).ThenBy(n => n.SpanStart),
            cancellationToken);

    private static CompilationScan Run(ExtractionContext context, IEnumerable<SyntaxNode> roots, CancellationToken cancellationToken)
    {
        var scan = new CompilationScan();
        foreach (var root in roots)
        {
            var model = context.Model(root.SyntaxTree);
            var seen = new HashSet<IOperation>();
            foreach (var node in root.DescendantNodesAndSelf())
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
                            scan.UnnamedClosedValues.Add((conversion, construct, EnclosingMember(model, d.Syntax)));
                            break;
                        case IBinaryOperation or IUnaryOperation or ICompoundAssignmentOperation or IIncrementOrDecrementOperation
                            when Symbols.IsClosedEnum(Symbols.UnwrapNullable(d.Type)):
                            scan.UnnamedClosedValues.Add((d, "arithmetic on a closed enum", EnclosingMember(model, d.Syntax)));
                            break;
                        case IObjectCreationOperation creation:
                            scan.Creations.Add(creation);
                            break;
                    }
                }
            }
        }
        scan.UnnamedClosedValues.Sort((a, b) => CompareSyntax(a.Operation.Syntax, b.Operation.Syntax));
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
