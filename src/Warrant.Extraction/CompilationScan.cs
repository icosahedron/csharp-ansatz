using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
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

    private readonly Dictionary<Compilation, (List<(IMethodSymbol, SyntaxNode)>, List<IWithOperation>)> _accessorsAndWiths = new();

    /// <summary>A compilation's <c>[UnsafeAccessor]</c> declarations and <c>with</c> expressions, computed once (#55).</summary>
    public (List<(IMethodSymbol, SyntaxNode)> Accessors, List<IWithOperation> Withs) AccessorsAndWiths(
        Compilation compilation, Func<(List<(IMethodSymbol, SyntaxNode)>, List<IWithOperation>)> find)
    {
        if (!_accessorsAndWiths.TryGetValue(compilation, out var found))
        {
            found = find();
            _accessorsAndWiths.Add(compilation, found);
        }
        return found;
    }

    /// <summary>The compilation that declares a symbol: the compilation itself or a referenced project's (#32).</summary>
    public Compilation CompilationOf(ISymbol symbol) =>
        IsOwn(symbol) ? Compilation : _referenced.First(c => SymbolEqualityComparer.Default.Equals(c.Assembly, symbol.ContainingAssembly));

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
    /// Every call of <see cref="object.MemberwiseClone"/> and every method group naming it, which create an instance
    /// without a constructor (#55), with the receiver's type and the types the use is written in, innermost first.
    /// </summary>
    public List<(SyntaxNode Syntax, ITypeSymbol? Receiver, IReadOnlyList<INamedTypeSymbol> EnclosingTypes)> MemberwiseClones { get; } = [];

    /// <summary>Every <c>with</c> expression, which copies a record without its declared constructors (#55).</summary>
    public List<IWithOperation> Withs { get; } = [];

    /// <summary>
    /// Every method declared with <c>[UnsafeAccessor]</c>, with the syntax that declares it: one can call a private
    /// constructor or <see cref="object.MemberwiseClone"/> from anywhere (#55).
    /// </summary>
    public List<(IMethodSymbol Method, SyntaxNode Syntax)> UnsafeAccessors { get; } = [];

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
    /// The scan of a referenced project's closed class (#32): its own declarations and its base classes' (#55). Its
    /// instance constructors are private, so they can be called only from inside its declarations, and
    /// <see cref="object.MemberwiseClone"/> is protected, so it can be called on an instance only from the class or a base
    /// class; a base class without source is rejected before this matters. WRT0008 is not reported for it.
    /// </summary>
    public static CompilationScan OfDeclarations(ExtractionContext context, INamedTypeSymbol type, CancellationToken cancellationToken)
    {
        var types = new List<INamedTypeSymbol>();
        for (var t = type; t is not null && t.SpecialType != SpecialType.System_Object; t = t.BaseType)
        {
            types.Add(t.OriginalDefinition);
        }
        var scan = Run(
            context,
            types.SelectMany(t => t.DeclaringSyntaxReferences)
                .Select(r => r.GetSyntax(cancellationToken))
                .OrderBy(n => n.SyntaxTree.FilePath, StringComparer.Ordinal)
                .ThenBy(n => n.SpanStart),
            cancellationToken);

        // An [UnsafeAccessor] can call a private constructor from any class, and a with expression can copy a record from
        // anywhere, so those of the whole referenced compilation count, and those of the compilation being verified.
        scan.UnsafeAccessors.Clear();
        scan.Withs.Clear();
        foreach (var compilation in new[] { context.CompilationOf(type), context.Compilation }.Distinct())
        {
            var (accessors, withs) = context.AccessorsAndWiths(compilation, () => AccessorsAndWiths(context, compilation, cancellationToken));
            scan.UnsafeAccessors.AddRange(accessors);
            scan.Withs.AddRange(withs);
        }
        scan.UnsafeAccessors.Sort((a, b) => CompareSyntax(a.Syntax, b.Syntax));
        scan.Withs.Sort((a, b) => CompareSyntax(a.Syntax, b.Syntax));
        return scan;
    }

    /// <summary>A compilation's <c>[UnsafeAccessor]</c> declarations and <c>with</c> expressions, found once per extraction.</summary>
    private static (List<(IMethodSymbol, SyntaxNode)>, List<IWithOperation>) AccessorsAndWiths(
        ExtractionContext context, Compilation compilation, CancellationToken cancellationToken)
    {
        var accessors = new List<(IMethodSymbol, SyntaxNode)>();
        var withs = new List<IWithOperation>();
        foreach (var tree in compilation.SyntaxTrees.OrderBy(t => t.FilePath, StringComparer.Ordinal))
        {
            var model = context.Model(tree);
            foreach (var node in tree.GetRoot(cancellationToken).DescendantNodes())
            {
                cancellationToken.ThrowIfCancellationRequested();
                if (UnsafeAccessor(model, node, cancellationToken) is { } accessor)
                {
                    accessors.Add((accessor, node));
                }
                else if (node is WithExpressionSyntax && model.GetOperation(node, cancellationToken) is IWithOperation with)
                {
                    withs.Add(with);
                }
            }
        }
        return (accessors, withs);
    }

    /// <summary>The types a node is written in, innermost first, as original definitions.</summary>
    private static List<INamedTypeSymbol> EnclosingTypes(SemanticModel model, SyntaxNode node)
    {
        var types = new List<INamedTypeSymbol>();
        var symbol = model.GetEnclosingSymbol(node.SpanStart);
        for (var t = symbol as INamedTypeSymbol ?? symbol?.ContainingType; t is not null; t = t.ContainingType)
        {
            types.Add(t.OriginalDefinition);
        }
        return types;
    }

    /// <summary>The method a declaration declares, if it is an <c>[UnsafeAccessor]</c>, which must be <c>extern</c>.</summary>
    private static IMethodSymbol? UnsafeAccessor(SemanticModel model, SyntaxNode node, CancellationToken cancellationToken)
    {
        var modifiers = node switch
        {
            MethodDeclarationSyntax m => m.Modifiers,
            LocalFunctionStatementSyntax l => l.Modifiers,
            _ => default,
        };
        return modifiers.Any(SyntaxKind.ExternKeyword)
            && model.GetDeclaredSymbol(node, cancellationToken) is IMethodSymbol method
            && method.GetAttributes().Any(a => Symbols.IsUnsafeAccessor(a.AttributeClass))
            ? method
            : null;
    }

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
                if (UnsafeAccessor(model, node, cancellationToken) is { } accessor)
                {
                    scan.UnsafeAccessors.Add((accessor, node));
                }
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
                        case IInvocationOperation { TargetMethod: { Name: nameof(MemberwiseClone), ContainingType.SpecialType: SpecialType.System_Object } } clone:
                            scan.MemberwiseClones.Add((clone.Syntax, clone.Instance?.Type, EnclosingTypes(model, clone.Syntax)));
                            break;
                        case IMethodReferenceOperation { Method: { Name: nameof(MemberwiseClone), ContainingType.SpecialType: SpecialType.System_Object } } group:
                            scan.MemberwiseClones.Add((group.Syntax, group.Instance?.Type, EnclosingTypes(model, group.Syntax)));
                            break;
                        case IWithOperation with:
                            scan.Withs.Add(with);
                            break;
                    }
                }
            }
        }
        scan.UnnamedClosedValues.Sort((a, b) => CompareSyntax(a.Operation.Syntax, b.Operation.Syntax));
        scan.Creations.Sort((a, b) => CompareSyntax(a.Syntax, b.Syntax));
        scan.MemberwiseClones.Sort((a, b) => CompareSyntax(a.Syntax, b.Syntax));
        scan.Withs.Sort((a, b) => CompareSyntax(a.Syntax, b.Syntax));
        scan.UnsafeAccessors.Sort((a, b) => CompareSyntax(a.Syntax, b.Syntax));
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
