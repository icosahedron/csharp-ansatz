using System.Reflection;
using System.Text;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace Warrant.Engine.Tests.Differential;

/// <summary>
/// The copy of a compilation that plan M6 U22's tests run on the CLR, modelled on <c>TheoremStatementTests</c>: the same
/// sources with members added and none changed.
/// <list type="bullet">
/// <item>Each <c>Spec.Requires(c)</c> and <c>Spec.Ensures(r =&gt; e)</c> leading a method body, of a verified method or of a
/// contract-class member, becomes a static method of the same type, <c>static bool __WarrantSpecN(params[, T r]) =&gt; c</c>
/// or <c>e</c>, so the CLR computes it (<see cref="SpecEvaluator"/>). A contract-class member's are keyed by the interface
/// member it implements, as extraction keys its contract unit.</item>
/// <item>Each interface named by a <c>[ContractFor]</c> class gets a mock class, <c>WarrantDifferential.MockN</c>, that
/// implements every member explicitly by calling a handler with the member's key, its CLR return type and its arguments
/// (<see cref="Mocks"/>).</item>
/// <item>Each verified method's explicit throws: the type of every <c>throw new T(…)</c> in it and in the verified methods
/// it calls, transitively (<see cref="ExplicitThrows"/>).</item>
/// </list>
/// The added members are not verified and nothing in the original sources calls them, so a method extraction read runs
/// on the CLR exactly as it would in the original compilation.
/// </summary>
internal sealed class ContractCompilation
{
    private const string SpecPrefix = "__WarrantSpec";

    private const string MockNamespace = "WarrantDifferential";

    private ContractCompilation(
        CSharpCompilation compilation,
        Dictionary<string, List<SpecMethod>> specs,
        Dictionary<string, string> mocks,
        Dictionary<string, IReadOnlySet<string>> throws)
    {
        Compilation = compilation;
        Specs = specs.ToDictionary(p => p.Key, p => (IReadOnlyList<SpecMethod>)p.Value, StringComparer.Ordinal);
        Mocks = mocks;
        ExplicitThrows = throws;
    }

    /// <summary>The rewritten compilation.</summary>
    public CSharpCompilation Compilation { get; }

    /// <summary>
    /// Each method's <c>Spec.Requires</c> and <c>Spec.Ensures</c> as CLR methods, in source order, by the key of the verified
    /// method or of the interface member a contract-class member implements.
    /// </summary>
    public IReadOnlyDictionary<string, IReadOnlyList<SpecMethod>> Specs { get; }

    /// <summary>The metadata name of the mock class of each interface with a contract class, by the interface's key.</summary>
    public IReadOnlyDictionary<string, string> Mocks { get; }

    /// <summary>The keys of the exception types each verified method throws explicitly, its verified callees' included.</summary>
    public IReadOnlyDictionary<string, IReadOnlySet<string>> ExplicitThrows { get; }

    public static ContractCompilation Of(CSharpCompilation compilation)
    {
        var specs = new Dictionary<string, List<SpecMethod>>(StringComparer.Ordinal);
        var throws = new Dictionary<string, IReadOnlySet<string>>(StringComparer.Ordinal);
        var interfaces = new List<INamedTypeSymbol>();
        var result = compilation;
        int counter = 0;
        foreach (var tree in compilation.SyntaxTrees)
        {
            var model = compilation.GetSemanticModel(tree);
            foreach (var method in tree.GetRoot().DescendantNodes().OfType<MethodDeclarationSyntax>())
            {
                var symbol = model.GetDeclaredSymbol(method)!;
                if (IsVerified(symbol))
                {
                    var found = new HashSet<string>(StringComparer.Ordinal);
                    CollectThrows(compilation, symbol, found, new HashSet<IMethodSymbol>(SymbolEqualityComparer.Default));
                    throws.Add(symbol.GetDocumentationCommentId()!, found);
                }
            }
            foreach (var type in tree.GetRoot().DescendantNodes().OfType<ClassDeclarationSyntax>())
            {
                if (model.GetDeclaredSymbol(type) is { } t && t.GetAttributes().FirstOrDefault(a => a.AttributeClass?.ToDisplayString() == "Warrant.ContractForAttribute") is { } contractFor
                    && contractFor.ConstructorArguments is [{ Value: INamedTypeSymbol contracted }])
                {
                    interfaces.Add(contracted);
                }
            }
            var rewriter = new SpecRewriter(model, specs, () => counter++);
            var root = rewriter.Visit(tree.GetRoot());
            result = result.ReplaceSyntaxTree(tree, tree.WithRootAndOptions(root, tree.Options));
        }
        var mocks = new Dictionary<string, string>(StringComparer.Ordinal);
        var source = new StringBuilder("#nullable enable\n");
        for (int i = 0; i < interfaces.Count; i++)
        {
            var name = $"Mock{i}";
            mocks.Add(interfaces[i].GetDocumentationCommentId()!, $"{MockNamespace}.{name}");
            source.Append(MockSource(interfaces[i], name));
        }
        var options = compilation.SyntaxTrees.First().Options;
        result = result.AddSyntaxTrees(CSharpSyntaxTree.ParseText(source.ToString(), (CSharpParseOptions)options, path: "WarrantDifferentialMocks.cs"));
        return new ContractCompilation(result, specs, mocks, throws);
    }

    private static bool IsVerified(ISymbol symbol) =>
        symbol.GetAttributes().Any(a => a.AttributeClass?.ToDisplayString() == "Warrant.VerifiedAttribute");

    /// <summary>The types of the <c>throw new T(…)</c> in a method and, transitively, in the verified methods it calls.</summary>
    private static void CollectThrows(Compilation compilation, IMethodSymbol method, HashSet<string> found, HashSet<IMethodSymbol> seen)
    {
        if (!seen.Add(method))
        {
            return;
        }
        foreach (var reference in method.DeclaringSyntaxReferences)
        {
            var node = reference.GetSyntax();
            var model = compilation.GetSemanticModel(node.SyntaxTree);
            foreach (var thrown in node.DescendantNodes().Select(n => n switch
            {
                ThrowStatementSyntax s => s.Expression,
                ThrowExpressionSyntax e => e.Expression,
                _ => null,
            }).OfType<ExpressionSyntax>())
            {
                if (model.GetTypeInfo(thrown).Type is { } type)
                {
                    found.Add(type.GetDocumentationCommentId()!);
                }
            }
            foreach (var invocation in node.DescendantNodes().OfType<InvocationExpressionSyntax>())
            {
                if (model.GetSymbolInfo(invocation).Symbol is IMethodSymbol callee && IsVerified(callee))
                {
                    CollectThrows(compilation, callee.OriginalDefinition, found, seen);
                }
            }
        }
    }

    /// <summary>A mock class implementing every member of <paramref name="iface"/> and of the interfaces it inherits.</summary>
    private static string MockSource(INamedTypeSymbol iface, string name)
    {
        var format = SymbolDisplayFormat.FullyQualifiedFormat.AddMiscellaneousOptions(SymbolDisplayMiscellaneousOptions.IncludeNullableReferenceTypeModifier);
        var handler = "global::System.Func<string, global::System.Type, object?[], object?>";
        var text = new StringBuilder();
        text.Append(System.Globalization.CultureInfo.InvariantCulture, $"namespace {MockNamespace}\n{{\n    internal sealed class {name} : {iface.ToDisplayString(format)}\n    {{\n");
        text.Append(System.Globalization.CultureInfo.InvariantCulture, $"        private readonly {handler} _handler;\n        public {name}({handler} handler) {{ _handler = handler; }}\n");
        foreach (var owner in iface.AllInterfaces.Prepend(iface))
        {
            foreach (var member in owner.GetMembers())
            {
                if (member is not IMethodSymbol { MethodKind: MethodKind.Ordinary, IsAbstract: true } method)
                {
                    if (member.IsAbstract)
                    {
                        throw new NotSupportedException($"{member} is not a method; a mock implements methods only");
                    }
                    continue;
                }
                if (method.IsGenericMethod || method.Parameters.Any(p => p.RefKind != RefKind.None))
                {
                    throw new NotSupportedException($"{method} is generic or has a ref parameter; a mock does not implement it");
                }
                var returns = method.ReturnsVoid ? "void" : method.ReturnType.ToDisplayString(format);
                var parameters = string.Join(", ", method.Parameters.Select(p => $"{p.Type.ToDisplayString(format)} @{p.Name}"));
                var args = string.Join(", ", method.Parameters.Select(p => $"@{p.Name}"));
                var call = $"_handler(\"{method.GetDocumentationCommentId()}\", typeof({returns}), new object?[] {{ {args} }})";
                text.Append(System.Globalization.CultureInfo.InvariantCulture, $"        {returns} {owner.ToDisplayString(format)}.{method.Name}({parameters}) {{ {(method.ReturnsVoid ? call : $"return ({returns}){call}!")}; }}\n");
            }
        }
        text.Append("    }\n}\n");
        return text.ToString();
    }

    /// <summary>Adds a <c>Spec</c> method to its type for each leading <c>Spec.Requires</c> and <c>Spec.Ensures</c>.</summary>
    private sealed class SpecRewriter(SemanticModel model, Dictionary<string, List<SpecMethod>> specs, Func<int> next) : CSharpSyntaxRewriter
    {
        public override SyntaxNode? VisitClassDeclaration(ClassDeclarationSyntax node) => Add(node, base.VisitClassDeclaration(node));

        public override SyntaxNode? VisitRecordDeclaration(RecordDeclarationSyntax node) => Add(node, base.VisitRecordDeclaration(node));

        public override SyntaxNode? VisitStructDeclaration(StructDeclarationSyntax node) => Add(node, base.VisitStructDeclaration(node));

        private SyntaxNode? Add(TypeDeclarationSyntax original, SyntaxNode? visited)
        {
            if (visited is not TypeDeclarationSyntax type)
            {
                return visited;
            }
            var typeSymbol = model.GetDeclaredSymbol(original)!;
            var added = new List<MemberDeclarationSyntax>();
            foreach (var method in original.Members.OfType<MethodDeclarationSyntax>())
            {
                if (method.Body is not { } body)
                {
                    continue;
                }
                var symbol = model.GetDeclaredSymbol(method)!;
                var keys = Keys(symbol);
                if (keys.Count == 0)
                {
                    continue;
                }
                var parameters = string.Join(", ", method.ParameterList.Parameters.Select(p => $"{p.Type} {p.Identifier.Text}"));
                var names = method.ParameterList.Parameters.Select(p => p.Identifier.Text).ToList();
                foreach (var statement in body.Statements)
                {
                    if (statement is not ExpressionStatementSyntax { Expression: InvocationExpressionSyntax invocation }
                        || model.GetSymbolInfo(invocation).Symbol is not IMethodSymbol { ContainingType: { } spec } called
                        || spec.ToDisplayString() != "Warrant.Spec")
                    {
                        break;
                    }
                    var name = $"{SpecPrefix}{next()}";
                    SpecMethod specMethod;
                    string text;
                    switch (called.Name)
                    {
                        case "Requires":
                            text = $"public static bool {name}({parameters}) => {invocation.ArgumentList.Arguments[0].Expression};";
                            specMethod = new SpecMethod(TypeName(typeSymbol), name, SpecKind.Requires, statement.ToString().Trim());
                            break;
                        case "Ensures":
                            var lambda = invocation.ArgumentList.Arguments[0].Expression;
                            var (resultParameter, expression) = lambda switch
                            {
                                SimpleLambdaExpressionSyntax { ExpressionBody: { } e } s => (s.Parameter.Identifier.Text, e),
                                ParenthesizedLambdaExpressionSyntax { ParameterList.Parameters: [var p], ExpressionBody: { } e } => (p.Identifier.Text, e),
                                ParenthesizedLambdaExpressionSyntax { ParameterList.Parameters: [], ExpressionBody: { } e } => ((string?)null, e),
                                _ => throw new NotSupportedException($"{symbol}: a Spec.Ensures whose argument is not an expression-bodied lambda: {lambda}"),
                            };
                            if (resultParameter is null)
                            {
                                text = $"public static bool {name}({parameters}) => {expression};";
                            }
                            else
                            {
                                var resultType = ((GenericNameSyntax)((MemberAccessExpressionSyntax)invocation.Expression).Name).TypeArgumentList.Arguments[0];
                                var all = names.Count == 0 ? $"{resultType} {resultParameter}" : $"{parameters}, {resultType} {resultParameter}";
                                text = $"public static bool {name}({all}) => {expression};";
                            }
                            specMethod = new SpecMethod(TypeName(typeSymbol), name, resultParameter is null ? SpecKind.EnsuresWithoutResult : SpecKind.Ensures, statement.ToString().Trim());
                            break;
                        default:
                            // Spec.Decreases leads too; it states nothing a run can check.
                            continue;
                    }
                    added.Add(SyntaxFactory.ParseMemberDeclaration(text) ?? throw new InvalidOperationException(text));
                    foreach (var key in keys)
                    {
                        if (!specs.TryGetValue(key, out var list))
                        {
                            specs[key] = list = [];
                        }
                        list.Add(specMethod);
                    }
                }
            }
            return added.Count == 0 ? type : type.AddMembers([.. added]);
        }

        /// <summary>A verified method's own key; a contract-class member's interface members; none for other methods.</summary>
        private static List<string> Keys(IMethodSymbol symbol)
        {
            if (IsVerified(symbol))
            {
                return [symbol.GetDocumentationCommentId()!];
            }
            var type = symbol.ContainingType;
            if (!type.GetAttributes().Any(a => a.AttributeClass?.ToDisplayString() == "Warrant.ContractForAttribute"))
            {
                return [];
            }
            return [.. type.AllInterfaces
                .SelectMany(i => i.GetMembers())
                .Where(m => SymbolEqualityComparer.Default.Equals(type.FindImplementationForInterfaceMember(m), symbol))
                .Select(m => m.GetDocumentationCommentId()!)];
        }

        /// <summary>The CLR metadata name of a type: its namespace, its containing types after <c>+</c>, and its metadata name.</summary>
        private static string TypeName(INamedTypeSymbol type)
        {
            var name = type.MetadataName;
            for (var outer = type.ContainingType; outer is not null; outer = outer.ContainingType)
            {
                name = $"{outer.MetadataName}+{name}";
            }
            return type.ContainingNamespace.IsGlobalNamespace ? name : $"{type.ContainingNamespace.ToDisplayString()}.{name}";
        }
    }
}

/// <summary>What a <see cref="SpecMethod"/> computes.</summary>
internal enum SpecKind
{
    /// <summary>A <c>Spec.Requires</c>: a function of the parameters.</summary>
    Requires,

    /// <summary>A <c>Spec.Ensures&lt;T&gt;</c>: a function of the parameters and the result.</summary>
    Ensures,

    /// <summary>A <c>Spec.Ensures(() =&gt; …)</c>: a function of the parameters.</summary>
    EnsuresWithoutResult,
}

/// <summary>One <c>Spec</c> statement as a static method of the rewritten compilation.</summary>
/// <param name="Type">Its type's metadata name.</param>
/// <param name="Method">The method's name.</param>
/// <param name="Kind">What it computes.</param>
/// <param name="Source">The statement as written, for messages.</param>
internal sealed record SpecMethod(string Type, string Method, SpecKind Kind, string Source);

/// <summary>The <c>Spec</c> methods of a <see cref="ContractCompilation"/>, bound to its loaded assembly.</summary>
internal sealed class SpecEvaluator(ContractCompilation contracts, Assembly assembly)
{
    /// <summary>Whether a method or member has a <c>Spec</c> statement of the kind.</summary>
    public bool Has(string key, bool requires) =>
        contracts.Specs.TryGetValue(key, out var specs) && specs.Any(s => (s.Kind == SpecKind.Requires) == requires);

    /// <summary>The first <c>Spec.Requires</c> of a method or member that is false for these arguments, or null.</summary>
    public string? FailedRequires(string key, IReadOnlyList<object?> args) =>
        First(key, s => s.Kind == SpecKind.Requires, args, result: null);

    /// <summary>The first <c>Spec.Ensures</c> of a method or member that is false for these arguments and result, or null.</summary>
    public string? FailedEnsures(string key, IReadOnlyList<object?> args, object? result) =>
        First(key, s => s.Kind != SpecKind.Requires, args, result);

    private string? First(string key, Func<SpecMethod, bool> kind, IReadOnlyList<object?> args, object? result)
    {
        if (!contracts.Specs.TryGetValue(key, out var specs))
        {
            return null;
        }
        foreach (var spec in specs.Where(kind))
        {
            var method = assembly.GetType(spec.Type, throwOnError: true)!.GetMethod(spec.Method, BindingFlags.Public | BindingFlags.Static)!;
            object?[] all = spec.Kind == SpecKind.Ensures ? [.. args, result] : [.. args];
            if (!(bool)method.Invoke(null, BindingFlags.DoNotWrapExceptions, binder: null, all, culture: null)!)
            {
                return spec.Source;
            }
        }
        return null;
    }
}
