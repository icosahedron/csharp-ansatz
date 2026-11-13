using System.Reflection;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace Warrant.Engine.Tests.Differential;

/// <summary>
/// The CLR's side of a skipped input (#233): the model ends in <c>assertFailed</c> where a <c>Spec.Assert</c> is false (#186)
/// or default-context arithmetic would wrap (#244), and the CLR runs on, so the skip must be confirmed on the CLR rather than
/// decided by the model alone. Each verified method gets a witness copy, a static or instance method of the same type and
/// signature, <c>__WarrantWitnessN</c>, whose body is the original's with every <c>Spec.Assert(c)</c> statement made
/// <c>if (!(c)) throw …</c> and the whole body in a <c>checked</c> block, so default-context arithmetic raises
/// <see cref="OverflowException"/> where it would wrap; an explicit <c>unchecked</c> stays unchecked, as in the model. The
/// copies are added members that nothing calls, so the original methods run as before.
/// <para>
/// A copy calls the original callees, so a failure inside a verified callee is not witnessed; such a skip is reported as a
/// disagreement, never accepted unconfirmed. A narrowing conversion is checked in the copy too, so a copy may raise where
/// the model only wraps; it is consulted only on an input the model already fails.
/// </para>
/// </summary>
internal static class AssertWitness
{
    private const string Prefix = "__WarrantWitness";

    /// <summary>The message of the exception a witness copy throws for a false <c>Spec.Assert</c>.</summary>
    public const string AssertMessage = "Warrant.Differential: Spec.Assert failed";

    /// <summary>
    /// <paramref name="compilation"/> with a witness copy of each verified method added, and the copies' names by the
    /// verified method's key.
    /// </summary>
    public static CSharpCompilation Add(CSharpCompilation compilation, out IReadOnlyDictionary<string, string> witnesses)
    {
        var names = new Dictionary<string, string>(StringComparer.Ordinal);
        var result = compilation;
        foreach (var tree in compilation.SyntaxTrees)
        {
            var model = compilation.GetSemanticModel(tree);
            var root = new Rewriter(model, names).Visit(tree.GetRoot());
            result = result.ReplaceSyntaxTree(tree, tree.WithRootAndOptions(root, tree.Options));
        }
        witnesses = names;
        return result;
    }

    /// <summary>
    /// Whether the witness copy of a method raises for these arguments (the receiver first for an instance method): a false
    /// <c>Spec.Assert</c> or an overflow. Null when the method has no copy.
    /// </summary>
    public static bool? Fails(MethodInfo original, string? witness, IReadOnlyList<object?> args)
    {
        if (witness is null)
        {
            return null;
        }
        var flags = BindingFlags.Public | BindingFlags.NonPublic | (original.IsStatic ? BindingFlags.Static : BindingFlags.Instance);
        var copy = original.DeclaringType!.GetMethod(witness, flags, [.. original.GetParameters().Select(p => p.ParameterType)])
            ?? throw new InvalidOperationException($"no witness {witness} for {original}");
        try
        {
            _ = copy.IsStatic ? CorpusAssembly.InvokeAndAwait(copy, null, args) : CorpusAssembly.InvokeAndAwait(copy, args[0], args.Skip(1).ToList());
            return false;
        }
        catch (OverflowException)
        {
            return true;
        }
        catch (InvalidProgramException ex) when (ex.Message == AssertMessage)
        {
            return true;
        }
#pragma warning disable CA1031 // Any other outcome is not a witness of the skip.
        catch (Exception)
#pragma warning restore CA1031
        {
            return false;
        }
    }

    private sealed class Rewriter(SemanticModel model, Dictionary<string, string> names) : CSharpSyntaxRewriter
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
            var added = new List<MemberDeclarationSyntax>();
            foreach (var method in original.Members.OfType<MethodDeclarationSyntax>())
            {
                if (method.ExplicitInterfaceSpecifier is not null || (method.Body is null && method.ExpressionBody is null)
                    || model.GetDeclaredSymbol(method) is not { } symbol
                    || !symbol.GetAttributes().Any(a => a.AttributeClass?.ToDisplayString() == "Warrant.VerifiedAttribute"))
                {
                    continue;
                }
                var name = $"{Prefix}{names.Count}";
                names.Add(symbol.GetDocumentationCommentId()!, name);
                added.Add(Copy(method, symbol, name));
            }
            return added.Count == 0 ? type : type.AddMembers([.. added]);
        }

        private MethodDeclarationSyntax Copy(MethodDeclarationSyntax method, IMethodSymbol symbol, string name)
        {
            BlockSyntax body;
            if (method.Body is { } block)
            {
                body = block;
            }
            else
            {
                var expression = method.ExpressionBody!.Expression;
                bool statement = symbol.ReturnsVoid
                    || (symbol.IsAsync && symbol.ReturnType is INamedTypeSymbol { IsGenericType: false });
                body = SyntaxFactory.Block(statement
                    ? SyntaxFactory.ExpressionStatement(expression)
                    : SyntaxFactory.ReturnStatement(expression));
            }
            body = (BlockSyntax)new AssertRewriter(model).Visit(body);
            var modifiers = SyntaxFactory.TokenList(method.Modifiers.Where(m =>
                !m.IsKind(SyntaxKind.OverrideKeyword) && !m.IsKind(SyntaxKind.VirtualKeyword) && !m.IsKind(SyntaxKind.SealedKeyword)
                && !m.IsKind(SyntaxKind.NewKeyword) && !m.IsKind(SyntaxKind.PartialKeyword)));
            return method
                .WithAttributeLists(default)
                .WithModifiers(modifiers)
                .WithIdentifier(SyntaxFactory.Identifier(name))
                .WithExpressionBody(null)
                .WithSemicolonToken(default)
                .WithBody(SyntaxFactory.Block(SyntaxFactory.CheckedStatement(SyntaxKind.CheckedStatement, body)));
        }
    }

    /// <summary>Makes each <c>Spec.Assert(c, …)</c> statement <c>if (!(c)) throw new InvalidProgramException(…)</c>.</summary>
    private sealed class AssertRewriter(SemanticModel model) : CSharpSyntaxRewriter
    {
        public override SyntaxNode? VisitExpressionStatement(ExpressionStatementSyntax node)
        {
            // The original node, still in the semantic model's tree: a copy's body is rewritten from the original syntax.
            if (node.Expression is InvocationExpressionSyntax invocation
                && model.GetSymbolInfo(invocation).Symbol is IMethodSymbol { Name: "Assert", ContainingType: { } spec }
                && spec.ToDisplayString() == "Warrant.Spec")
            {
                var condition = invocation.ArgumentList.Arguments[0].Expression;
                return SyntaxFactory.ParseStatement(
                    $"if (!({condition})) throw new global::System.InvalidProgramException(\"{AssertMessage}\");");
            }
            return base.VisitExpressionStatement(node);
        }
    }
}
