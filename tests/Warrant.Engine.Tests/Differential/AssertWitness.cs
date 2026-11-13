using System.Reflection;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace Warrant.Engine.Tests.Differential;

/// <summary>
/// The CLR's side of a skipped input (#233): the model ends in <c>assertFailed</c> where a <c>Spec.Assert</c> is false (#186)
/// or default-context <c>+</c>, <c>-</c>, <c>*</c> or unary <c>-</c> would wrap (#244), and the CLR runs on, so the skip must
/// be confirmed on the CLR rather than decided by the model alone. Each verified method gets a witness copy, a static or
/// instance method of the same type and signature, <c>__WarrantWitnessN</c>, whose body is the original's with every
/// <c>Spec.Assert(c)</c> statement made <c>if (!(c)) throw …</c> and the whole body in a <c>checked</c> block, so that
/// default-context arithmetic raises <see cref="OverflowException"/> where it would wrap. A default-context narrowing
/// cast, in the body or in an assertion's condition, is made <c>unchecked((T)checked(e))</c>: it wraps, since the model
/// wraps it too, and its operand stays checked (#266); an explicit <c>unchecked</c> stays unchecked. An expression body
/// that is a throw expression stays a <c>throw</c>. The copies are added members that nothing calls, so the original
/// methods run as before.
/// <para>
/// What a copy's <see cref="OverflowException"/> shows is weaker than a false assertion: an explicit <c>checked</c>
/// overflow, a <c>decimal</c> overflow or <c>MinValue / -1</c> raises it in the copy as in the original. So when the
/// original run itself threw <see cref="OverflowException"/>, only a false assertion witnesses the skip (#266). That is
/// strict in one case: default-context arithmetic that wraps and then an explicit <c>checked</c> operation that overflows
/// on the wrapped value (<c>var s = a + b; return checked(s * 2);</c>) is an <c>assertFailed</c> run the copy cannot
/// confirm, so it is reported as a disagreement, never skipped. A copy calls the original callees, so a failure inside a
/// verified callee is not witnessed either; such a skip is likewise reported as a disagreement, never accepted
/// unconfirmed.
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
    /// <c>Spec.Assert</c>, or an overflow unless the original run threw <see cref="OverflowException"/> itself
    /// (<paramref name="thrown"/>). Null when the method has no copy.
    /// </summary>
    public static bool? Fails(MethodInfo original, string? witness, IReadOnlyList<object?> args, Exception? thrown = null)
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
            return thrown is not OverflowException;
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
            // Every decision is made on the original nodes, which the semantic model knows (#266); only then is the
            // rewritten expression of an expression body put into a new statement.
            var rewriter = new BodyRewriter(model);
            BlockSyntax body;
            if (method.Body is { } block)
            {
                body = (BlockSyntax)rewriter.Visit(block);
            }
            else
            {
                var expression = method.ExpressionBody!.Expression;
                bool statement = symbol.ReturnsVoid
                    || (symbol.IsAsync && symbol.ReturnType is INamedTypeSymbol { IsGenericType: false });
                body = SyntaxFactory.Block(
                    BodyRewriter.IsAssert(model, expression) is { } condition ? rewriter.Check(condition)
                    // `=> throw e` is the statement `throw e;`, never `return throw e;`.
                    : expression is ThrowExpressionSyntax thrown ? SyntaxFactory.ThrowStatement((ExpressionSyntax)rewriter.Visit(thrown.Expression))
                    : statement ? SyntaxFactory.ExpressionStatement((ExpressionSyntax)rewriter.Visit(expression))
                    : SyntaxFactory.ReturnStatement((ExpressionSyntax)rewriter.Visit(expression)));
            }
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

    /// <summary>
    /// Makes each <c>Spec.Assert(c, …)</c> statement <c>if (!(c)) throw new InvalidProgramException(…)</c>, and each narrowing
    /// cast in C#'s default context, in the body or in an assertion's condition, <c>unchecked((T)checked(e))</c>. It must
    /// visit original nodes, which the semantic model knows.
    /// </summary>
    private sealed class BodyRewriter(SemanticModel model) : CSharpSyntaxRewriter
    {
        /// <summary>The condition of a <c>Spec.Assert</c> invocation (an original node); null for any other expression.</summary>
        public static ExpressionSyntax? IsAssert(SemanticModel model, ExpressionSyntax expression) =>
            expression is InvocationExpressionSyntax invocation
            && model.GetSymbolInfo(invocation).Symbol is IMethodSymbol { Name: "Assert", ContainingType: { } spec }
            && spec.ToDisplayString() == "Warrant.Spec"
                ? invocation.ArgumentList.Arguments[0].Expression
                : null;

        /// <summary>
        /// The copy's check of an assertion's condition (an original node), the condition rewritten as the body is, so a
        /// narrowing in it wraps as the model's does (#266).
        /// </summary>
        public StatementSyntax Check(ExpressionSyntax condition) =>
            SyntaxFactory.ParseStatement($"if (!({Visit(condition)})) throw new global::System.InvalidProgramException(\"{AssertMessage}\");");

        public override SyntaxNode? VisitExpressionStatement(ExpressionStatementSyntax node) =>
            IsAssert(model, node.Expression) is { } condition ? Check(condition) : base.VisitExpressionStatement(node);

        public override SyntaxNode? VisitCastExpression(CastExpressionSyntax node)
        {
            var visited = (CastExpressionSyntax)base.VisitCastExpression(node)!;
            bool inContext = node.Ancestors().TakeWhile(a => a is not MemberDeclarationSyntax)
                .Any(a => a is CheckedExpressionSyntax or CheckedStatementSyntax);
            if (inContext
                || model.GetOperation(node) is not Microsoft.CodeAnalysis.Operations.IConversionOperation conversion
                || conversion.GetConversion() is not { IsNumeric: true, IsExplicit: true })
            {
                return visited;
            }
            // unchecked((T)checked(e)): the conversion wraps, and the operand keeps the copy's checked context.
            var operand = SyntaxFactory.CheckedExpression(SyntaxKind.CheckedExpression, visited.Expression.WithoutTrivia());
            return SyntaxFactory.CheckedExpression(SyntaxKind.UncheckedExpression, visited.WithExpression(operand));
        }
    }
}
