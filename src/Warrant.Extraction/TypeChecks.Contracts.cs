using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace Warrant.Extraction;

/// <summary>The contract shape of a <c>[ContractFor]</c> class (plan M6 KTD10).</summary>
internal static partial class TypeChecks
{
    private static readonly SymbolDisplayFormat WithNullability =
        SymbolDisplayFormat.FullyQualifiedFormat.AddMiscellaneousOptions(SymbolDisplayMiscellaneousOptions.IncludeNullableReferenceTypeModifier);

    /// <summary>
    /// Checks a <c>[ContractFor(typeof(I))]</c> class against the contract shape, in KTD10's steps, so a contract cannot
    /// hide code that would run: it names an interface; it is <c>file</c> or <c>internal</c>, <c>abstract</c> and not
    /// generic; it implements exactly <c>I</c> (with the interfaces <c>I</c> inherits) on top of <c>object</c>; each member
    /// it declares implements a member of those interfaces with the same nullability; and each member's body is
    /// <c>Spec.Requires</c>/<c>Spec.Ensures</c> calls then <c>return default!</c>, those calls alone for a <c>void</c>
    /// member, <c>=&gt; default!</c>, or none (<c>abstract</c>). The <c>Spec</c> conditions themselves are read only when a
    /// verified call uses the member, so a member whose signature has an unmodelled type is allowed until then.
    /// </summary>
    /// <param name="compilation">The class's compilation.</param>
    /// <param name="type">The class.</param>
    /// <param name="cancellationToken">Cancels the check.</param>
    /// <returns>The first step it fails, or null when it has the shape.</returns>
    public static Rejection? ContractShape(Compilation compilation, INamedTypeSymbol type, CancellationToken cancellationToken)
    {
        if (ContractIndex.Interface(type) is not { TypeKind: TypeKind.Interface } @interface)
        {
            return NotContractShape(type, "[ContractFor] of a type that is not an interface", null);
        }
        if (type.DeclaredAccessibility != Accessibility.Internal)
        {
            return NotContractShape(type, "contract class that is not file or internal", null);
        }
        if (type.TypeKind != TypeKind.Class || !type.IsAbstract || type.IsStatic)
        {
            return NotContractShape(type, "contract class that is not abstract", null);
        }
        if (type.IsGenericType)
        {
            return NotContractShape(type, "generic contract class", null);
        }
        var expected = new HashSet<INamedTypeSymbol>(@interface.AllInterfaces, SymbolEqualityComparer.Default) { @interface };
        if (type.BaseType?.SpecialType != SpecialType.System_Object || type.IsRecord || !expected.SetEquals(type.AllInterfaces))
        {
            return NotContractShape(type, "contract class that does not implement exactly its interface", null);
        }

        var interfaceMembers = expected.SelectMany(i => i.GetMembers()).Where(m => !m.IsStatic).ToList();
        var members = type.GetMembers()
            .Where(m => !m.IsImplicitlyDeclared
                && m is not IMethodSymbol { MethodKind: MethodKind.PropertyGet or MethodKind.PropertySet or MethodKind.EventAdd or MethodKind.EventRemove })
            .ToList();
        members.Sort(Symbols.CompareByLocation);
        foreach (var member in members)
        {
            cancellationToken.ThrowIfCancellationRequested();
            var implemented = interfaceMembers.FirstOrDefault(m => SymbolEqualityComparer.Default.Equals(type.FindImplementationForInterfaceMember(m), member));
            if (implemented is null)
            {
                return NotContractShape(type, "contract class member that is not a member of its interface", member);
            }
            if (!SameNullability(member, implemented))
            {
                return NotContractShape(type, "contract member whose nullability differs from its interface", member);
            }
            if (NoThrowIn(compilation, member, cancellationToken) is { } noThrow)
            {
                return new Rejection(
                    DiagnosticIds.Unsupported,
                    "Spec.NoThrow in a contract member",
                    noThrow,
                    $"{Symbols.Display(member)} calls Spec.NoThrow, which a [ContractFor] class does not take: Spec.NoThrow is for a verified method's own body, where it states that no explicit throw is reachable under the Requires, and an exception from a dependency is always allowed (#182).");
            }
            if (!ContractBody(compilation, member, cancellationToken))
            {
                return NotContractShape(type, "contract member body other than Spec calls and return default!", member);
            }
        }
        return null;
    }

    private static Rejection NotContractShape(INamedTypeSymbol type, string construct, ISymbol? member) =>
        new(
            DiagnosticIds.Unsupported,
            construct,
            Symbols.FirstLocation(member ?? type),
            $"{Symbols.Display(type)} is a [ContractFor] class but does not have the contract shape: {construct}"
                + (member is null ? "." : $" ({Symbols.Display(member)})."));

    /// <summary>Whether a contract member's signature has its interface member's nullable annotations, which callers rely on.</summary>
    private static bool SameNullability(ISymbol member, ISymbol implemented)
    {
        static string Show(ITypeSymbol t) => t.ToDisplayString(WithNullability);
        return (member, implemented) switch
        {
            (IMethodSymbol m, IMethodSymbol i) => Show(m.ReturnType) == Show(i.ReturnType)
                && m.Parameters.Length == i.Parameters.Length
                && m.Parameters.Zip(i.Parameters, (a, b) => Show(a.Type) == Show(b.Type)).All(same => same),
            (IPropertySymbol m, IPropertySymbol i) => Show(m.Type) == Show(i.Type),
            (IEventSymbol m, IEventSymbol i) => Show(m.Type) == Show(i.Type),
            _ => false,
        };
    }

    /// <summary>
    /// Whether a contract member's body assumes only what its <c>Spec</c> calls say: <c>abstract</c>; <c>=&gt; default!</c>;
    /// or a block of <c>Spec.Requires</c> and <c>Spec.Ensures</c> statements followed, unless the member is <c>void</c>, by
    /// <c>return default!;</c>. A property or event is <c>abstract</c> or <c>=&gt; default!</c>.
    /// </summary>
    private static bool ContractBody(Compilation compilation, ISymbol member, CancellationToken cancellationToken)
    {
        if (member.IsAbstract)
        {
            return true;
        }
        var syntax = member.DeclaringSyntaxReferences.Select(r => r.GetSyntax(cancellationToken)).FirstOrDefault();
        switch (member, syntax)
        {
            case (IMethodSymbol method, MethodDeclarationSyntax { ExpressionBody: { } arrow }):
                return !method.ReturnsVoid && IsDefaultForgiven(arrow.Expression);
            case (IMethodSymbol method, MethodDeclarationSyntax { Body: { } block }):
                {
                    var model = compilation.GetSemanticModel(block.SyntaxTree);
                    int specs = block.Statements.TakeWhile(s => IsContractSpec(model, s, cancellationToken)).Count();
                    var rest = block.Statements.Skip(specs).ToList();
                    return method.ReturnsVoid
                        ? rest.Count == 0
                        : rest.Count == 1 && rest[0] is ReturnStatementSyntax { Expression: { } returned } && IsDefaultForgiven(returned);
                }
            case (IPropertySymbol, BasePropertyDeclarationSyntax property):
                return property switch
                {
                    PropertyDeclarationSyntax { ExpressionBody: { } arrow } => IsDefaultForgiven(arrow.Expression),
                    IndexerDeclarationSyntax { ExpressionBody: { } arrow } => IsDefaultForgiven(arrow.Expression),
                    _ => property.AccessorList is { Accessors.Count: 1 } accessors
                        && accessors.Accessors[0] is { ExpressionBody: { } getter } accessor
                        && accessor.IsKind(SyntaxKind.GetAccessorDeclaration)
                        && IsDefaultForgiven(getter.Expression),
                };
            default:
                return false;
        }
    }

    /// <summary>The location of a <c>Spec.NoThrow()</c> statement in a contract member's block body; null when it has none (#182).</summary>
    private static Location? NoThrowIn(Compilation compilation, ISymbol member, CancellationToken cancellationToken)
    {
        if (member.DeclaringSyntaxReferences.Select(r => r.GetSyntax(cancellationToken)).FirstOrDefault() is not MethodDeclarationSyntax { Body: { } block })
        {
            return null;
        }
        var model = compilation.GetSemanticModel(block.SyntaxTree);
        return block.Statements
            .FirstOrDefault(s => s is ExpressionStatementSyntax { Expression: InvocationExpressionSyntax call }
                && model.GetSymbolInfo(call, cancellationToken).Symbol is IMethodSymbol target
                && Symbols.IsNamed(target, "Warrant.Spec", "NoThrow"))
            ?.GetLocation();
    }

    /// <summary>A statement <c>Spec.Requires(...)</c> or <c>Spec.Ensures(...)</c>.</summary>
    private static bool IsContractSpec(SemanticModel model, StatementSyntax statement, CancellationToken cancellationToken) =>
        statement is ExpressionStatementSyntax { Expression: InvocationExpressionSyntax call }
        && model.GetSymbolInfo(call, cancellationToken).Symbol is IMethodSymbol target
        && (Symbols.IsNamed(target, "Warrant.Spec", "Requires") || Symbols.IsNamed(target, "Warrant.Spec", "Ensures"));

    /// <summary><c>default!</c> or <c>default(T)!</c>: a value that assumes nothing, which a contract member never runs.</summary>
    private static bool IsDefaultForgiven(ExpressionSyntax expression) =>
        expression is PostfixUnaryExpressionSyntax { Operand: var operand } forgiving
        && forgiving.IsKind(SyntaxKind.SuppressNullableWarningExpression)
        && (operand.IsKind(SyntaxKind.DefaultLiteralExpression) || operand is DefaultExpressionSyntax);
}
