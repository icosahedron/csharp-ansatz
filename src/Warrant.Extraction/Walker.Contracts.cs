using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Operations;
using Warrant.Vir;

namespace Warrant.Extraction;

/// <summary>
/// Contracts (plan M6 U8, KTD8, KTD16): the leading <c>Spec.Decreases</c>, <c>Spec.Requires</c> and <c>Spec.Ensures</c>
/// statements of a block body, in that order, and <c>Spec.Assert</c> wherever a statement may stand.
/// </summary>
internal sealed partial class Walker
{
    private const string SpecType = "Warrant.Spec";

    private static bool IsSpec(IInvocationOperation call, string name) => Symbols.IsNamed(call.TargetMethod, SpecType, name);

    /// <summary>The rank of a leading <c>Spec</c> statement: 0 for <c>Decreases</c>, 1 for <c>Requires</c>, 2 for <c>Ensures</c>.</summary>
    private static int? LeadingRank(IInvocationOperation call) =>
        IsDecreases(call) ? 0 : IsSpec(call, "Requires") ? 1 : IsSpec(call, "Ensures") ? 2 : null;

    /// <summary>
    /// One leading <c>Spec</c> statement, checked against its place: it must be in the body's prefix of such statements
    /// (<paramref name="leading"/>), and its rank must not be below the previous one's (<paramref name="last"/>).
    /// </summary>
    private VirStmt Leading(IInvocationOperation call, int rank, bool leading, int last, SyntaxNode at)
    {
        if (rank == 0)
        {
            if (!leading || last >= 0)
            {
                throw DecreasesNotFirst(at, outOfOrder: leading && last > 0);
            }
            return Track(new DecreasesStmt(Measure(call)), at);
        }
        var name = rank == 1 ? "Spec.Requires" : "Spec.Ensures";
        if (!leading)
        {
            throw new RejectedException(new Rejection(
                DiagnosticIds.Unsupported,
                $"{name} not leading the body",
                at.GetLocation(),
                $"{name} must lead the body: it goes at the start of the method's block body, after any Spec.Decreases"
                    + (rank == 2 ? " and Spec.Requires" : "") + " and before any other statement."));
        }
        if (rank < last)
        {
            throw new RejectedException(new Rejection(
                DiagnosticIds.Unsupported,
                "Spec.Requires after Spec.Ensures",
                at.GetLocation(),
                "Spec.Requires is out of order: the leading Spec statements are Spec.Decreases, then Spec.Requires, then Spec.Ensures."));
        }
        _claims++;
        try
        {
            return rank == 1
                ? Track(new RequiresStmt(Expr(call.Arguments[0].Value)), at)
                : Ensures(call, at);
        }
        finally
        {
            _claims--;
        }
    }

    /// <summary>
    /// <c>Spec.Ensures&lt;T&gt;(r =&gt; c)</c>, which binds the returned value, or <c>Spec.Ensures(() =&gt; c)</c>, which binds
    /// nothing (KTD8). <c>T</c> must be the declared return type, or the awaited type of a <c>Task&lt;T&gt;</c> or
    /// <c>ValueTask&lt;T&gt;</c>, nullable annotation included; the form without a result is for methods with no value.
    /// </summary>
    private EnsuresStmt Ensures(IInvocationOperation call, SyntaxNode at)
    {
        var target = call.TargetMethod;
        var expected = ResultType();
        bool bindsResult = target.IsGenericMethod;
        if (bindsResult)
        {
            var given = target.TypeArguments[0];
            bool givenAnnotated = target.TypeArgumentNullableAnnotations[0] == NullableAnnotation.Annotated;
            if (expected is not { } result)
            {
                throw new RejectedException(new Rejection(
                    DiagnosticIds.Unsupported,
                    "Spec.Ensures with a result on a method that returns none",
                    at.GetLocation(),
                    $"The method returns no value, so its postcondition binds none: write Spec.Ensures(() => ...), not Spec.Ensures<{TypeText(given, givenAnnotated)}>."));
            }
            var want = TypeText(result.Type, result.Annotated);
            if (!SymbolEqualityComparer.Default.Equals(given, result.Type) || (result.Type.IsReferenceType && givenAnnotated != result.Annotated))
            {
                throw new RejectedException(new Rejection(
                    DiagnosticIds.Unsupported,
                    "Spec.Ensures type argument that is not the return type",
                    at.GetLocation(),
                    $"Spec.Ensures<{TypeText(given, givenAnnotated)}> does not match the method's result, {want}: write Spec.Ensures<{want}>(r => ...)."));
            }
        }
        else if (expected is { } result)
        {
            var want = TypeText(result.Type, result.Annotated);
            throw new RejectedException(new Rejection(
                DiagnosticIds.Unsupported,
                "Spec.Ensures without the result",
                at.GetLocation(),
                $"The method returns {want}, so its postcondition binds the result: write Spec.Ensures<{want}>(r => ...)."));
        }

        if (call.Arguments[0].Value is not IDelegateCreationOperation { Target: IAnonymousFunctionOperation lambda })
        {
            throw new RejectedException(new Rejection(
                DiagnosticIds.MalformedSpec,
                "Spec.Ensures whose condition is not a lambda",
                call.Arguments[0].Syntax.GetLocation(),
                bindsResult
                    ? "The condition of Spec.Ensures must be a lambda over the result, such as r => r >= 0."
                    : "The condition of Spec.Ensures must be a lambda with no parameters, such as () => true."));
        }
        if (lambda.Body.Operations.Length != 1 || lambda.Body.Operations[0] is not IReturnOperation { ReturnedValue: { } condition })
        {
            throw Reject("lambda with statements", lambda.Syntax);
        }
        if (!bindsResult)
        {
            return Track(new EnsuresStmt(null, null, Expr(condition)), at);
        }
        // The result is read in the condition as the lambda's parameter, whose type the check above made the result's.
        var parameter = lambda.Symbol.Parameters[0];
        int local = _nextLocal++;
        _bound.Add(parameter, local);
        return Track(new EnsuresStmt(local, parameter.Name, Expr(condition)), at);
    }

    /// <summary>
    /// The type a method's postcondition speaks of: its declared return type, or the awaited type of a
    /// <c>Task&lt;T&gt;</c> or <c>ValueTask&lt;T&gt;</c>; null for <c>void</c>, <c>Task</c> and <c>ValueTask</c>.
    /// </summary>
    private (ITypeSymbol Type, bool Annotated)? ResultType()
    {
        if (_returns is not { } returns || returns.Type.SpecialType == SpecialType.System_Void)
        {
            return null;
        }
        var (type, annotated) = returns;
        if (type is INamedTypeSymbol named && named.ContainingNamespace?.ToDisplayString() == "System.Threading.Tasks"
            && named.Name is "Task" or "ValueTask")
        {
            if (named.TypeArguments.Length == 0)
            {
                return null;
            }
            return (named.TypeArguments[0], named.TypeArgumentNullableAnnotations[0] == NullableAnnotation.Annotated);
        }
        return (type, annotated);
    }

    private static string TypeText(ITypeSymbol type, bool annotated) =>
        Symbols.Display(type.WithNullableAnnotation(NullableAnnotation.NotAnnotated)) + (annotated && type.IsReferenceType ? "?" : "");

    /// <summary><c>Spec.Assert(c, script...)</c>: a check node at its position, with the tactics that prove it (KTD16).</summary>
    private AssertStmt Assert(IInvocationOperation call, SyntaxNode at)
    {
        VirExpr condition;
        _claims++;
        try
        {
            condition = Expr(call.Arguments[0].Value);
        }
        finally
        {
            _claims--;
        }
        var script = AssertScript(call.Arguments.Where(a => a.Parameter?.Ordinal > 0));
        return Track(new AssertStmt(condition, script), at);
    }

    /// <summary>
    /// A <c>Spec.Requires</c>, <c>Spec.Ensures</c> or <c>Spec.Assert</c> call that is not a statement of a block body:
    /// an expression-bodied member's body, which takes no contract in M6 (design Q17), or a nested expression.
    /// </summary>
    private static RejectedException ContractNotAStatement(IInvocationOperation call)
    {
        var name = "Spec." + call.TargetMethod.Name;
        var syntax = call.Syntax;
        if (syntax.Parent is ArrowExpressionClauseSyntax)
        {
            return new RejectedException(new Rejection(
                DiagnosticIds.Unsupported,
                $"{name} in an expression-bodied member",
                syntax.GetLocation(),
                $"An expression-bodied member takes no contract: write the body as a block, {{ {name}(...); ... }}."));
        }
        return name == "Spec.Assert"
            ? Reject("Spec.Assert outside a statement", syntax)
            : new RejectedException(new Rejection(
                DiagnosticIds.Unsupported,
                $"{name} not leading the body",
                syntax.GetLocation(),
                $"{name} must lead the body: it goes at the start of the method's block body, as a statement of its own."));
    }
}
