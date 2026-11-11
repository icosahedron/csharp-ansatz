using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Operations;
using Warrant.Vir;

namespace Warrant.Extraction;

/// <summary>
/// Nullable values (plan M6 KTD5, U17): <c>T?</c> is a value or null, read through the null tests, <c>??</c>, <c>Value</c>
/// and the non-null unwrap. A variable's nullability is its declaration's; Roslyn's flow state is never evidence, so a
/// <c>T?</c> value used where a <c>T</c> is required is an unwrap that throws on null, which the proof must rule out.
/// </summary>
internal sealed partial class Walker
{
    /// <summary>Whether a parameter is declared nullable (<c>Payment? p</c>); a value type's <c>T?</c> is its type instead.</summary>
    private static bool Annotated(IParameterSymbol parameter) => parameter.NullableAnnotation == NullableAnnotation.Annotated;

    /// <summary>Whether a property is declared nullable.</summary>
    private static bool Annotated(IPropertySymbol property) => property.NullableAnnotation == NullableAnnotation.Annotated;

    /// <summary>
    /// A value where one of type <paramref name="target"/> is required: wrapped when the target is its nullable form, and
    /// unwrapped (KTD5) when it is the nullable form of the target. A <c>null</c> literal cannot become a non-nullable value.
    /// Any other pair is left alone, for the caller's own checks.
    /// </summary>
    private VirExpr FitTo(VirExpr value, VirType target, SyntaxNode at)
    {
        if (value.Type == target)
        {
            return value;
        }
        if (target is NullableType wrapped && value.Type == wrapped.Value)
        {
            return Track(new ConvertExpr(value.Type, target, VirOverflow.Wrap, value), at);
        }
        if (value.Type is NullableType nullable && nullable.Value == target)
        {
            if (value is NullExpr)
            {
                throw Reject("null", at);
            }
            return Unwrap(target, UnwrapKind.NonNull, value, at);
        }
        return value;
    }

    /// <summary>
    /// A value where a reference of declared type <paramref name="declared"/> is required: a call argument, a returned value,
    /// a field of a record being built. Value types need nothing here, since Roslyn writes their conversions out.
    /// </summary>
    private VirExpr FitDeclared(VirExpr value, ITypeSymbol declared, bool annotated, SyntaxNode at)
    {
        if (!declared.IsReferenceType)
        {
            return value;
        }
        if (annotated)
        {
            return value.Type is RefType && Symbols.IsNullableReference(declared) ? FitTo(value, VirType.Nullable(value.Type), at) : value;
        }
        return value.Type is NullableType nullable ? FitTo(value, nullable.Value, at) : value;
    }

    /// <summary>The receiver of a member access or of <c>with</c>, which a null reference makes throw (KTD5).</summary>
    private VirExpr Dereferenced(IOperation receiver)
    {
        var value = Expr(receiver);
        return value.Type is NullableType nullable ? FitTo(value, nullable.Value, receiver.Syntax) : value;
    }

    /// <summary>
    /// The value inside a nullable value, which throws on null. A theorem statement is a <c>Prop</c> and cannot throw (KTD11),
    /// so there it is rejected, naming the read.
    /// </summary>
    private UnwrapExpr Unwrap(VirType type, UnwrapKind kind, VirExpr operand, SyntaxNode at)
    {
        if (_inTheorem)
        {
            throw Reject(kind == UnwrapKind.Value ? "nullable read" : "non-null unwrap", at, "it can throw, and a theorem statement cannot");
        }
        return Track(new UnwrapExpr(type, kind, operand), at);
    }

    /// <summary>
    /// The type of a conditional or switch expression over reference values: its own, or that type's nullable form when a
    /// branch may be null. Roslyn writes the value types' conversions out, so their branches already agree.
    /// </summary>
    private static VirType Join(VirType type, IEnumerable<VirExpr> branches) =>
        type is RefType && branches.Any(b => b.Type == VirType.Nullable(type)) ? VirType.Nullable(type) : type;

    /// <summary><c>x is null</c> (or, negated, <c>x is not null</c>, <c>x != null</c>, <c>x.HasValue</c>).</summary>
    /// <param name="value">The value tested.</param>
    /// <param name="negated">Whether the test is for not null.</param>
    /// <param name="nullSyntax">The <c>null</c> the value is compared with, where a non-nullable value is rejected.</param>
    /// <param name="syntax">The whole test.</param>
    private VirExpr NullTest(VirExpr value, bool negated, SyntaxNode nullSyntax, SyntaxNode syntax)
    {
        // A value declared non-nullable is assumed non-null, which would make the test constant (U17).
        if (value.Type is not NullableType)
        {
            throw Reject("null", nullSyntax);
        }
        var test = Track(new IsNullExpr(value), syntax);
        return negated ? Track(new NotExpr(test), syntax) : test;
    }

    /// <summary>The <c>null</c> of <c>is null</c> or <c>is not null</c>, and whether it is negated; null for any other pattern.</summary>
    private static (SyntaxNode Null, bool Negated)? NullPattern(IPatternOperation pattern) =>
        pattern switch
        {
            IConstantPatternOperation c when IsNullLiteral(c.Value) => (c.Value.Syntax, false),
            INegatedPatternOperation { Pattern: IConstantPatternOperation c } when IsNullLiteral(c.Value) => (c.Value.Syntax, true),
            _ => null,
        };

    /// <summary>Whether an operation is the constant <c>null</c>, possibly converted.</summary>
    private static bool IsNullLiteral(IOperation op) => op.ConstantValue is { HasValue: true, Value: null };

    /// <summary><c>null</c> converted to a nullable type: the null of that type.</summary>
    private NullExpr NullLiteral(IConversionOperation c)
    {
        var type = c.Type;
        if (type is INamedTypeSymbol { OriginalDefinition.SpecialType: SpecialType.System_Nullable_T })
        {
            return Track(new NullExpr(MapType(type, annotated: false, c.Syntax)), c.Syntax);
        }
        if (type is not null && Symbols.IsNullableReference(type))
        {
            return Track(new NullExpr(MapType(type, annotated: true, c.Syntax)), c.Syntax);
        }
        throw Reject("null", c.Syntax);
    }

    /// <summary>
    /// <c>x ?? y</c>: the value inside <c>x</c>, or <c>y</c> when <c>x</c> is null. The result is nullable exactly when
    /// <c>y</c> is; a value that is not nullable is never null, so it is rejected as a comparison with null would be.
    /// </summary>
    private CoalesceExpr Coalesce(ICoalesceOperation coalesce)
    {
        var syntax = coalesce.Syntax;
        var left = Expr(coalesce.Value);
        if (left.Type is not NullableType nullable)
        {
            throw Reject("null", coalesce.Value.Syntax);
        }
        var right = coalesce.WhenNull is IThrowOperation t ? ThrowExpression(t, nullable.Value) : Expr(coalesce.WhenNull);
        var type = right.Type is NullableType ? nullable : nullable.Value;
        right = FitTo(right, type, coalesce.WhenNull.Syntax);
        bool lifted = type is NullableType && coalesce.ValueConversion.IsNullable;
        if (right.Type != type || !(coalesce.ValueConversion.IsIdentity || lifted))
        {
            throw Reject("unsupported conversion", syntax);
        }
        return Track(new CoalesceExpr(type, left, right), syntax);
    }

    /// <summary>The value <c>GetValueOrDefault()</c> gives for null: <c>default(T)</c>.</summary>
    private static VirExpr DefaultOf(VirType type) =>
        type == VirType.Decimal ? DecimalLitExpr.Of(0m) : new LitExpr(type, 0);

    /// <summary>A switch's scrutinee, which may not be nullable: its patterns would be lifted comparisons.</summary>
    private static VirExpr NotNullableScrutinee(VirExpr scrutinee, SyntaxNode syntax) =>
        scrutinee.Type is NullableType ? throw Reject("switch on a nullable value", syntax) : scrutinee;

    /// <summary>The <c>!</c> that forgives this expression, if any: the node itself or its parent.</summary>
    private static SyntaxNode? Forgiving(SyntaxNode syntax) =>
        IsForgiving(syntax) ? syntax : syntax.Parent is { } parent && IsForgiving(parent) ? parent : null;

    private static bool IsForgiving(SyntaxNode syntax) =>
        syntax is PostfixUnaryExpressionSyntax && syntax.IsKind(SyntaxKind.SuppressNullableWarningExpression);
}
