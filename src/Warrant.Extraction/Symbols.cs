using System.Globalization;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Warrant.Vir;

namespace Warrant.Extraction;

/// <summary>What a type is to the M4 model.</summary>
internal enum TypeShape
{
    Other,
    Record,
    OpenEnum,
    ClosedEnum,
    ClosedClass,
}

/// <summary>Symbol helpers shared by the walker, the type checks and the scan.</summary>
internal static class Symbols
{
    public const string VerifiedAttribute = "Warrant.VerifiedAttribute";
    public const string TheoremAttribute = "Warrant.TheoremAttribute";
    public const string ClosedAttribute = "Warrant.ClosedAttribute";

    /// <summary>Lean's auxiliary constructions of an inductive type, which live in its namespace (KTD6).</summary>
    public static readonly string[] ReservedNames =
        ["rec", "recOn", "casesOn", "noConfusion", "noConfusionType", "below", "brecOn", "ctorIdx", "injEq"];

    public static bool Has(ISymbol symbol, string attribute) =>
        symbol.GetAttributes().Any(a => a.AttributeClass is { } c && c.ToDisplayString() == attribute);

    public static bool IsVerified(ISymbol symbol) => Has(symbol, VerifiedAttribute);

    public static bool IsTheorem(ISymbol symbol) => Has(symbol, TheoremAttribute);

    /// <summary>Whether an attribute class is <c>System.Runtime.CompilerServices.UnsafeAccessorAttribute</c> (#55).</summary>
    public static bool IsUnsafeAccessor(INamedTypeSymbol? attribute) =>
        attribute?.ToDisplayString() == "System.Runtime.CompilerServices.UnsafeAccessorAttribute";

    public static string Key(ISymbol symbol) =>
        symbol.GetDocumentationCommentId() ?? throw new InvalidOperationException($"'{symbol}' has no documentation-comment ID.");

    public static string Display(ISymbol symbol) => symbol.ToDisplayString(SymbolDisplayFormat.CSharpErrorMessageFormat);

    public static bool IsNamed(ISymbol symbol, string containingType, string name) =>
        symbol.Name == name && symbol.ContainingType is { } t && t.ToDisplayString() == containingType;

    public static TypeShape Shape(ITypeSymbol type)
    {
        if (type is not INamedTypeSymbol named)
        {
            return TypeShape.Other;
        }
        if (named.TypeKind == TypeKind.Enum)
        {
            return Has(named, ClosedAttribute) ? TypeShape.ClosedEnum : TypeShape.OpenEnum;
        }
        if (named.TypeKind == TypeKind.Class && Has(named, ClosedAttribute))
        {
            return TypeShape.ClosedClass;
        }
        if (named.IsRecord)
        {
            return TypeShape.Record;
        }
        return TypeShape.Other;
    }

    public static bool IsClosed(ITypeSymbol? type) =>
        type is not null && Shape(type) is TypeShape.ClosedEnum or TypeShape.ClosedClass;

    public static bool IsClosedEnum(ITypeSymbol? type) => type is not null && Shape(type) == TypeShape.ClosedEnum;

    /// <summary>A record class or closed class: a reference the CLR lets be null.</summary>
    public static bool IsNullableReference(ITypeSymbol type) =>
        Shape(type) switch
        {
            TypeShape.Record => type.IsReferenceType,
            TypeShape.ClosedClass => true,
            _ => false,
        };

    public static bool IsIntegral(ITypeSymbol? type) =>
        type is not null && type.SpecialType is SpecialType.System_SByte or SpecialType.System_Byte or SpecialType.System_Int16
            or SpecialType.System_UInt16 or SpecialType.System_Int32 or SpecialType.System_UInt32 or SpecialType.System_Int64
            or SpecialType.System_UInt64 or SpecialType.System_Char or SpecialType.System_IntPtr or SpecialType.System_UIntPtr;

    public static ITypeSymbol? UnwrapNullable(ITypeSymbol? type) =>
        type is INamedTypeSymbol { OriginalDefinition.SpecialType: SpecialType.System_Nullable_T } n ? n.TypeArguments[0] : type;

    /// <summary>The primary constructor of a positional record, or null.</summary>
    public static IMethodSymbol? PrimaryConstructor(INamedTypeSymbol record) =>
        record.InstanceConstructors.FirstOrDefault(c =>
            !c.IsImplicitlyDeclared && c.DeclaringSyntaxReferences.Any(r => r.GetSyntax() is RecordDeclarationSyntax));

    /// <summary>A positional property: the compiler's auto-property for a primary-constructor parameter.</summary>
    public static bool IsPositional(IPropertySymbol property) =>
        property.ContainingType.IsRecord
        && property.DeclaringSyntaxReferences.Length > 0
        && property.DeclaringSyntaxReferences.All(r => r.GetSyntax() is ParameterSyntax);

    /// <summary>The compiler's positional properties of a record, in primary-constructor order; null if a parameter has none.</summary>
    public static IReadOnlyList<IPropertySymbol>? PositionalProperties(INamedTypeSymbol record, IMethodSymbol primary)
    {
        var result = new List<IPropertySymbol>();
        foreach (var parameter in primary.Parameters)
        {
            var property = record.GetMembers(parameter.Name).OfType<IPropertySymbol>().FirstOrDefault(p => !p.IsStatic);
            if (property is null || !IsPositional(property))
            {
                return null;
            }
            result.Add(property);
        }
        return result;
    }

    public static VirPrimitive? Primitive(ITypeSymbol type) =>
        type.SpecialType switch
        {
            SpecialType.System_Boolean => VirPrimitive.Bool,
            SpecialType.System_Int32 => VirPrimitive.Int32,
            SpecialType.System_Int64 => VirPrimitive.Int64,
            _ => null,
        };

    public static VirType PrimitiveType(VirPrimitive p) =>
        p switch
        {
            VirPrimitive.Bool => VirType.Bool,
            VirPrimitive.Int32 => VirType.Int32,
            VirPrimitive.Int64 => VirType.Int64,
            _ => throw new ArgumentOutOfRangeException(nameof(p), p, "Only bool, int and long come from Primitive; Walker.MapType maps decimal itself."),
        };

    /// <summary>
    /// A constant as a long. A ulong above long.MaxValue wraps instead of throwing: only enums use such values, and an
    /// enum whose underlying type is not int or long is rejected when its type unit is built.
    /// </summary>
    public static long ToInt64(object value) =>
        value is ulong u ? unchecked((long)u) : Convert.ToInt64(value, CultureInfo.InvariantCulture);

    /// <summary>The span of a syntax node; lines and columns one-based, end exclusive.</summary>
    public static VirSpan Span(SyntaxNode node) => Span(node.GetLocation())!;

    public static VirSpan? Span(Location location)
    {
        if (!location.IsInSource)
        {
            return null;
        }
        var line = location.GetLineSpan();
        return new VirSpan(
            line.Path,
            line.StartLinePosition.Line + 1,
            line.StartLinePosition.Character + 1,
            line.EndLinePosition.Line + 1,
            line.EndLinePosition.Character + 1);
    }

    /// <summary>The first source location of a symbol, by path and then position, so partial declarations order deterministically.</summary>
    public static Location? FirstLocation(ISymbol symbol) =>
        symbol.Locations
            .Where(l => l.IsInSource)
            .OrderBy(l => l.SourceTree!.FilePath, StringComparer.Ordinal)
            .ThenBy(l => l.SourceSpan.Start)
            .FirstOrDefault();

    /// <summary>Orders symbols by their first source location: file path (ordinal), then position.</summary>
    public static int CompareByLocation(ISymbol a, ISymbol b)
    {
        var la = FirstLocation(a);
        var lb = FirstLocation(b);
        int c = string.CompareOrdinal(la?.SourceTree?.FilePath, lb?.SourceTree?.FilePath);
        return c != 0 ? c : (la?.SourceSpan.Start ?? 0).CompareTo(lb?.SourceSpan.Start ?? 0);
    }
}

/// <summary>Reference identity, for maps keyed by VIR node instances (whose records compare by value).</summary>
internal sealed class ReferenceComparer : IEqualityComparer<object>
{
    public static readonly ReferenceComparer Instance = new();

    public new bool Equals(object? x, object? y) => ReferenceEquals(x, y);

    public int GetHashCode(object obj) => System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(obj);
}

/// <summary>A rejection: the first construct outside the subset that a unit uses.</summary>
internal sealed class Rejection
{
    public Rejection(string id, string construct, Location? at, string message)
    {
        Id = id;
        Construct = construct;
        At = at;
        Message = message;
    }

    public string Id { get; }

    public string Construct { get; }

    public Location? At { get; }

    public string Message { get; }
}

/// <summary>Thrown inside a walk to stop at the first rejected construct.</summary>
#pragma warning disable CA1032, CA1064 // Internal control flow, never seen outside the walker.
internal sealed class RejectedException : Exception
#pragma warning restore CA1032, CA1064
{
    public RejectedException(Rejection rejection)
        : base(rejection.Message) => Rejection = rejection;

    public Rejection Rejection { get; }
}
