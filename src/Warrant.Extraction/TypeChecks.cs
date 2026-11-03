using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Operations;
using Warrant.Vir;

namespace Warrant.Extraction;

/// <summary>A type unit's definition, or why it is rejected.</summary>
internal sealed class TypeBuild
{
    public TypeBuild(INamedTypeSymbol symbol, SortedSet<string> deps)
    {
        Symbol = symbol;
        Deps = deps;
    }

    public INamedTypeSymbol Symbol { get; }

    public SortedSet<string> Deps { get; }

    public VirDefinition? Definition { get; set; }

    public Rejection? Rejection { get; set; }

    /// <summary>For a closed class: whether it or a base class has its own equality (KTD11).</summary>
    public bool OwnEquality { get; set; }
}

/// <summary>
/// The checks on records, enums and closed types (docs/m4/03, "Records" and "Closed types"), and their definitions.
/// </summary>
internal static class TypeChecks
{
    public static TypeBuild Build(ExtractionContext context, CompilationScan scan, INamedTypeSymbol type)
    {
        var walker = new Walker(context, inTheorem: false);
        var build = new TypeBuild(type, walker.Deps);
        try
        {
            build.Definition = Symbols.Shape(type) switch
            {
                TypeShape.Record => Record(walker, type),
                TypeShape.OpenEnum => OpenEnum(type),
                TypeShape.ClosedEnum => ClosedEnum(type),
                TypeShape.ClosedClass => ClosedClass(context, scan, type, build),
                _ => throw new InvalidOperationException($"'{type}' has no type unit."),
            };
        }
        catch (RejectedException e)
        {
            build.Rejection = e.Rejection;
        }
        build.Deps.Remove(Symbols.Key(type));
        return build;
    }

    private static RejectedException Reject(INamedTypeSymbol type, string construct, string id = DiagnosticIds.Unsupported, Location? at = null) =>
        new(new Rejection(
            id,
            construct,
            at ?? Symbols.FirstLocation(type),
            id == DiagnosticIds.NotClosedShape
                ? $"{Symbols.Display(type)} is [Closed] but does not have the closed shape: {construct}."
                : $"{Symbols.Display(type)}: M4 does not support {construct}."));

    private static void ReservedNames(INamedTypeSymbol type)
    {
        if (type.GetMembers().Any(m => Symbols.ReservedNames.Contains(m.Name, StringComparer.Ordinal)))
        {
            throw Reject(type, "reserved member name");
        }
    }

    private static RecordDefinition Record(Walker walker, INamedTypeSymbol type)
    {
        if (type.TypeKind == TypeKind.Struct)
        {
            throw Reject(type, "record struct");
        }
        if (!type.IsSealed)
        {
            throw Reject(type, "unsealed record");
        }
        if (type.IsGenericType)
        {
            throw Reject(type, "generic type");
        }
        if (type.BaseType is { SpecialType: not SpecialType.System_Object })
        {
            throw Reject(type, "record with a base record");
        }
        var primary = Symbols.PrimaryConstructor(type) ?? throw Reject(type, "record that is not positional");
        ReservedNames(type);

        // A user-written equality member makes == mean something other than field-by-field equality (KTD10).
        bool ownEquality = type.GetMembers().Any(m => !m.IsImplicitlyDeclared && m switch
        {
            IMethodSymbol { Name: "Equals", Parameters.Length: 1 } => true,
            IMethodSymbol { Name: "GetHashCode", Parameters.Length: 0 } => true,
            IMethodSymbol { Name: "op_Equality" or "op_Inequality" } => true,
            IPropertySymbol { Name: "EqualityContract" } => true,
            _ => false,
        });
        if (ownEquality)
        {
            throw Reject(type, "record with its own equality");
        }

        // `with` runs the copy constructor; the model copies the fields, which only the compiler's copy constructor does.
        bool ownCopy = type.InstanceConstructors.Any(c => !c.IsImplicitlyDeclared
            && c.Parameters.Length == 1
            && SymbolEqualityComparer.Default.Equals(c.Parameters[0].Type, type));
        if (ownCopy)
        {
            throw Reject(type, "record with its own copy constructor");
        }
        var properties = Symbols.PositionalProperties(type, primary)
            ?? throw Reject(type, "positional property that is not the compiler's auto-property");

        // The generated Equals compares every instance field, so other state would make the model's equality differ.
        bool otherState = type.GetMembers().Any(m => !m.IsStatic && m switch
        {
            IFieldSymbol { IsConst: false } f => f.AssociatedSymbol is not IPropertySymbol p || !Symbols.IsPositional(p),
            IEventSymbol => true,
            _ => false,
        });
        if (otherState)
        {
            throw Reject(type, "record with other instance state");
        }

        var fields = new List<VirField>();
        foreach (var property in properties)
        {
            var at = property.DeclaringSyntaxReferences[0].GetSyntax();
            var fieldType = walker.MapType(property.Type, property.NullableAnnotation == NullableAnnotation.Annotated, at);
            fields.Add(new VirField(property.Name, fieldType));
        }
        return new RecordDefinition(new VirList<VirField>(fields));
    }

    private static PrimitiveType Underlying(INamedTypeSymbol type)
    {
        switch (type.EnumUnderlyingType?.SpecialType)
        {
            case SpecialType.System_Int32:
                return VirType.Int32;
            case SpecialType.System_Int64:
                return VirType.Int64;
            default:
                throw Reject(type, "enum with an underlying type other than int or long");
        }
    }

    private static IEnumerable<IFieldSymbol> EnumMembers(INamedTypeSymbol type) =>
        type.GetMembers().OfType<IFieldSymbol>().Where(f => f.HasConstantValue);

    private static EnumDefinition OpenEnum(INamedTypeSymbol type)
    {
        var underlying = Underlying(type);
        var members = EnumMembers(type).Select(f => new VirEnumMember(f.Name, Symbols.ToInt64(f.ConstantValue!)));
        return new EnumDefinition(underlying, new VirList<VirEnumMember>(members));
    }

    private static ClosedDefinition ClosedEnum(INamedTypeSymbol type)
    {
        Underlying(type);
        ReservedNames(type);
        var members = EnumMembers(type).Select(f => new VirClosedMember(f.Name, Symbols.ToInt64(f.ConstantValue!))).ToList();

        // Two members with one value would be two constructors the kernel proves different (KTD9).
        if (members.Select(m => m.Value).Distinct().Count() != members.Count)
        {
            throw Reject(type, "closed enum with duplicate values");
        }
        return new ClosedDefinition(new VirList<VirClosedMember>(members));
    }

    /// <summary>Whether a closed enum has a member valued 0, the value of <c>default</c>.</summary>
    public static bool HasZero(INamedTypeSymbol closedEnum) =>
        EnumMembers(closedEnum).Any(f => Symbols.ToInt64(f.ConstantValue!) == 0);

    /// <summary>The closed shape (design D13), checked in docs/m4/03's five steps; a failure is WRT0009 naming the step.</summary>
    private static ClosedDefinition ClosedClass(ExtractionContext context, CompilationScan scan, INamedTypeSymbol type, TypeBuild build)
    {
        // 1. Sealed.
        if (!type.IsSealed)
        {
            throw Reject(type, "not sealed", DiagnosticIds.NotClosedShape);
        }

        // 2. Every instance constructor private, and no primary constructor.
        bool primary = type.DeclaringSyntaxReferences.Any(r => r.GetSyntax() is TypeDeclarationSyntax { ParameterList: not null });
        if (primary || type.InstanceConstructors.Any(c => c.DeclaredAccessibility != Accessibility.Private))
        {
            throw Reject(type, "constructor that is not private", DiagnosticIds.NotClosedShape);
        }

        // 3. Every static member of the class's own type is an initialised get-only auto-property or static readonly field,
        //    whose initialiser creates an instance; anything else could return a different object on each read.
        var instances = new List<ISymbol>();
        var allowed = new HashSet<(SyntaxTree, int, int)>();
        foreach (var member in type.GetMembers().Where(m => m.IsStatic && !m.IsImplicitlyDeclared))
        {
            var memberType = member switch
            {
                IFieldSymbol f => f.Type,
                IPropertySymbol p => p.Type,
                _ => null,
            };
            if (memberType is null || !SymbolEqualityComparer.Default.Equals(memberType, type))
            {
                continue;
            }
            var initializer = StaticInstanceInitializer(member);
            var creation = initializer is null ? null : Creation(context, initializer, type);
            if (creation is null)
            {
                throw Reject(
                    type,
                    "static instance that is not an initialised get-only auto-property or readonly field",
                    DiagnosticIds.NotClosedShape);
            }
            allowed.Add((creation.SyntaxTree, creation.SpanStart, creation.Span.Length));
            instances.Add(member);
        }

        //    A static constructor runs after the initialisers and could make two instances one object, or throw.
        if (type.StaticConstructors.Any(c => !c.IsImplicitlyDeclared))
        {
            throw Reject(type, "static constructor", DiagnosticIds.NotClosedShape);
        }

        // 4. The constructors are called nowhere else.
        foreach (var creation in scan.Creations)
        {
            if (SymbolEqualityComparer.Default.Equals(creation.Constructor?.ContainingType, type)
                && !allowed.Contains((creation.Syntax.SyntaxTree, creation.Syntax.SpanStart, creation.Syntax.Span.Length)))
            {
                throw Reject(type, "constructor called outside the static instances", DiagnosticIds.NotClosedShape, creation.Syntax.GetLocation());
            }
        }

        // 5. At least one instance.
        if (instances.Count == 0)
        {
            throw Reject(type, "no static instances", DiagnosticIds.NotClosedShape);
        }

        ReservedNames(type);
        build.OwnEquality = HasOwnEquality(type);

        // Declaration order; for partial classes, by file path and then position.
        instances.Sort(Symbols.CompareByLocation);
        return new ClosedDefinition(new VirList<VirClosedMember>(instances.Select(m => new VirClosedMember(m.Name, null))));
    }

    /// <summary>The initialiser of a get-only auto-property or a static readonly field, or null if the member is neither.</summary>
    private static ExpressionSyntax? StaticInstanceInitializer(ISymbol member)
    {
        var syntax = member.DeclaringSyntaxReferences.Length == 1 ? member.DeclaringSyntaxReferences[0].GetSyntax() : null;
        switch (member)
        {
            case IPropertySymbol { SetMethod: null } when syntax is PropertyDeclarationSyntax
            {
                ExpressionBody: null,
                AccessorList: { } accessors,
                Initializer: { } init,
            } && accessors.Accessors.All(a => a.Body is null && a.ExpressionBody is null):
                return init.Value;
            case IFieldSymbol { IsReadOnly: true } when syntax is VariableDeclaratorSyntax { Initializer: { } init }:
                return init.Value;
            default:
                return null;
        }
    }

    /// <summary>The syntax of the object creation an initialiser consists of, if it creates an instance of the type.</summary>
    private static SyntaxNode? Creation(ExtractionContext context, ExpressionSyntax initializer, INamedTypeSymbol type)
    {
        var op = context.Model(initializer.SyntaxTree).GetOperation(initializer);
        while (op is IConversionOperation { IsImplicit: true } c)
        {
            op = c.Operand;
        }
        return op is IObjectCreationOperation { Constructor: { } ctor } creation
            && SymbolEqualityComparer.Default.Equals(ctor.ContainingType, type)
            ? creation.Syntax
            : null;
    }

    /// <summary>Whether the class or a base class overrides <c>Equals</c>, defines <c>==</c>, or implements <c>IEquatable&lt;T&gt;</c>.</summary>
    public static bool HasOwnEquality(INamedTypeSymbol type)
    {
        for (var t = type; t is not null && t.SpecialType != SpecialType.System_Object; t = t.BaseType)
        {
            bool own = t.GetMembers().Any(m => !m.IsImplicitlyDeclared && m is IMethodSymbol
            {
                Name: "Equals" or "op_Equality" or "op_Inequality",
            });
            if (own)
            {
                return true;
            }
        }
        return type.AllInterfaces.Any(i => i.OriginalDefinition.ToDisplayString() == "System.IEquatable<T>");
    }
}
