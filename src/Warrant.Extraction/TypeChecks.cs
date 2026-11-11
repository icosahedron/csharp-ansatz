using System.Collections.Immutable;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
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
internal static partial class TypeChecks
{
    public static TypeBuild Build(ExtractionContext context, Lazy<CompilationScan> scan, INamedTypeSymbol type)
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

        // A user-written equality member makes == mean something other than field-by-field equality (KTD10). An explicit
        // IEquatable<T>.Equals is one (#132): its name is the interface member's qualified name, and it is what
        // EqualityComparer<T>.Default calls when an enclosing record's generated Equals compares a field of this type.
        bool ownEquality = type.GetMembers().Any(m => !m.IsImplicitlyDeclared && m switch
        {
            IMethodSymbol { Name: "Equals", Parameters.Length: 1 } => true,
            IMethodSymbol { ExplicitInterfaceImplementations: { IsEmpty: false } implemented } => implemented.Any(IsEquatableEquals),
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

            // The model's $eq compares a closed-class field by instance, but the generated Equals calls
            // EqualityComparer<T>.Default.Equals, which reaches the class's own equality (#25).
            if (property.Type is INamedTypeSymbol fieldClass && Symbols.Shape(fieldClass) == TypeShape.ClosedClass && HasOwnEquality(fieldClass))
            {
                throw Reject(type, "record field of a closed class with its own equality", at: at.GetLocation());
            }
            var fieldType = walker.MapType(property.Type, property.NullableAnnotation == NullableAnnotation.Annotated, at);
            fields.Add(new VirField(property.Name, fieldType));
        }
        return new RecordDefinition(new VirList<VirField>(fields));
    }

    /// <summary>Whether <paramref name="method"/> is <c>System.IEquatable&lt;T&gt;.Equals</c>, for any <c>T</c>.</summary>
    private static bool IsEquatableEquals(IMethodSymbol method) =>
        method.ContainingType.OriginalDefinition is
        {
            MetadataName: "IEquatable`1",
            ContainingNamespace: { Name: "System", ContainingNamespace.IsGlobalNamespace: true },
        };

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
    private static ClosedDefinition ClosedClass(ExtractionContext context, Lazy<CompilationScan> scan, INamedTypeSymbol type, TypeBuild build)
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
        var creations = new List<IObjectCreationOperation>();
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
            allowed.Add((creation.Syntax.SyntaxTree, creation.Syntax.SpanStart, creation.Syntax.Span.Length));
            creations.Add(creation);
            instances.Add(member);
        }

        //    A static constructor runs after the initialisers and could make two instances one object, or throw.
        if (type.StaticConstructors.Any(c => !c.IsImplicitlyDeclared))
        {
            throw Reject(type, "static constructor", DiagnosticIds.NotClosedShape);
        }

        //    Creating the instances cannot throw. If it could, the type initialiser would fail and every use of the class
        //    would throw TypeInitializationException, while the model still has the instances (#24).
        if (ConstructionCouldThrow(context, type, creations, allowed) is { } throwing)
        {
            throw Reject(type, "constructor or initialiser that could throw", DiagnosticIds.NotClosedShape, throwing.GetLocation());
        }

        // 4. The constructors are called nowhere else.
        foreach (var creation in scan.Value.Creations)
        {
            if (SymbolEqualityComparer.Default.Equals(creation.Constructor?.ContainingType, type)
                && !allowed.Contains((creation.Syntax.SyntaxTree, creation.Syntax.SpanStart, creation.Syntax.Span.Length)))
            {
                throw Reject(type, "constructor called outside the static instances", DiagnosticIds.NotClosedShape, creation.Syntax.GetLocation());
            }
        }

        //    Nor is an instance created, or a static instance replaced, without one where Warrant can see it (#55):
        //    MemberwiseClone written in the class or a base class (the only places that can call it on an instance), a
        //    with expression, or an [UnsafeAccessor] that calls a constructor or MemberwiseClone or reaches a field.
        //    Reflection, serializers and code Warrant does not see are the closed assumption's.
        if (CreatedWithoutConstructor(type, scan.Value) is { } bypass)
        {
            throw Reject(type, "instance created or changed without a constructor call", DiagnosticIds.NotClosedShape, bypass.GetLocation());
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

    /// <summary>
    /// The first place that can create an instance of a closed class without calling its constructor, or change one of its
    /// static instances, or null (#55):
    /// <list type="bullet">
    /// <item><see cref="object.MemberwiseClone"/>, called or named as a method group, written in the class or a base class
    /// (whatever the receiver: <c>base.</c>, a type parameter, a nested type's outer instance), or on a receiver of the
    /// class or a base class;</item>
    /// <item>a <c>with</c> expression on the class or a base class;</item>
    /// <item>an <c>[UnsafeAccessor]</c> that calls a constructor of anything but a named type outside the lineage (an
    /// <c>object</c> or <c>dynamic</c> return can be pointed anywhere by <c>[UnsafeAccessorType]</c>), that calls
    /// <see cref="object.MemberwiseClone"/>, or that reaches a field through a lineage, <c>object</c> or <c>dynamic</c>
    /// type, since a field accessor can make two static instances one object; or one whose kind is unknown.</item>
    /// </list>
    /// </summary>
    private static SyntaxNode? CreatedWithoutConstructor(INamedTypeSymbol type, CompilationScan scan)
    {
        // By documentation-comment ID: the compilation being verified sees a referenced class as metadata, a different symbol
        // from the one its recorded source declares (#32), and the ID names it uniquely there.
        var lineage = new HashSet<string>(StringComparer.Ordinal);
        for (var t = type; t is not null && t.SpecialType != SpecialType.System_Object; t = t.BaseType)
        {
            lineage.Add(Symbols.Key(t.OriginalDefinition));
        }
        bool InLineage(ITypeSymbol? t) => t is INamedTypeSymbol n && lineage.Contains(Symbols.Key(n.OriginalDefinition));
        bool Unnamed(ITypeSymbol t) => t.SpecialType == SpecialType.System_Object || t.TypeKind is TypeKind.Dynamic or TypeKind.TypeParameter;

        var candidates = new List<SyntaxNode>();
        candidates.AddRange(scan.MemberwiseClones
            .Where(c => InLineage(c.Receiver) || c.EnclosingTypes.Any(InLineage))
            .Select(c => c.Syntax));
        candidates.AddRange(scan.Withs.Where(w => InLineage(w.Type)).Select(w => w.Syntax));
        foreach (var (method, syntax) in scan.UnsafeAccessors)
        {
            var attribute = method.GetAttributes().First(a => Symbols.IsUnsafeAccessor(a.AttributeClass));
            var kind = attribute.ConstructorArguments.Length == 1 && attribute.ConstructorArguments[0].Value is int k ? k : -1;
            var name = attribute.NamedArguments.FirstOrDefault(a => a.Key == "Name").Value.Value as string ?? method.Name;
            const int Constructor = 0, Method = 1, StaticMethod = 2, Field = 3, StaticField = 4;
            var signature = method.Parameters.Select(p => p.Type).Append(method.ReturnType).ToList();
            bool constructs = kind == Constructor && (InLineage(method.ReturnType) || Unnamed(method.ReturnType) || method.ReturnType is not INamedTypeSymbol);
            bool clones = kind is Method or StaticMethod && name == nameof(MemberwiseClone);
            bool reachesField = kind is Field or StaticField && signature.Any(t => InLineage(t) || Unnamed(t));
            if (constructs || clones || reachesField || kind is < Constructor or > StaticField)
            {
                candidates.Add(syntax);
            }
        }
        return candidates.OrderBy(n => n.SyntaxTree.FilePath, StringComparer.Ordinal).ThenBy(n => n.SpanStart).FirstOrDefault();
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
            } && HasOnlyAutoAccessors(accessors):
                return init.Value;
            case IFieldSymbol { IsReadOnly: true } when syntax is VariableDeclaratorSyntax { Initializer: { } init }:
                return init.Value;
            default:
                return null;
        }
    }

    /// <summary>The object creation an initialiser consists of, if it creates an instance of the type.</summary>
    private static IObjectCreationOperation? Creation(ExtractionContext context, ExpressionSyntax initializer, INamedTypeSymbol type)
    {
        // C# has no operation for parentheses, so they are removed first (#126).
        var expression = initializer;
        while (expression is ParenthesizedExpressionSyntax parenthesized)
        {
            expression = parenthesized.Expression;
        }
        var op = context.Model(expression.SyntaxTree).GetOperation(expression);
        while (op is IConversionOperation { IsImplicit: true } c)
        {
            op = c.Operand;
        }
        return op is IObjectCreationOperation { Constructor: { } ctor } creation
            && SymbolEqualityComparer.Default.Equals(ctor.ContainingType, type)
            ? creation
            : null;
    }

    /// <summary>
    /// The first piece of code that runs while a closed class's instances are created and that could throw, or null if
    /// there is none (#24). Only this is allowed, on the class and on each of its base classes:
    /// <list type="bullet">
    /// <item>the static instances' creations, with constant arguments and no object initialiser;</item>
    /// <item>every other static initialiser of the class itself a constant, and every instance initialiser a constant or a
    /// primary-constructor parameter;</item>
    /// <item>
    /// every instance constructor, a <c>this(...)</c> or <c>base(...)</c> call whose arguments are constants or parameters,
    /// and a body of assignments of constants or parameters to the class's own fields and auto-properties;
    /// </item>
    /// <item>a base class's primary constructor passing only constants or parameters to its own base;</item>
    /// <item>no static constructor on a base class (the class's own is rejected by step 3), and every base class declared in source.</item>
    /// </list>
    /// A base class's static initialisers are not checked (#47). Without a static constructor the class is
    /// <c>beforefieldinit</c>, so the runtime runs them when one of its static fields is first read, not when an instance
    /// is created; and nothing allowed above reads one. A generic base class is checked through its original definition.
    /// An assignment to a virtual, abstract or overriding property is not allowed: it can dispatch to an override's setter.
    /// Implicit identity, numeric, reference and nullable conversions that are not user-defined cannot throw, so they are
    /// allowed; a user-defined conversion runs code, so it is not.
    /// </summary>
    private static SyntaxNode? ConstructionCouldThrow(
        ExtractionContext context, INamedTypeSymbol type, List<IObjectCreationOperation> creations, HashSet<(SyntaxTree, int, int)> instanceCreations)
    {
        foreach (var creation in creations)
        {
            if (creation.Initializer is not null)
            {
                return creation.Syntax;
            }
            if (creation.Arguments.FirstOrDefault(a => !IsConstant(a.Value) || a.InConversion.IsUserDefined) is { } argument)
            {
                return argument.Syntax;
            }
        }

        for (var t = type; t is not null && t.SpecialType != SpecialType.System_Object; t = t.BaseType)
        {
            bool constructorsUnreadable = t.DeclaringSyntaxReferences.IsEmpty;
            if (constructorsUnreadable)
            {
                return type.DeclaringSyntaxReferences[0].GetSyntax();
            }
            if (!SymbolEqualityComparer.Default.Equals(t, type) && t.StaticConstructors.FirstOrDefault(c => !c.IsImplicitlyDeclared) is { } cctor)
            {
                return cctor.DeclaringSyntaxReferences[0].GetSyntax();
            }
            // The declarations' operations are in terms of the original definition, so a generic base is checked as that.
            var owner = t.OriginalDefinition;
            bool isBase = !SymbolEqualityComparer.Default.Equals(t, type);
            foreach (var declaration in t.DeclaringSyntaxReferences.Select(r => r.GetSyntax()).OfType<TypeDeclarationSyntax>())
            {
                var model = context.Model(declaration.SyntaxTree);

                // A primary constructor's call to its base (the class's own primary constructor is rejected by step 2).
                if (declaration.BaseList?.Types.OfType<PrimaryConstructorBaseTypeSyntax>().FirstOrDefault() is { } primaryBase)
                {
                    foreach (var argument in primaryBase.ArgumentList.Arguments)
                    {
                        if (model.GetOperation(argument) is not IArgumentOperation a || !IsConstantOrParameter(a.Value) || a.InConversion.IsUserDefined)
                        {
                            return argument;
                        }
                    }
                }

                foreach (var member in declaration.Members)
                {
                    bool isStatic = member.Modifiers.Any(m => m.IsKind(SyntaxKind.StaticKeyword));
                    var initializers = member switch
                    {
                        _ when isStatic && isBase => [],
                        BaseFieldDeclarationSyntax f when !f.Modifiers.Any(m => m.IsKind(SyntaxKind.ConstKeyword)) =>
                            f.Declaration.Variables.Select(v => v.Initializer),
                        PropertyDeclarationSyntax p => [p.Initializer],
                        _ => [],
                    };
                    foreach (var clause in initializers.OfType<EqualsValueClauseSyntax>())
                    {
                        // The initialiser operation's value includes the conversion to the member's type, which may be
                        // user-defined; the expression's own operation does not.
                        var value = clause.Value;
                        // A static instance's creation is recorded by its own span, which parentheses around it do not
                        // share (#126).
                        var creation = value;
                        while (creation is ParenthesizedExpressionSyntax parenthesized)
                        {
                            creation = parenthesized.Expression;
                        }
                        // An instance initialiser stores into the backing field directly, so a primary-constructor parameter is
                        // as safe there as in a constructor body; a static initialiser has no parameters to read.
                        if (!instanceCreations.Contains((creation.SyntaxTree, creation.SpanStart, creation.Span.Length))
                            && !(model.GetOperation(clause) is ISymbolInitializerOperation init
                                && (isStatic ? IsConstant(init.Value) : IsConstantOrParameter(init.Value))))
                        {
                            return value;
                        }
                    }
                    if (member is ConstructorDeclarationSyntax ctor && !ctor.Modifiers.Any(m => m.IsKind(SyntaxKind.StaticKeyword))
                        && ConstructorCouldThrow(model, owner, ctor) is { } throwing)
                    {
                        return throwing;
                    }
                }
            }
        }
        return null;
    }

    /// <summary>The first part of an instance constructor that could throw, or null (see <see cref="ConstructionCouldThrow"/>).</summary>
    private static SyntaxNode? ConstructorCouldThrow(SemanticModel model, INamedTypeSymbol owner, ConstructorDeclarationSyntax syntax)
    {
        if (model.GetOperation(syntax) is not IConstructorBodyOperation body)
        {
            return syntax;
        }
        if (body.Initializer is { } initializer)
        {
            var call = initializer is IExpressionStatementOperation s ? s.Operation : initializer;
            if (call is not IInvocationOperation { TargetMethod: var target } invocation
                || !(SameDefinition(target.ContainingType, owner) || SameDefinition(target.ContainingType, owner.BaseType)))
            {
                return initializer.Syntax;
            }
            if (invocation.Arguments.FirstOrDefault(a => !IsConstantOrParameter(a.Value) || a.InConversion.IsUserDefined) is { } argument)
            {
                return argument.Syntax;
            }
        }
        foreach (var statement in Statements(body.BlockBody).Concat(Statements(body.ExpressionBody)))
        {
            if (statement is not IExpressionStatementOperation { Operation: ISimpleAssignmentOperation { IsRef: false } assignment }
                || !IsOwnStorage(owner, assignment.Target)
                || !IsConstantOrParameter(assignment.Value))
            {
                return statement.Syntax;
            }
        }
        return null;
    }

    private static ImmutableArray<IOperation> Statements(IBlockOperation? block) => block?.Operations ?? ImmutableArray<IOperation>.Empty;

    /// <summary>
    /// Whether an assignment target is a field, or a compiler-written auto-property that no override can replace, of
    /// <c>this</c> declared on the owner.
    /// </summary>
    private static bool IsOwnStorage(INamedTypeSymbol owner, IOperation target) => target switch
    {
        IFieldReferenceOperation { Instance: IInstanceReferenceOperation, Field: { IsStatic: false } field } =>
            SameDefinition(field.ContainingType, owner),
        IPropertyReferenceOperation
        {
            Instance: IInstanceReferenceOperation,
            Property: { IsStatic: false, IsVirtual: false, IsAbstract: false, IsOverride: false, Parameters.IsEmpty: true } property,
        } =>
            SameDefinition(property.ContainingType, owner) && IsAutoProperty(owner, property),
        _ => false,
    };

    /// <summary>Whether two types are the same declaration, whatever their type arguments.</summary>
    private static bool SameDefinition(ITypeSymbol? a, ITypeSymbol? b) =>
        a is not null && b is not null && SymbolEqualityComparer.Default.Equals(a.OriginalDefinition, b.OriginalDefinition);

    /// <summary>Whether a property has a compiler-generated backing field and no accessor with a body.</summary>
    private static bool IsAutoProperty(INamedTypeSymbol owner, IPropertySymbol property) =>
        owner.OriginalDefinition.GetMembers().OfType<IFieldSymbol>()
            .Any(f => SymbolEqualityComparer.Default.Equals(f.AssociatedSymbol?.OriginalDefinition, property.OriginalDefinition))
        && property.DeclaringSyntaxReferences.Length == 1
        && property.DeclaringSyntaxReferences[0].GetSyntax() is PropertyDeclarationSyntax { ExpressionBody: null, AccessorList: { } accessors }
        && HasOnlyAutoAccessors(accessors);

    /// <summary>Whether no accessor has a body, as in a compiler-written auto-property.</summary>
    private static bool HasOnlyAutoAccessors(AccessorListSyntax accessors) =>
        accessors.Accessors.All(a => a.Body is null && a.ExpressionBody is null);

    private static bool IsConstant(IOperation? op) =>
        op is { ConstantValue.HasValue: true } || WithoutSafeConversions(op) is { ConstantValue.HasValue: true };

    private static bool IsConstantOrParameter(IOperation? op) =>
        IsConstant(op) || WithoutSafeConversions(op) is IParameterReferenceOperation;

    /// <summary>
    /// The operand under implicit identity, numeric, reference and nullable conversions that are not user-defined, which
    /// cannot throw.
    /// </summary>
    private static IOperation? WithoutSafeConversions(IOperation? op)
    {
        while (op is IConversionOperation { IsImplicit: true, Conversion: { IsUserDefined: false } conversion } c
            && (conversion.IsIdentity || conversion.IsNumeric || conversion.IsReference || conversion.IsNullable))
        {
            op = c.Operand;
        }
        return op;
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
