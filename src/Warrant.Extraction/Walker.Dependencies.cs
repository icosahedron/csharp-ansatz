using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Operations;
using Warrant.Vir;

namespace Warrant.Extraction;

/// <summary>
/// Dependencies and <c>async</c> (plan M6 U18, KTD9, KTD22). A verified instance method of a class may call members of a
/// dependency: an instance <c>readonly</c> field declared in its own class, or a primary-constructor parameter of that class
/// that nothing assigns, of an interface type with a <c>[ContractFor]</c> class in this compilation. Each call is an
/// external call naming the dependency and the member, whose contract unit the method then depends on; every other use of
/// the class's state is rejected. A call returning <c>Task</c>, <c>Task&lt;T&gt;</c>, <c>ValueTask</c> or
/// <c>ValueTask&lt;T&gt;</c> must be the direct operand of <c>await</c>.
/// </summary>
internal sealed partial class Walker
{
    /// <summary>The class whose verified instance method is walked, whose state may hold dependencies; null otherwise.</summary>
    private INamedTypeSymbol? _owner;

    /// <summary>The dependencies the walk called through, in order of first use: the indices of its external calls.</summary>
    private readonly List<DependencyUse> _dependencies = [];

    /// <summary>The interface members called through a dependency, by key, with the contract class that states their contract.</summary>
    private readonly SortedDictionary<string, ContractMember> _contractMembers = new(StringComparer.Ordinal);

    /// <summary>How many <c>Spec</c> conditions the walk is inside: a claim, which has no world to call a dependency in (KTD26).</summary>
    private int _claims;

    /// <summary>The primary-constructor parameters already checked for assignments, and whether one was found.</summary>
    private readonly Dictionary<IParameterSymbol, bool> _assigned = new(SymbolEqualityComparer.Default);

    /// <summary>Lets the walk call through the dependencies of <paramref name="owner"/>, the class of a verified instance method.</summary>
    public void SetOwner(INamedTypeSymbol owner) => _owner = owner;

    /// <summary>The unit's dependencies (KTD9), each with the members called through it; null when it calls none.</summary>
    public VirList<VirDependency>? Dependencies =>
        _dependencies.Count == 0
            ? null
            : new VirList<VirDependency>(_dependencies.Select(d => new VirDependency(d.Name, Symbols.Key(d.Interface), new VirList<string>(d.Members.Keys))));

    /// <summary>The dependencies called through, in index order.</summary>
    public IReadOnlyList<DependencyUse> DependencyUses => _dependencies;

    /// <summary>The interface members called through a dependency, by key: the contract units the unit relies on.</summary>
    public IReadOnlyDictionary<string, ContractMember> ContractMembers => _contractMembers;

    /// <summary>A dependency a walk called through: its field or parameter, its interface, and the members called, by key.</summary>
    internal sealed class DependencyUse
    {
        public DependencyUse(ISymbol symbol, INamedTypeSymbol @interface)
        {
            Symbol = symbol;
            Interface = @interface;
        }

        public ISymbol Symbol { get; }

        public string Name => Symbol.Name;

        public INamedTypeSymbol Interface { get; }

        public SortedDictionary<string, IMethodSymbol> Members { get; } = new(StringComparer.Ordinal);
    }

    /// <summary>An interface member called through a dependency, and the contract class whose member states its contract.</summary>
    internal sealed class ContractMember
    {
        public ContractMember(IMethodSymbol member, INamedTypeSymbol contractClass)
        {
            Member = member;
            ContractClass = contractClass;
        }

        public IMethodSymbol Member { get; }

        public INamedTypeSymbol ContractClass { get; }
    }

    // ---- Return types (KTD22) ----

    /// <summary>
    /// A method's result type: <c>unit</c> for <c>void</c>; <c>task{T}</c> for <c>Task&lt;T&gt;</c> and
    /// <c>ValueTask&lt;T&gt;</c>, with <c>T</c>'s own nullable annotation; <c>task{unit}</c> for <c>Task</c> and
    /// <c>ValueTask</c>; otherwise the type as <see cref="MapType"/> maps it.
    /// </summary>
    public VirType MapReturn(ITypeSymbol type, bool annotated, SyntaxNode? at)
    {
        if (type.SpecialType == SpecialType.System_Void)
        {
            return VirType.Unit;
        }
        if (IsTask(type) is { } task)
        {
            return task.TypeArguments.Length == 0
                ? VirType.Task(VirType.Unit)
                : VirType.Task(MapType(task.TypeArguments[0], task.TypeArgumentNullableAnnotations[0] == NullableAnnotation.Annotated, at));
        }
        return MapType(type, annotated, at);
    }

    /// <summary><c>Task</c>, <c>Task&lt;T&gt;</c>, <c>ValueTask</c> or <c>ValueTask&lt;T&gt;</c>, or null for any other type.</summary>
    public static INamedTypeSymbol? IsTask(ITypeSymbol? type) =>
        type is INamedTypeSymbol { Name: "Task" or "ValueTask", Arity: <= 1 } named && IsTasksNamespace(named) ? named : null;

    private static bool IsTasksNamespace(INamedTypeSymbol type) => type.ContainingNamespace?.ToDisplayString() == "System.Threading.Tasks";

    /// <summary>A member of <c>Task</c>, <c>ValueTask</c> or their factories: a combinator, <c>ConfigureAwait</c>, or <c>Delay</c>.</summary>
    private static bool IsTaskMember(ISymbol member) =>
        member.ContainingType is { } owner && IsTasksNamespace(owner)
        && owner.OriginalDefinition.Name is "Task" or "ValueTask" or "TaskFactory" or "TaskExtensions";

    private static RejectedException TaskMember(ISymbol member, SyntaxNode at)
    {
        var construct = member.Name == "ConfigureAwait" ? "ConfigureAwait" : "Task combinator";
        return Unsupported(
            construct,
            at,
            $"{Symbols.Display(member)}: M6 sequences only awaited calls to dependencies and verified methods, each awaited where it is made (KTD22).");
    }

    /// <summary>
    /// <c>await</c> of a call to a dependency member or a verified method that returns a task: the awaited value, of the
    /// task's result type. Anything else awaited is rejected.
    /// </summary>
    private AwaitExpr Await(IAwaitOperation await)
    {
        var syntax = await.Syntax;
        if (await.Operation is not IInvocationOperation call)
        {
            throw Unsupported(
                "await of something other than a call",
                syntax,
                "M6 awaits only a call to a dependency member or a verified method, written where it is made: await store.Get(id).");
        }
        var value = Invocation(call, awaited: true);
        if (value.Type is not TaskType task)
        {
            throw Unsupported("await of something other than a call", syntax, $"{Symbols.Display(call.TargetMethod)} does not return a Task or ValueTask.");
        }
        return Track(new AwaitExpr(task.Result, value), syntax);
    }

    /// <summary>A call, unless it returns a task and is not the direct operand of <c>await</c> (KTD22, #67).</summary>
    private static T Awaited<T>(T call, bool awaited, SyntaxNode at)
        where T : VirExpr
    {
        if (call.Type is TaskType && !awaited)
        {
            throw Unsupported(
                "Task-returning call that is not awaited",
                at,
                "A call that returns a Task or ValueTask must be awaited where it is made: an async method's exception is captured in its task, so a task that is discarded, stored or returned would be modelled as throwing where the CLR returns.");
        }
        return call;
    }

    // ---- Dependencies (KTD9) ----

    /// <summary>
    /// Whether an operation reads the state of the class: an instance field of <c>this</c>, a static field of an interface
    /// type, or a primary-constructor parameter.
    /// </summary>
    private bool IsState(IOperation op) =>
        op switch
        {
            IFieldReferenceOperation { Field.IsStatic: false, Instance: IInstanceReferenceOperation } => true,
            IFieldReferenceOperation { Field: { IsStatic: true, Type.TypeKind: TypeKind.Interface } } => true,
            IParameterReferenceOperation p => IsPrimaryConstructorParameter(p.Parameter),
            _ => false,
        };

    private bool IsPrimaryConstructorParameter(IParameterSymbol parameter) =>
        !_parameters.ContainsKey(parameter) && !_bound.ContainsKey(parameter)
        && parameter.ContainingSymbol is IMethodSymbol { MethodKind: MethodKind.Constructor } constructor
        && constructor.DeclaringSyntaxReferences.Any(r => r.GetSyntax() is TypeDeclarationSyntax);

    /// <summary>
    /// The dependency a state read names (<see cref="IsState"/>), with its interface's contract class; any other state, or
    /// a dependency that breaks KTD9's rules, is rejected with the rule's construct.
    /// </summary>
    private (DependencyUse Use, INamedTypeSymbol ContractClass) Dependency(IOperation state)
    {
        var syntax = state.Syntax;
        var (symbol, type) = state switch
        {
            IFieldReferenceOperation f => ((ISymbol)f.Field, f.Field.Type),
            IParameterReferenceOperation p => (p.Parameter, p.Parameter.Type),
            _ => throw new InvalidOperationException($"'{state.Kind}' is not state."),
        };
        var field = symbol as IFieldSymbol;
        if (type is not INamedTypeSymbol { TypeKind: TypeKind.Interface } @interface)
        {
            throw MemberAccessOnThis(symbol, syntax);
        }
        if (field is { IsStatic: true })
        {
            throw Unsupported("static dependency", syntax, $"{Symbols.Display(field)} is static; a dependency is an instance field or a primary-constructor parameter of the method's own class.");
        }
        if (_owner is null)
        {
            throw MemberAccessOnThis(symbol, syntax);
        }
        if (field is not null && !SymbolEqualityComparer.Default.Equals(field.ContainingType.OriginalDefinition, _owner.OriginalDefinition))
        {
            throw Unsupported("inherited dependency", syntax, $"{Symbols.Display(field)} is declared in {Symbols.Display(field.ContainingType)}; a dependency is declared in the method's own class, {Symbols.Display(_owner)}.");
        }
        if (@interface.IsGenericType)
        {
            throw Unsupported("generic interface dependency", syntax, $"{Symbols.Display(symbol)} is of the generic interface {Symbols.Display(@interface)}.");
        }
        if (field is { IsReadOnly: false })
        {
            throw Unsupported("mutable dependency field", syntax, $"{Symbols.Display(field)} is not readonly, so the method could see another implementation than the one it was proved for; declare it readonly.");
        }
        if (symbol is IParameterSymbol parameter && Assigned(parameter))
        {
            throw Unsupported("assigned primary-constructor parameter", syntax, $"{parameter.Name} is assigned or passed by ref or out in {Symbols.Display(_owner)}, so it is not a fixed dependency.");
        }
        var index = _context.Contracts?.Value;
        var contractClass = index?.ClassFor(Symbols.Key(@interface));
        if (contractClass is null)
        {
            throw Unsupported(
                "dependency without a contract class",
                syntax,
                $"{Symbols.Display(@interface)} has no [ContractFor(typeof({@interface.Name}))] class in this compilation, so nothing states what {symbol.Name}'s members are assumed to do.");
        }
        if (index!.ProblemOf(Symbols.Key(contractClass)) is not null)
        {
            throw Unsupported(
                "dependency whose contract class is rejected",
                syntax,
                $"{Symbols.Display(contractClass)}, the contract class of {Symbols.Display(@interface)}, does not have the contract shape.");
        }
        var use = _dependencies.FirstOrDefault(d => SymbolEqualityComparer.Default.Equals(d.Symbol, symbol));
        if (use is null)
        {
            use = new DependencyUse(symbol, @interface);
            _dependencies.Add(use);
        }
        return (use, contractClass);
    }

    /// <summary>A call to a member of a dependency: an external call, whose contract is its interface member's contract unit.</summary>
    private ExternalCallExpr External(IInvocationOperation call, IOperation state)
    {
        var syntax = call.Syntax;
        var (use, contractClass) = Dependency(state);
        var target = call.TargetMethod;
        if (target.ContainingType.TypeKind != TypeKind.Interface)
        {
            throw NotVerified(target, syntax);
        }
        if (_claims > 0)
        {
            throw Unsupported(
                "dependency call in a Spec expression",
                syntax,
                $"A Spec.Requires, Spec.Ensures or Spec.Assert condition is a claim, not code that runs, so it cannot call {Symbols.Display(target)} through {use.Name}.");
        }
        if (target.IsGenericMethod)
        {
            throw Reject("generic member", syntax);
        }
        var key = Symbols.Key(target);
        var args = Arguments(target, call.Arguments, syntax);
        var type = MapReturn(target.ReturnType, target.ReturnNullableAnnotation == NullableAnnotation.Annotated, syntax);
        use.Members[key] = target;
        if (!_contractMembers.ContainsKey(key))
        {
            _contractMembers.Add(key, new ContractMember(target, contractClass));
        }
        Deps.Add(key);
        return Track(new ExternalCallExpr(type, _dependencies.IndexOf(use), key, args), syntax);
    }

    /// <summary>A use of a dependency other than calling one of its members, which the model has no value for.</summary>
    private RejectedException NotACall(IOperation state, string construct)
    {
        var (use, _) = Dependency(state);
        return Unsupported(
            construct,
            state.Syntax,
            $"{use.Name} is a dependency, which a verified method may only call methods of: its other uses have no model in M6.");
    }

    private static RejectedException MemberAccessOnThis(ISymbol symbol, SyntaxNode at) =>
        Unsupported(
            "member access on this",
            at,
            $"{Symbols.Display(symbol)}: a verified instance method may use its class's state only to call a dependency, a readonly field or never-assigned primary-constructor parameter of an interface type with a [ContractFor] class; other instance state waits for M7's heap model.");

    /// <summary>
    /// Whether any syntax in the declarations of the parameter's class, lambdas included, assigns the primary-constructor
    /// parameter or passes it by <c>ref</c> or <c>out</c>.
    /// </summary>
    private bool Assigned(IParameterSymbol parameter)
    {
        if (_assigned.TryGetValue(parameter, out bool found))
        {
            return found;
        }
        var type = parameter.ContainingSymbol.ContainingType;
        foreach (var declaration in type.DeclaringSyntaxReferences.Select(r => r.GetSyntax()))
        {
            var model = _context.Model(declaration.SyntaxTree);
            foreach (var name in declaration.DescendantNodes().OfType<IdentifierNameSyntax>())
            {
                if (name.Identifier.ValueText == parameter.Name
                    && SymbolEqualityComparer.Default.Equals(model.GetSymbolInfo(name).Symbol, parameter)
                    && IsWritten(name))
                {
                    found = true;
                    break;
                }
            }
            if (found)
            {
                break;
            }
        }
        _assigned.Add(parameter, found);
        return found;
    }

    /// <summary>Whether a name is assigned, incremented, deconstructed into, or passed or taken by <c>ref</c> or <c>out</c>.</summary>
    private static bool IsWritten(ExpressionSyntax name)
    {
        SyntaxNode node = name;
        while (true)
        {
            switch (node.Parent)
            {
                case ParenthesizedExpressionSyntax parenthesized:
                    node = parenthesized;
                    continue;
                case ArgumentSyntax { Parent: TupleExpressionSyntax tuple }:
                    node = tuple;
                    continue;
                case AssignmentExpressionSyntax assignment:
                    return assignment.Left == node;
                case PrefixUnaryExpressionSyntax prefix:
                    return prefix.IsKind(SyntaxKind.PreIncrementExpression) || prefix.IsKind(SyntaxKind.PreDecrementExpression);
                case PostfixUnaryExpressionSyntax postfix:
                    return postfix.IsKind(SyntaxKind.PostIncrementExpression) || postfix.IsKind(SyntaxKind.PostDecrementExpression);
                case ArgumentSyntax argument:
                    return argument.RefKindKeyword.IsKind(SyntaxKind.RefKeyword) || argument.RefKindKeyword.IsKind(SyntaxKind.OutKeyword);
                case RefExpressionSyntax:
                    return true;
                default:
                    return false;
            }
        }
    }

    /// <summary>
    /// Whether the arguments, in parameter order, run in another order than written while one of them awaits or calls a
    /// dependency: the model evaluates them in parameter order, and the calls change the world in the order they run.
    /// </summary>
    private static bool Reordered(IEnumerable<IArgumentOperation> arguments, VirExpr?[] byOrdinal)
    {
        var written = arguments.Where(a => !a.IsImplicit && a.Parameter is not null).OrderBy(a => a.Syntax.SpanStart).Select(a => a.Parameter!.Ordinal).ToList();
        bool ordered = written.Zip(written.Skip(1), (a, b) => a < b).All(x => x);
        return !ordered && byOrdinal.Any(a => a is not null && CallsOut(a));
    }

    private static bool CallsOut(VirNode node) => node is AwaitExpr or ExternalCallExpr || VirTree.Children(node).Any(CallsOut);

    /// <summary>A rejection with its own message, for the M6 constructs whose message says what to do instead.</summary>
    private static RejectedException Unsupported(string construct, SyntaxNode at, string message) =>
        new(new Rejection(DiagnosticIds.Unsupported, construct, at.GetLocation(), message));

    // ---- Contract units (KTD10) ----

    /// <summary>
    /// A contract member's body as a contract unit reads it: its leading <c>Spec.Requires</c> and <c>Spec.Ensures</c>,
    /// whose order and types are checked as a method's are; empty for an <c>abstract</c> member or <c>=&gt; default!</c>.
    /// The class's shape check has already made sure nothing else is in it.
    /// </summary>
    public BlockStmt ContractBody(IMethodBodyOperation? body, SyntaxNode at)
    {
        var block = body?.BlockBody;
        var result = new List<VirStmt>();
        int last = -1;
        foreach (var op in block is null ? Enumerable.Empty<IOperation>() : block.Operations)
        {
            if (op is not IExpressionStatementOperation { Operation: IInvocationOperation call } || LeadingRank(call) is not { } rank)
            {
                break;
            }
            result.Add(Leading(call, rank, leading: true, last, op.Syntax));
            last = rank;
        }
        return Track(new BlockStmt(new VirList<VirStmt>(result)), block?.Syntax ?? at);
    }
}
