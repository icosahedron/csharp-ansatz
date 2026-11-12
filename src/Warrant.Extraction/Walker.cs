using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Operations;
using Warrant.Vir;

namespace Warrant.Extraction;

/// <summary>
/// The allow-list walk over one member's <see cref="IOperation"/> tree (docs/m4/03, "Walking the operation tree").
/// Each node is accepted only if its kind, operator kind, operand types and checked flag are on the list; the first one
/// that is not stops the walk with a <see cref="RejectedException"/> naming the construct.
/// </summary>
internal sealed partial class Walker
{
    private readonly ExtractionContext _context;
    private readonly Dictionary<IParameterSymbol, int> _parameters = new(SymbolEqualityComparer.Default);
    private readonly Dictionary<ILocalSymbol, int> _locals = new(SymbolEqualityComparer.Default);

    /// <summary>The variables bound by <c>Spec.ForAll</c> and <c>Spec.Exists</c> lambdas, by local ID.</summary>
    private readonly Dictionary<IParameterSymbol, int> _bound = new(SymbolEqualityComparer.Default);

    /// <summary>
    /// The variables bound by <c>Spec.ForAll</c>, in order. A reference-typed one ranges over non-null values only, which
    /// the unit's assumptions must say, as they do for a parameter.
    /// </summary>
    private readonly List<IParameterSymbol> _universals = [];

    /// <summary>The variables bound by <c>Spec.ForAll</c> in the unit walked, in source order.</summary>
    public IReadOnlyList<IParameterSymbol> Universals => _universals;
    private readonly Dictionary<object, SyntaxNode> _syntax = new(ReferenceComparer.Instance);
    private readonly bool _inTheorem;

    /// <summary>The next local ID: locals and bound variables share one numbering, unique within the unit.</summary>
    private int _nextLocal;

    /// <summary>The VIR type of each nullable local, by local ID: its declared type, or for <c>var</c> its initializer's.</summary>
    private readonly Dictionary<int, VirType> _nullableLocals = [];

    /// <summary>The member's declared return type and whether it is annotated nullable; null for a theorem.</summary>
    private (ITypeSymbol Type, bool Annotated)? _returns;

    public Walker(ExtractionContext context, bool inTheorem)
    {
        _context = context;
        _inTheorem = inTheorem;
    }

    /// <summary>The keys of the units this one calls or whose types it mentions.</summary>
    public SortedSet<string> Deps { get; } = new(StringComparer.Ordinal);

    /// <summary>The keys of the verified members this one calls, for the recursion check.</summary>
    public SortedSet<string> Calls { get; } = new(StringComparer.Ordinal);

    /// <summary>The syntax of a VIR node this walk created, by node instance.</summary>
    public SyntaxNode? SyntaxOf(VirNode node) => _syntax.TryGetValue(node, out var s) ? s : null;

    public static RejectedException Reject(string construct, SyntaxNode? at, string? detail = null, string id = DiagnosticIds.Unsupported) =>
        new(new Rejection(id, construct, at?.GetLocation(), detail is null ? $"M4 does not support {construct}." : $"M4 does not support {construct}: {detail}."));

    public void AddParameter(IParameterSymbol parameter, int index) => _parameters.Add(parameter, index);

    /// <summary>
    /// Sets the member's declared return type, which a returned value must fit (KTD5). An <c>async</c> method returns the
    /// value its <c>Task&lt;T&gt;</c> or <c>ValueTask&lt;T&gt;</c> carries, so that is the type its returns fit (KTD22).
    /// </summary>
    public void SetReturns(ITypeSymbol type, bool annotated, bool isAsync = false) =>
        _returns = isAsync && IsTask(type) is { TypeArguments.Length: 1 } task
            ? (task.TypeArguments[0], task.TypeArgumentNullableAnnotations[0] == NullableAnnotation.Annotated)
            : (type, annotated);

    /// <summary>A returned value: an expression body's, or a <c>return</c> statement's, fitted to the declared return type.</summary>
    public VirExpr Returned(IOperation value)
    {
        var e = Expr(value);
        return _returns is { } returns ? FitDeclared(e, returns.Type, returns.Annotated, value.Syntax) : e;
    }

    /// <summary>Maps a declared type (a parameter, return, local or field type) to VIR, recording the type units it uses.</summary>
    public VirType MapType(ITypeSymbol? type, bool annotated, SyntaxNode? at)
    {
        if (type is null)
        {
            throw Reject("null", at);
        }
        // T? is a value or null (M6 KTD5): Nullable<T> of bool, int, long or decimal, and an annotated reference to a record
        // class or closed class. The annotation is the declaration's, never Roslyn's flow state.
        if (type is INamedTypeSymbol { OriginalDefinition.SpecialType: SpecialType.System_Nullable_T } nullable)
        {
            var value = nullable.TypeArguments[0];
            if (Symbols.Primitive(value) is null && value.SpecialType != SpecialType.System_Decimal)
            {
                throw Reject("nullable type", at, Symbols.Display(type));
            }
            return VirType.Nullable(MapType(value, annotated: false, at));
        }
        if (annotated && type.IsReferenceType)
        {
            if (!Symbols.IsNullableReference(type))
            {
                throw Reject("nullable type", at, Symbols.Display(type));
            }
            return VirType.Nullable(MapType(type, annotated: false, at));
        }
        if (Symbols.Primitive(type) is { } p)
        {
            return Symbols.PrimitiveType(p);
        }
        switch (type.SpecialType)
        {
            case SpecialType.System_String:
                throw Reject("string", at);
            case SpecialType.System_Decimal:
                return VirType.Decimal;
            case SpecialType.System_Single or SpecialType.System_Double:
                throw Reject("floating point", at);
        }
        if (Symbols.Shape(type) != TypeShape.Other && type is INamedTypeSymbol named)
        {
            if (!_context.IsOwn(named))
            {
                // A closed class from a referenced project is checked from the source its build recorded (#32). The
                // analyzer has no such source and leaves the check to the build.
                bool closedClass = Symbols.Shape(named) == TypeShape.ClosedClass;
                if (closedClass && _context.DeferReferenced && !named.IsGenericType)
                {
                    var referenced = Symbols.Key(named);
                    Deps.Add(referenced);
                    return VirType.Ref(referenced);
                }
                var reason = "";
                named = (closedClass ? _context.FromReferencedSource(named, out reason) : null)
                    ?? throw Reject(
                        "type defined outside the compilation",
                        at,
                        closedClass ? $"{Symbols.Display(type)}, and {reason}" : Symbols.Display(type));
            }
            if (named.IsGenericType)
            {
                throw Reject("generic type", at, Symbols.Display(type));
            }
            var key = Symbols.Key(named);
            Deps.Add(key);
            _context.UseType(named);
            return VirType.Ref(key);
        }
        throw Reject("unsupported type", at, Symbols.Display(type));
    }

    // ---- Statements ----

    public BlockStmt Block(IBlockOperation block) => Track(new BlockStmt(Statements(block.Operations)), block.Syntax);

    /// <summary>
    /// A member's block body, which may start with the leading <c>Spec</c> statements (M6 KTD8): <c>Spec.Decreases</c> if
    /// any, then <c>Spec.Requires</c>, then <c>Spec.NoThrow</c> (#182), then <c>Spec.Ensures</c>.
    /// </summary>
    public BlockStmt Body(IBlockOperation block) => Track(new BlockStmt(Statements(block.Operations, leading: true)), block.Syntax);

    private VirList<VirStmt> Statements(IEnumerable<IOperation> operations, bool leading = false)
    {
        var result = new List<VirStmt>();
        bool ended = false;

        // The rank of the last leading Spec statement read; -1 before the first. Leading ends at the first other statement.
        int last = -1;
        foreach (var op in operations)
        {
            if (op is IEmptyOperation)
            {
                continue;
            }
            if (op is IExpressionStatementOperation { Operation: IInvocationOperation call } && LeadingRank(call) is { } rank)
            {
                result.Add(Leading(call, rank, leading, last, op.Syntax));
                last = rank;
                continue;
            }
            leading = false;
            if (op is IExpressionStatementOperation { Operation: IInvocationOperation assert } && IsSpec(assert, "Assert"))
            {
                if (ended)
                {
                    throw Reject("unreachable code", op.Syntax);
                }
                result.Add(Assert(assert, op.Syntax));
                continue;
            }
            if (op is ILocalFunctionOperation)
            {
                throw Reject("local function", op.Syntax);
            }
            if (ended)
            {
                throw Reject("unreachable code", op.Syntax);
            }
            result.AddRange(Statement(op));
            ended = Terminates(op);
        }
        return new VirList<VirStmt>(result);
    }

    /// <summary>Whether control never reaches the end of the statement (it returns on every path).</summary>
    private static bool Terminates(IOperation op) =>
        op switch
        {
            IReturnOperation or IThrowOperation or IExpressionStatementOperation { Operation: IThrowOperation } => true,
            IBlockOperation b => b.Operations.Any(Terminates),
            IConditionalOperation { WhenFalse: { } e } c => Terminates(c.WhenTrue) && Terminates(e),
            ISwitchOperation s => s.Cases.Any(c => c.Clauses.Any(cl => cl is IDefaultCaseClauseOperation || cl is IPatternCaseClauseOperation { Pattern: IDiscardPatternOperation }))
                && s.Cases.All(c => c.Body.Any(Terminates)),
            _ => false,
        };

    private List<VirStmt> Statement(IOperation op)
    {
        switch (op)
        {
            case IBlockOperation b:
                return [Block(b)];
            case IVariableDeclarationGroupOperation g:
                return Declarations(g);
            case IExpressionStatementOperation e:
                return [ExpressionStatement(e)];
            case IReturnOperation { ReturnedValue: { } value } r:
                return [Track(new ReturnStmt(Returned(value)), r.Syntax)];
            case IReturnOperation r:
                // VIR's return carries a value; a method without one ends by reaching its end (M6 U18).
                throw Reject("return without a value", r.Syntax, "a method that returns no value ends by reaching the end of its body");
            case IConditionalOperation c:
                {
                    var cond = Expr(c.Condition);
                    var then = Branch(c.WhenTrue);
                    var @else = c.WhenFalse is { } wf ? Branch(wf) : null;
                    return [Track(new IfStmt(cond, then, @else), c.Syntax)];
                }
            case ISwitchOperation s:
                return [SwitchStatement(s)];
            case ILoopOperation:
                throw Reject("loop", op.Syntax);
            case ITryOperation:
                throw Reject("try", op.Syntax);
            case IThrowOperation t:
                return [Track(new ThrowStmt(Thrown(t)), t.Syntax)];
            case IBranchOperation or ILabeledOperation:
                throw Reject("jump statement", op.Syntax);
            default:
                throw Reject("unsupported statement", op.Syntax, op.Kind.ToString());
        }
    }

    /// <summary>An <c>if</c> branch, always as a block, as chapter 4's example writes it.</summary>
    private BlockStmt Branch(IOperation op)
    {
        if (op is IBlockOperation b)
        {
            return Block(b);
        }
        return Track(new BlockStmt(Statements([op])), op.Syntax);
    }

    private List<VirStmt> Declarations(IVariableDeclarationGroupOperation group)
    {
        var result = new List<VirStmt>();
        foreach (var declaration in group.Declarations)
        {
            foreach (var declarator in declaration.Declarators)
            {
                var init = declarator.Initializer?.Value ?? declaration.Initializer?.Value
                    ?? throw Reject("local without an initializer", declarator.Syntax);
                // #133: a ref local is another name for a variable, so a write through either is seen through both. The
                // model has no aliases; as a copy it would lose the write, and it would get around "assignment to a parameter".
                if (declarator.Symbol.RefKind != RefKind.None)
                {
                    throw Reject("ref local", declarator.Syntax);
                }
                // `var` declares a reference-typed local nullable whatever its initializer, so such a local takes its
                // initializer's type; an explicitly typed one takes its declared type, which the initializer must fit (KTD5).
                bool isVar = declaration.Syntax is VariableDeclarationSyntax { Type.IsVar: true };

                // A stored task (KTD22): its call is rejected as not awaited, which says what to write, before its type is.
                if (IsTask(declarator.Symbol.Type) is not null)
                {
                    Expr(init);
                }
                var declared = MapType(
                    declarator.Symbol.Type, !isVar && declarator.Symbol.NullableAnnotation == NullableAnnotation.Annotated, declarator.Syntax);
                var value = Expr(init);
                var type = declared;
                if (isVar)
                {
                    type = value.Type is NullableType ? value.Type : declared;
                }
                else
                {
                    value = FitTo(value, declared, init.Syntax);
                }
                int id = _nextLocal++;
                _locals.Add(declarator.Symbol, id);
                if (type is NullableType)
                {
                    _nullableLocals.Add(id, type);
                }
                result.Add(Track(new DeclStmt(id, declarator.Symbol.Name, value), declarator.Syntax));
            }
        }
        return result;
    }

    private int Local(IOperation target, SyntaxNode at)
    {
        switch (target)
        {
            case ILocalReferenceOperation l when _locals.TryGetValue(l.Local, out int id):
                return id;
            case IParameterReferenceOperation:
                throw Reject("assignment to a parameter", at);
            default:
                throw Reject("assignment to a field or property", at);
        }
    }

    private VirStmt ExpressionStatement(IExpressionStatementOperation statement)
    {
        var syntax = statement.Syntax;
        switch (statement.Operation)
        {
            case IAwaitOperation or IInvocationOperation:
                return Track(new EvalStmt(Discarded(statement.Operation)), syntax);
            case ISimpleAssignmentOperation { Target: IDiscardOperation } discard:
                return Track(new EvalStmt(Discarded(discard.Value)), syntax);
            case ISimpleAssignmentOperation a:
                {
                    if (a.IsRef)
                    {
                        throw Reject("ref local", syntax);
                    }
                    int id = Local(a.Target, syntax);
                    var value = Expr(a.Value);
                    var type = _nullableLocals.TryGetValue(id, out var nullable) ? nullable : MapType(a.Target.Type, annotated: false, syntax);
                    return Track(new AssignStmt(id, FitTo(value, type, a.Value.Syntax)), syntax);
                }
            case ICompoundAssignmentOperation a:
                {
                    int id = Local(a.Target, syntax);
                    if (a.OperatorMethod is not null)
                    {
                        throw Reject("user-defined operator", syntax);
                    }
                    if (!a.InConversion.IsIdentity || !a.OutConversion.IsIdentity)
                    {
                        throw Reject("unsupported conversion", syntax);
                    }
                    var type = MapType(a.Target.Type, annotated: false, syntax);
                    var left = Track(new LocalExpr(type, id), a.Target.Syntax);
                    var value = Arithmetic(a.OperatorKind, a.IsChecked, a.IsLifted, type, a.Target.Type, left, a.Value, a.Syntax);
                    return Track(new AssignStmt(id, value), syntax);
                }
            case IIncrementOrDecrementOperation inc:
                {
                    int id = Local(inc.Target, syntax);
                    if (inc.OperatorMethod is not null)
                    {
                        throw Reject("user-defined operator", syntax);
                    }
                    if (inc.IsLifted)
                    {
                        throw Reject("lifted arithmetic", syntax);
                    }
                    var type = MapType(inc.Target.Type, annotated: false, syntax);
                    if (type is not PrimitiveType { Kind: VirPrimitive.Int32 or VirPrimitive.Int64 })
                    {
                        throw Reject("increment of a non-integer", syntax);
                    }
                    var one = Track(new LitExpr(type, 1), syntax);
                    var op = inc.Kind == OperationKind.Increment ? BinaryOp.Add : BinaryOp.Sub;
                    var overflow = Overflow(inc.IsChecked, syntax);
                    var value = Track(new BinaryExpr(type, op, overflow, Track(new LocalExpr(type, id), inc.Target.Syntax), one), syntax);
                    return Track(new AssignStmt(id, value), syntax);
                }
            case IThrowOperation t:
                return Track(new ThrowStmt(Thrown(t)), syntax);
            case { } other:
                // Walk it to report what it is (a call to a theorem, an unverified member), then reject the statement itself.
                Expr(other);
                throw Reject("expression statement", syntax);
            default:
                throw Reject("expression statement", syntax);
        }
    }

    /// <summary>
    /// An expression whose value is discarded, run for its effects (M6 KTD22): a call to a verified method or a dependency
    /// member, or an awaited one. Anything else as a statement is rejected.
    /// </summary>
    public VirExpr Discarded(IOperation operation)
    {
        var value = Expr(operation);
        return value is CallExpr or ExternalCallExpr or AwaitExpr ? value : throw Reject("expression statement", operation.Syntax);
    }

    private SwitchStmt SwitchStatement(ISwitchOperation s)
    {
        var scrutinee = NotNullableScrutinee(Expr(s.Value), s.Syntax);
        var sections = new List<SwitchSection>();
        foreach (var section in s.Cases)
        {
            var labels = new List<VirPattern>();
            if (section.Clauses.Length > 1 && section.Clauses.Any(cl => cl is IDefaultCaseClauseOperation))
            {
                // `case 1: default:` — translation places default last, which a shared section cannot express.
                throw Reject("switch section mixing default with case labels", section.Syntax);
            }
            foreach (var clause in section.Clauses)
            {
                labels.Add(clause switch
                {
                    IDefaultCaseClauseOperation d => Track(new DiscardPattern(), d.Syntax),
                    ISingleValueCaseClauseOperation v => Track(new ConstPattern(Constant(v.Value)), v.Syntax),
                    IPatternCaseClauseOperation { Guard: not null } p => throw Reject("case guard", p.Syntax),
                    IPatternCaseClauseOperation p => Pattern(p.Pattern),
                    _ => throw Reject("unsupported pattern", clause.Syntax),
                });
            }
            var body = section.Body.ToList();
            if (body.Count > 0 && body[body.Count - 1] is IBranchOperation { BranchKind: BranchKind.Break } last
                && (body.Count == 1 || !Terminates(body[body.Count - 2])))
            {
                body.RemoveAt(body.Count - 1);
            }
            sections.Add(new SwitchSection(new VirList<VirPattern>(labels), Statements(body)));
        }
        return Track(new SwitchStmt(scrutinee, new VirList<SwitchSection>(sections)), s.Syntax);
    }

    // ---- Expressions ----

    public VirExpr Expr(IOperation op)
    {
        var syntax = op.Syntax;

        // `x!` is not an operation: it only silences the compiler, and a value it forgives can still be null (KTD5).
        if (Forgiving(syntax) is { } forgiving)
        {
            throw Reject("null-forgiving operator", forgiving);
        }

        // Closed enums: the cast, unboxing and default checks run on the original node, before constants (KTD13).
        if (Symbols.IsClosedEnum(op.Type))
        {
            if (op is IDefaultValueOperation || op is IConversionOperation { Operand: IDefaultValueOperation })
            {
                throw Reject("default of a closed enum", syntax);
            }
            if (op is IConversionOperation conv && CompilationScan.Classify(conv) is { } construct)
            {
                throw Reject(construct, syntax);
            }
        }

        // Constants of int, long, bool and decimal are what the IL contains (KTD13); a decimal keeps its scale (KTD7).
        if (op.ConstantValue is { HasValue: true, Value: decimal dec } && op.Type?.SpecialType == SpecialType.System_Decimal)
        {
            return Track(DecimalLitExpr.Of(dec), syntax);
        }
        if (op.ConstantValue.HasValue && op.Type is { } ctype && Symbols.Primitive(ctype) is { } prim)
        {
            var value = op.ConstantValue.Value!;
            long v = prim == VirPrimitive.Bool ? ((bool)value ? 1 : 0) : Symbols.ToInt64(value);
            return Track(new LitExpr(Symbols.PrimitiveType(prim), v), syntax);
        }
        if (op.ConstantValue.HasValue && op.Type is INamedTypeSymbol { TypeKind: TypeKind.Enum } enumType)
        {
            return EnumConstant(op, enumType);
        }

        switch (op)
        {
            // A variable's type is its declaration's, not the flow state Roslyn gives the reference (KTD5).
            case IParameterReferenceOperation p when _parameters.TryGetValue(p.Parameter, out int index):
                return Track(new ParamExpr(MapType(p.Parameter.Type, Annotated(p.Parameter), syntax), index), syntax);
            case ILocalReferenceOperation l when _locals.TryGetValue(l.Local, out int id):
                {
                    var type = MapType(l.Type, annotated: false, syntax);
                    return Track(new LocalExpr(_nullableLocals.TryGetValue(id, out var nullable) ? nullable : type, id), syntax);
                }
            case IParameterReferenceOperation p when _bound.TryGetValue(p.Parameter, out int bound):
                return Track(new LocalExpr(MapType(p.Parameter.Type, Annotated(p.Parameter), syntax), bound), syntax);
            case IParameterReferenceOperation p when IsPrimaryConstructorParameter(p.Parameter):
                throw NotACall(p, "dependency used other than to call a member");
            case IInstanceReferenceOperation { Type: { } self } when Symbols.Shape(self) != TypeShape.Record:
                throw MemberAccessOnThis(self, syntax);
            case IAwaitOperation a:
                return Await(a);
            case IInstanceReferenceOperation i:
                return Track(new SelfExpr(MapType(i.Type, annotated: false, syntax)), syntax);
            case IBinaryOperation b:
                return Binary(b);
            case IUnaryOperation u:
                return Unary(u);
            case IConversionOperation c:
                return Conversion(c);
            case IConditionalOperation { WhenFalse: { } whenFalse } c:
                {
                    if (c.IsRef)
                    {
                        throw Reject("ref conditional", syntax);
                    }
                    var type = MapType(c.Type, annotated: false, syntax);
                    var condition = Expr(c.Condition);
                    var then = Expr(c.WhenTrue);
                    var @else = Expr(whenFalse);
                    type = Join(type, [then, @else]);
                    return Track(new CondExpr(type, condition, FitTo(then, type, c.WhenTrue.Syntax), FitTo(@else, type, whenFalse.Syntax)), syntax);
                }
            case IIsPatternOperation isPattern when NullPattern(isPattern.Pattern) is { } nullPattern:
                return NullTest(Expr(isPattern.Value), nullPattern.Negated, nullPattern.Null, syntax);
            case ICoalesceOperation coalesce:
                return Coalesce(coalesce);
            case IInvocationOperation call:
                return Invocation(call);
            case IPropertyReferenceOperation prop:
                return PropertyRead(prop);
            case IFieldReferenceOperation field:
                return FieldRead(field);
            case IObjectCreationOperation create:
                return Creation(create);
            case IWithOperation with:
                return With(with);
            case ISwitchExpressionOperation sw:
                return SwitchExpression(sw);
            case IThrowOperation { Type: { } throwType } t:
                return ThrowExpression(t, MapType(throwType, annotated: false, syntax));
            case IThrowOperation:
                throw Reject("throw", syntax);
            case ILiteralOperation { Type: null } or IDefaultValueOperation:
                throw Reject("null", syntax);
            case IAnonymousFunctionOperation or IDelegateCreationOperation:
                throw Reject("lambda", syntax);
            default:
                throw Reject("unsupported expression", syntax, op.Kind.ToString());
        }
    }

    private VirExpr Constant(IOperation op)
    {
        var e = Expr(op);
        if (e is not (LitExpr or MemberExpr))
        {
            throw Reject("pattern that is not a constant", op.Syntax);
        }
        return e;
    }

    private VirExpr EnumConstant(IOperation op, INamedTypeSymbol type)
    {
        var vtype = MapType(type, annotated: false, op.Syntax);
        long value = Symbols.ToInt64(op.ConstantValue.Value!);
        string? name = null;
        if (op is IFieldReferenceOperation { Field: { HasConstantValue: true } f } && SymbolEqualityComparer.Default.Equals(f.ContainingType, type))
        {
            name = f.Name;
        }
        else
        {
            name = type.GetMembers().OfType<IFieldSymbol>()
                .FirstOrDefault(m => m.HasConstantValue && Symbols.ToInt64(m.ConstantValue!) == value)?.Name;
        }
        if (name is not null)
        {
            return Track(new MemberExpr(vtype, name), op.Syntax);
        }
        if (Symbols.Shape(type) == TypeShape.ClosedEnum)
        {
            throw Reject("closed enum constant that names no member", op.Syntax);
        }
        return Track(new LitExpr(vtype, value), op.Syntax);
    }

    private VirExpr Binary(IBinaryOperation b)
    {
        var syntax = b.Syntax;
        bool equality = b.OperatorKind is BinaryOperatorKind.Equals or BinaryOperatorKind.NotEquals;
        if (equality && (IsNullLiteral(b.LeftOperand) || IsNullLiteral(b.RightOperand)))
        {
            // `x == null` on a nullable value, whatever operator Roslyn picked (a record's ==, a lifted ==, object ==).
            var (nullOp, other) = IsNullLiteral(b.LeftOperand) ? (b.LeftOperand, b.RightOperand) : (b.RightOperand, b.LeftOperand);
            return NullTest(Expr(Unwrapped(other) ?? other), b.OperatorKind == BinaryOperatorKind.NotEquals, nullOp.Syntax, syntax);
        }
        if (b.IsLifted)
        {
            // With null operands these follow neither Option's order nor its equality (#76), so M6 leaves them out.
            bool comparison = equality || b.OperatorKind is BinaryOperatorKind.LessThan or BinaryOperatorKind.LessThanOrEqual
                or BinaryOperatorKind.GreaterThan or BinaryOperatorKind.GreaterThanOrEqual;
            throw Reject(comparison ? "lifted comparison" : "lifted arithmetic", syntax);
        }
        switch (b.OperatorKind)
        {
            case BinaryOperatorKind.LeftShift or BinaryOperatorKind.RightShift or BinaryOperatorKind.UnsignedRightShift:
                throw Reject("shift", syntax);
        }
        if (b.OperatorMethod is { } method)
        {
            return UserOperator(b, method);
        }
        var left = b.LeftOperand;
        var right = b.RightOperand;
        switch (b.OperatorKind)
        {
            case BinaryOperatorKind.Add or BinaryOperatorKind.Subtract or BinaryOperatorKind.Multiply
                or BinaryOperatorKind.Divide or BinaryOperatorKind.Remainder:
                {
                    var type = MapType(b.Type, annotated: false, syntax);
                    return Arithmetic(b.OperatorKind, b.IsChecked, isLifted: false, type, b.Type, Expr(left), right, syntax);
                }
            case BinaryOperatorKind.And or BinaryOperatorKind.Or or BinaryOperatorKind.ExclusiveOr:
                if (left.Type?.SpecialType != SpecialType.System_Boolean)
                {
                    throw Reject("integer bitwise operator", syntax);
                }
                var eager = b.OperatorKind switch
                {
                    BinaryOperatorKind.And => LogicalOp.AndEager,
                    BinaryOperatorKind.Or => LogicalOp.OrEager,
                    _ => LogicalOp.Xor,
                };
                return Track(new LogicalExpr(eager, Expr(left), Expr(right)), syntax);
            case BinaryOperatorKind.ConditionalAnd or BinaryOperatorKind.ConditionalOr:
                {
                    var op = b.OperatorKind == BinaryOperatorKind.ConditionalAnd ? LogicalOp.And : LogicalOp.Or;
                    return Track(new LogicalExpr(op, Expr(left), Expr(right)), syntax);
                }
            case BinaryOperatorKind.Equals or BinaryOperatorKind.NotEquals or BinaryOperatorKind.LessThan
                or BinaryOperatorKind.LessThanOrEqual or BinaryOperatorKind.GreaterThan or BinaryOperatorKind.GreaterThanOrEqual:
                return Comparison(b);
            default:
                throw Reject("unsupported operator", syntax, b.OperatorKind.ToString());
        }
    }

    /// <summary>
    /// The overflow behaviour of <c>+</c>, <c>-</c>, <c>*</c>, unary <c>-</c> or a narrowing at <paramref name="syntax"/>
    /// (#183, #236, #244): <c>checked</c> or <c>unchecked</c> as the nearest enclosing <c>checked</c>/<c>unchecked</c>
    /// expression or block says, and otherwise the project's default, <c>checked</c> under CheckForOverflowUnderflow and
    /// <c>wrap</c> without, which Roslyn's <paramref name="isChecked"/> gives. Explicit <c>unchecked</c> wraps on purpose;
    /// the default <c>wrap</c> must not overflow where Warrant proves something.
    /// </summary>
    private static VirOverflow Overflow(bool isChecked, SyntaxNode syntax)
    {
        for (var node = syntax; node is not null and not MemberDeclarationSyntax; node = node.Parent)
        {
            var keyword = node switch
            {
                CheckedExpressionSyntax e => e.Keyword,
                CheckedStatementSyntax s => s.Keyword,
                _ => default,
            };
            if (keyword.IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.UncheckedKeyword))
            {
                return VirOverflow.Unchecked;
            }
            if (keyword.IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.CheckedKeyword))
            {
                return VirOverflow.Checked;
            }
        }
        return isChecked ? VirOverflow.Checked : VirOverflow.Wrap;
    }

    private VirExpr Arithmetic(
        BinaryOperatorKind kind, bool isChecked, bool isLifted, VirType type, ITypeSymbol? clrType, VirExpr left, IOperation rightOp, SyntaxNode syntax)
    {
        if (isLifted)
        {
            throw Reject("lifted arithmetic", syntax);
        }
        switch (kind)
        {
            case BinaryOperatorKind.LeftShift or BinaryOperatorKind.RightShift or BinaryOperatorKind.UnsignedRightShift:
                throw Reject("shift", syntax);
            case BinaryOperatorKind.And or BinaryOperatorKind.Or or BinaryOperatorKind.ExclusiveOr:
                if (type == VirType.Bool)
                {
                    var eager = kind switch
                    {
                        BinaryOperatorKind.And => LogicalOp.AndEager,
                        BinaryOperatorKind.Or => LogicalOp.OrEager,
                        _ => LogicalOp.Xor,
                    };
                    return Track(new LogicalExpr(eager, left, Expr(rightOp)), syntax);
                }
                throw Reject("integer bitwise operator", syntax);
        }
        var op = kind switch
        {
            BinaryOperatorKind.Add => BinaryOp.Add,
            BinaryOperatorKind.Subtract => BinaryOp.Sub,
            BinaryOperatorKind.Multiply => BinaryOp.Mul,
            BinaryOperatorKind.Divide => BinaryOp.Div,
            BinaryOperatorKind.Remainder => BinaryOp.Rem,
            _ => throw Reject("unsupported operator", syntax, kind.ToString()),
        };
        if (type == VirType.Decimal)
        {
            return DecimalArithmetic(op, left, rightOp, syntax);
        }
        if (type is not PrimitiveType { Kind: VirPrimitive.Int32 or VirPrimitive.Int64 })
        {
            throw Reject(clrType?.TypeKind == TypeKind.Enum ? "enum arithmetic" : "unsupported operator", syntax, kind.ToString());
        }
        var right = Expr(rightOp);
        if (left.Type != type || right.Type != type)
        {
            throw Reject("enum arithmetic", syntax);
        }
        // `/` and `%` throw on a zero divisor and on MinValue / -1 in any context (KTD6), so their node is always `wrap`.
        // A theorem statement is a Prop: a raising `/` or `%` there is rejected through effect inference (KTD11), and one by
        // a constant other than 0 and -1 cannot raise, so it is pure and translates as Lean's `/` and `%` (M6 U9).
        var overflow = op is BinaryOp.Div or BinaryOp.Rem ? VirOverflow.Wrap : Overflow(isChecked, syntax);
        return Track(new BinaryExpr(type, op, overflow, left, right), syntax);
    }

    /// <summary>
    /// <c>+</c> and <c>-</c> on <c>decimal</c>, which throw <c>OverflowException</c> in any context, so their node is always
    /// <c>checked</c> (KTD7). Multiplication, division and remainder wait for M7.
    /// </summary>
    private BinaryExpr DecimalArithmetic(BinaryOp op, VirExpr left, IOperation rightOp, SyntaxNode syntax)
    {
        if (op is not (BinaryOp.Add or BinaryOp.Sub))
        {
            throw Reject("decimal operator other than + and -", syntax, op.ToString());
        }
        var right = Expr(rightOp);
        if (left.Type != VirType.Decimal || right.Type != VirType.Decimal)
        {
            throw Reject("unsupported operator", syntax);
        }
        return Track(new BinaryExpr(VirType.Decimal, op, VirOverflow.Checked, left, right), syntax);
    }

    private static CompareOp CompareOpOf(BinaryOperatorKind kind) =>
        kind switch
        {
            BinaryOperatorKind.Equals => CompareOp.Eq,
            BinaryOperatorKind.NotEquals => CompareOp.Ne,
            BinaryOperatorKind.LessThan => CompareOp.Lt,
            BinaryOperatorKind.LessThanOrEqual => CompareOp.Le,
            BinaryOperatorKind.GreaterThan => CompareOp.Gt,
            _ => CompareOp.Ge,
        };

    private CompareExpr Comparison(IBinaryOperation b)
    {
        var syntax = b.Syntax;
        var op = CompareOpOf(b.OperatorKind);
        bool equality = op is CompareOp.Eq or CompareOp.Ne;
        var left = b.LeftOperand;
        var right = b.RightOperand;

        // Reference equality on a closed class: both operands are implicitly converted to object.
        if (equality && Unwrapped(left) is { } l && Unwrapped(right) is { } r
            && Symbols.Shape(l.Type!) == TypeShape.ClosedClass && SymbolEqualityComparer.Default.Equals(l.Type, r.Type))
        {
            return Compared(op, CompareKind.Closed, Expr(l), Expr(r), syntax);
        }
        if (left is ILiteralOperation { Type: null } || right is ILiteralOperation { Type: null }
            || left is IConversionOperation { Operand: ILiteralOperation { Type: null } } || right is IConversionOperation { Operand: ILiteralOperation { Type: null } })
        {
            throw Reject("null", syntax);
        }
        var type = left.Type;
        if (type is null)
        {
            throw Reject("null", syntax);
        }
        CompareKind kind;
        switch (Symbols.Shape(type))
        {
            case TypeShape.OpenEnum:
                kind = CompareKind.Enum;
                break;
            case TypeShape.ClosedEnum:
                if (!equality)
                {
                    throw Reject("relational comparison over a closed type", syntax);
                }
                kind = CompareKind.Closed;
                break;
            default:
                switch (Symbols.Primitive(type))
                {
                    case VirPrimitive.Int32 or VirPrimitive.Int64:
                        kind = CompareKind.Int;
                        break;
                    case VirPrimitive.Bool when equality:
                        kind = CompareKind.Bool;
                        break;
                    case null when type.SpecialType == SpecialType.System_Decimal:
                        // Numeric: 1.0m == 1.00m (KTD7).
                        kind = CompareKind.Decimal;
                        break;
                    default:
                        MapType(type, annotated: false, syntax);
                        throw Reject("unsupported comparison", syntax, Symbols.Display(type));
                }
                break;
        }
        var lv = Expr(left);
        var rv = Expr(right);
        if (lv.Type != rv.Type)
        {
            throw Reject("unsupported comparison", syntax);
        }
        return Track(new CompareExpr(op, kind, lv, rv), syntax);
    }

    /// <summary>
    /// A comparison of two values, rejected when either may be null: comparing with <c>null</c> is a null test, and any
    /// other equality on a nullable value is left out like a lifted one (#76).
    /// </summary>
    private CompareExpr Compared(CompareOp op, CompareKind kind, VirExpr l, VirExpr r, SyntaxNode syntax)
    {
        if (l.Type is NullableType || r.Type is NullableType)
        {
            throw Reject("lifted comparison", syntax);
        }
        return Track(new CompareExpr(op, kind, l, r), syntax);
    }

    /// <summary>The operand of an implicit reference conversion to <c>object</c>, as Roslyn writes reference equality.</summary>
    private static IOperation? Unwrapped(IOperation op) =>
        op is IConversionOperation { IsImplicit: true, Conversion.IsReference: true, Operand: { Type: not null } inner } ? inner : null;

    private CompareExpr UserOperator(IBinaryOperation b, IMethodSymbol method)
    {
        var syntax = b.Syntax;
        var type = method.ContainingType;
        bool equality = b.OperatorKind is BinaryOperatorKind.Equals or BinaryOperatorKind.NotEquals;
        var op = CompareOpOf(b.OperatorKind);
        if (equality && Symbols.Shape(type) == TypeShape.Record && method.IsImplicitlyDeclared)
        {
            return Compared(op, CompareKind.Record, Expr(b.LeftOperand), Expr(b.RightOperand), syntax);
        }
        if (equality && Symbols.Shape(type) == TypeShape.ClosedClass)
        {
            // Modelled by identity; the type unit records that its own equality agrees (KTD11).
            return Compared(op, CompareKind.Closed, Expr(b.LeftOperand), Expr(b.RightOperand), syntax);
        }
        if (equality && InheritedClosedOperands(b, type) is var (left, right))
        {
            // A base class's operator on two instances of one closed class (#32): modelled by identity like the class's
            // own, with the same assumption, since HasOwnEquality counts base classes.
            return Compared(op, CompareKind.Closed, Expr(left), Expr(right), syntax);
        }
        throw Reject("user-defined operator", syntax, Symbols.Display(method));
    }

    /// <summary>
    /// The operands of a user-defined equality declared on a base class of a closed class, when both are instances of that
    /// closed class implicitly converted to the operator's parameter type; null otherwise.
    /// </summary>
    private static (IOperation Left, IOperation Right)? InheritedClosedOperands(IBinaryOperation b, INamedTypeSymbol declaring)
    {
        if (ClosedOperand(b.LeftOperand) is not { } left || ClosedOperand(b.RightOperand) is not { } right
            || !SymbolEqualityComparer.Default.Equals(left.Type, right.Type))
        {
            return null;
        }
        for (var t = ((INamedTypeSymbol)left.Type!).BaseType; t is not null; t = t.BaseType)
        {
            if (SymbolEqualityComparer.Default.Equals(t, declaring))
            {
                return (left, right);
            }
        }
        return null;

        static IOperation? ClosedOperand(IOperation op) =>
            op is IConversionOperation { IsImplicit: true, Conversion: { IsReference: true, IsUserDefined: false }, Operand: { Type: { } inner } operand }
                && Symbols.Shape(inner) == TypeShape.ClosedClass
                ? operand
                : null;
    }

    private VirExpr Unary(IUnaryOperation u)
    {
        var syntax = u.Syntax;
        if (u.OperatorMethod is not null)
        {
            throw Reject("user-defined operator", syntax);
        }
        if (u.IsLifted)
        {
            throw Reject("lifted arithmetic", syntax);
        }
        switch (u.OperatorKind)
        {
            case UnaryOperatorKind.Not:
                return Track(new NotExpr(Expr(u.Operand)), syntax);
            case UnaryOperatorKind.BitwiseNegation:
                throw Reject("integer bitwise operator", syntax);
            case UnaryOperatorKind.Minus or UnaryOperatorKind.Plus:
                {
                    var type = MapType(u.Type, annotated: false, syntax);
                    if (type is not PrimitiveType { Kind: VirPrimitive.Int32 or VirPrimitive.Int64 or VirPrimitive.Decimal })
                    {
                        throw Reject("unsupported operator", syntax, u.OperatorKind.ToString());
                    }
                    var overflow = VirOverflow.Wrap;

                    // Negating a decimal flips its sign bit, which cannot overflow (KTD7), and unary plus cannot either.
                    if (u.OperatorKind == UnaryOperatorKind.Minus && type != VirType.Decimal)
                    {
                        overflow = Overflow(u.IsChecked, syntax);
                    }
                    var operand = Expr(u.Operand);
                    var op = u.OperatorKind == UnaryOperatorKind.Minus ? UnaryOp.Neg : UnaryOp.Plus;
                    return Track(new UnaryExpr(type, op, overflow, operand), syntax);
                }
            default:
                throw Reject("unsupported operator", syntax, u.OperatorKind.ToString());
        }
    }

    private VirExpr Conversion(IConversionOperation c)
    {
        var syntax = c.Syntax;
        if (c.Operand is IThrowOperation t)
        {
            return ThrowExpression(t, MapType(c.Type, annotated: false, syntax));
        }
        if (c.Operand.Type is null && IsNullLiteral(c.Operand))
        {
            return NullLiteral(c);
        }
        if (c.Operand.Type is null)
        {
            throw Reject("null", syntax);
        }
        if (c.OperatorMethod is not null)
        {
            throw Reject("user-defined conversion", syntax);
        }
        if (c.Conversion.IsIdentity)
        {
            return Expr(c.Operand);
        }

        // A target-typed `b ? a : null` or switch expression: its branches carry the conversions.
        if (c.IsImplicit && c.Operand is IConditionalOperation or ISwitchExpressionOperation
            && SymbolEqualityComparer.Default.Equals(c.Type, c.Operand.Type))
        {
            return Expr(c.Operand);
        }
        var to = MapType(c.Type, annotated: false, syntax);
        var fromType = c.Operand.Type;
        var from = MapType(fromType, annotated: false, c.Operand.Syntax);
        var toType = c.Type!;
        if (c.Conversion.IsNullable)
        {
            // T to T? wraps the value; (T)x on a T? reads x.Value, which throws on null (#76). Anything else changes the
            // value type too, which M6 leaves out.
            if (to is NullableType wrapped && wrapped.Value == from)
            {
                return Track(new ConvertExpr(from, to, VirOverflow.Wrap, Expr(c.Operand)), syntax);
            }
            if (from is NullableType read && read.Value == to)
            {
                var operand = Expr(c.Operand);
                return Unwrap(to, UnwrapKind.Value, operand, syntax);
            }
            throw Reject("unsupported conversion", syntax, $"{Symbols.Display(fromType)} to {Symbols.Display(toType)}");
        }
        if (from == VirType.Int32 && to == VirType.Int64)
        {
            // Widening cannot overflow, so a checked widening is accepted (KTD15).
            return Track(new ConvertExpr(from, to, VirOverflow.Wrap, Expr(c.Operand)), syntax);
        }
        if (from == VirType.Int64 && to == VirType.Int32)
        {
            var overflow = Overflow(c.IsChecked, syntax);
            return Track(new ConvertExpr(from, to, overflow, Expr(c.Operand)), syntax);
        }
        if (Symbols.Shape(fromType) == TypeShape.OpenEnum && IsUnderlying(fromType, toType))
        {
            return Track(new ConvertExpr(from, to, VirOverflow.Wrap, Expr(c.Operand)), syntax);
        }
        if (Symbols.Shape(toType) == TypeShape.OpenEnum && IsUnderlying(toType, fromType))
        {
            return Track(new ConvertExpr(from, to, VirOverflow.Wrap, Expr(c.Operand)), syntax);
        }
        throw Reject("unsupported conversion", syntax, $"{Symbols.Display(fromType)} to {Symbols.Display(toType)}");
    }

    private static bool IsUnderlying(ITypeSymbol enumType, ITypeSymbol other) =>
        enumType is INamedTypeSymbol { EnumUnderlyingType: { } u } && SymbolEqualityComparer.Default.Equals(u, other);

    private VirList<VirExpr> Arguments(IMethodSymbol method, IEnumerable<IArgumentOperation> arguments, SyntaxNode at)
    {
        var byOrdinal = new VirExpr?[method.Parameters.Length];
        foreach (var argument in arguments)
        {
            if (argument.ArgumentKind == ArgumentKind.ParamArray || argument.Parameter is null)
            {
                throw Reject("params argument", argument.Syntax);
            }
            // A nullable argument for a non-nullable parameter is a checked unwrap (KTD5).
            var parameter = argument.Parameter;
            byOrdinal[parameter.Ordinal] = FitDeclared(Expr(argument.Value), parameter.Type, Annotated(parameter), argument.Value.Syntax);
        }
        if (byOrdinal.Any(a => a is null))
        {
            throw Reject("unsupported call", at);
        }
        // An awaited or external call changes the world, so it must run in the order written (M6 KTD4, U18).
        if (Reordered(arguments, byOrdinal))
        {
            throw Unsupported(
                "named arguments out of order with a dependency call",
                at,
                "An argument awaits or calls a dependency, and the named arguments are not in parameter order: write them in parameter order, so they run in the order the model runs them.");
        }
        // Other arguments cannot change the world, so putting them in parameter order changes nothing.
        return new VirList<VirExpr>(byOrdinal.Select(a => a!));
    }

    /// <param name="call">The call.</param>
    /// <param name="awaited">Whether the call is the direct operand of <c>await</c>, the one place a task may be made (KTD22).</param>
    private VirExpr Invocation(IInvocationOperation call, bool awaited = false)
    {
        var syntax = call.Syntax;
        var target = call.TargetMethod;
        if (target.MethodKind == MethodKind.LocalFunction)
        {
            throw Reject("local function", syntax);
        }
        if (Symbols.IsNamed(target, "Warrant.Spec", "Implies"))
        {
            if (!_inTheorem)
            {
                throw Reject("Spec.Implies outside a theorem statement", syntax, id: DiagnosticIds.MalformedSpec);
            }
            var args = Arguments(target, call.Arguments, syntax);
            return Track(new ImpliesExpr(args[0], args[1]), syntax);
        }
        if (Symbols.IsNamed(target, "Warrant.Prove", "That"))
        {
            throw Reject("Prove.That outside a theorem statement", syntax, id: DiagnosticIds.MalformedSpec);
        }
        if (Symbols.IsNamed(target, "Warrant.Spec", "ForAll") || Symbols.IsNamed(target, "Warrant.Spec", "Exists"))
        {
            return Quantifier(call);
        }
        if (IsDecreases(call))
        {
            throw DecreasesNotFirst(syntax, outOfOrder: false);
        }
        if (IsSpec(call, "Requires") || IsSpec(call, "NoThrow") || IsSpec(call, "Ensures") || IsSpec(call, "Assert"))
        {
            throw ContractNotAStatement(call);
        }
        if (IsScriptMember(target))
        {
            throw MalformedScript("proof script outside a theorem", syntax, $"{Symbols.Display(target)} is valid only in a theorem's .By(...) script");
        }
        if (Symbols.IsTheorem(target))
        {
            throw new RejectedException(new Rejection(
                DiagnosticIds.CallsTheorem, Symbols.Key(target), syntax.GetLocation(), $"A [Theorem] cannot be called: {Symbols.Display(target)}."));
        }
        if (IsTaskMember(target))
        {
            throw TaskMember(target, syntax);
        }
        if (call.Instance is { } receiver && IsState(receiver))
        {
            return Awaited(External(call, receiver), awaited, syntax);
        }
        if (call.Instance is IInstanceReferenceOperation { Type: { } self } && Symbols.Shape(self) != TypeShape.Record)
        {
            throw MemberAccessOnThis(target, syntax);
        }
        if (!InSource(target) && ModelledMembers.Contains(Symbols.Key(target)))
        {
            return Modelled(call);
        }
        if (target is { Name: "GetValueOrDefault", Parameters.Length: 0, IsStatic: false }
            && target.ContainingType.OriginalDefinition.SpecialType == SpecialType.System_Nullable_T)
        {
            // x.GetValueOrDefault() is x ?? default(T).
            var value = Expr(call.Instance ?? throw Reject("unsupported call", syntax));
            if (value.Type is not NullableType { Value: var valueType })
            {
                throw Reject("unsupported call", syntax);
            }
            return Track(new CoalesceExpr(valueType, value, Track(DefaultOf(valueType), syntax)), syntax);
        }
        if (!Symbols.IsVerified(target) || !InSource(target))
        {
            throw NotVerified(target, syntax);
        }
        if (target.IsGenericMethod)
        {
            throw Reject("generic member", syntax);
        }
        if (!target.IsStatic && target.ContainingType.TypeKind == TypeKind.Class && Symbols.Shape(target.ContainingType) == TypeShape.Other)
        {
            // A class's verified instance method has no receiver in its unit: only its dependencies, which the caller has none of.
            throw Reject("call to an instance method of a class", syntax, Symbols.Display(target));
        }
        var key = Symbols.Key(target);
        var parts = new List<VirExpr>();
        if (!target.IsStatic)
        {
            parts.Add(Dereferenced(call.Instance ?? throw Reject("unsupported call", syntax)));
        }
        parts.AddRange(Arguments(target, call.Arguments, syntax));
        var type = MapReturn(target.ReturnType, target.ReturnNullableAnnotation == NullableAnnotation.Annotated, syntax);
        Deps.Add(key);
        Calls.Add(key);
        return Awaited(Track(new CallExpr(type, key, new VirList<VirExpr>(parts)), syntax), awaited, syntax);
    }

    /// <summary>
    /// A call to a modelled BCL member (KTD23). One that can throw (<see cref="Effects.ThrowingModelledMembers"/>) makes
    /// the unit raising, and a theorem statement with one is rejected through effect inference (KTD11).
    /// </summary>
    private ModelledCallExpr Modelled(IInvocationOperation call)
    {
        var syntax = call.Syntax;
        var target = call.TargetMethod;
        var key = Symbols.Key(target);
        var type = MapType(target.ReturnType, annotated: false, syntax);
        return Track(new ModelledCallExpr(type, key, Arguments(target, call.Arguments, syntax)), syntax);
    }

    /// <summary>
    /// The thrown type's key for <c>throw new T(...)</c> (KTD4). The exception's arguments are not modelled, so each must be
    /// a constant or a parameter, which cannot raise; and <c>T</c> must be a <c>System</c> exception type or a plain
    /// subclass of one (<see cref="IsPlainSubclass"/>), so building it throws nothing but itself.
    /// </summary>
    private string Thrown(IThrowOperation t)
    {
        var syntax = t.Syntax;
        var value = t.Exception;
        if (value is null)
        {
            throw Reject("rethrow", syntax);
        }
        while (value is IConversionOperation { IsImplicit: true, OperatorMethod: null, Conversion.IsReference: true } conversion)
        {
            value = conversion.Operand;
        }
        if (value is not IObjectCreationOperation { Constructor: { } constructor, Type: INamedTypeSymbol type, Initializer: null } create)
        {
            throw Reject("throw of a value other than a new exception", syntax);
        }
        foreach (var argument in create.Arguments)
        {
            if (argument.Syntax.DescendantNodesAndSelf().FirstOrDefault(IsForgiving) is { } forgiving)
            {
                throw Reject("null-forgiving operator", forgiving);
            }
            if (!ConstantOrParameter(argument.Value, _parameters.Keys))
            {
                throw Reject("exception argument that is not a constant or a parameter", argument.Syntax);
            }
        }
        if (type.IsGenericType || !(IsSystemException(type) || IsPlainSubclass(constructor)))
        {
            throw Reject("exception type that is not a System exception or a plain subclass of one", syntax, Symbols.Display(type));
        }
        return Symbols.Key(type);
    }

    /// <summary>A throw expression, of the type its context expects.</summary>
    public ThrowExpr ThrowExpression(IThrowOperation t, VirType type) => Track(new ThrowExpr(type, Thrown(t)), t.Syntax);

    /// <summary>A constant, or a reference to one of <paramref name="parameters"/>, under implicit built-in conversions.</summary>
    private static bool ConstantOrParameter(IOperation value, IEnumerable<IParameterSymbol> parameters)
    {
        while (value is IConversionOperation { IsImplicit: true, OperatorMethod: null } conversion)
        {
            value = conversion.Operand;
        }
        return value.ConstantValue.HasValue
            || (value is IParameterReferenceOperation p && parameters.Contains(p.Parameter, SymbolEqualityComparer.Default));
    }

    /// <summary>
    /// An exception type of the framework: in a <c>System</c> namespace, from a framework assembly rather than this
    /// compilation or a referenced project, and derived from <c>System.Exception</c>.
    /// </summary>
    private bool IsSystemException(INamedTypeSymbol type)
    {
        var ns = type.ContainingNamespace?.ToDisplayString() ?? "";
        var assembly = type.ContainingAssembly?.Name ?? "";
        bool framework = assembly is "mscorlib" or "netstandard" or "System" || assembly.StartsWith("System.", StringComparison.Ordinal);
        return (ns == "System" || ns.StartsWith("System.", StringComparison.Ordinal))
            && framework
            && !InSource(type)
            && DerivesFromException(type);
    }

    private static bool DerivesFromException(INamedTypeSymbol type)
    {
        for (var t = type; t is not null; t = t.BaseType)
        {
            if (t.ToDisplayString() == "System.Exception")
            {
                return true;
            }
        }
        return false;
    }

    /// <summary>
    /// A constructor of an exception type declared in this compilation whose body is empty and which chains, with constants
    /// and its own parameters, to a constructor of its base class, a <c>System</c> exception. The type has no primary
    /// constructor, field or property initializer and static constructor, which would also run when it is built.
    /// </summary>
    private bool IsPlainSubclass(IMethodSymbol constructor)
    {
        var type = constructor.ContainingType;
        if (!InSource(type) || type.BaseType is not { } baseType || !IsSystemException(baseType))
        {
            return false;
        }
        if (type.StaticConstructors.Any(c => !c.IsImplicitlyDeclared))
        {
            return false;
        }
        foreach (var declaration in type.DeclaringSyntaxReferences.Select(r => r.GetSyntax()))
        {
            if (declaration is TypeDeclarationSyntax { ParameterList: not null })
            {
                return false;
            }
            if (declaration is TypeDeclarationSyntax typeSyntax && typeSyntax.Members.Any(m =>
                (m is FieldDeclarationSyntax f
                    && !f.Modifiers.Any(Microsoft.CodeAnalysis.CSharp.SyntaxKind.ConstKeyword)
                    && f.Declaration.Variables.Any(v => v.Initializer is not null))
                || m is PropertyDeclarationSyntax { Initializer: not null }))
            {
                return false;
            }
        }
        if (constructor.DeclaringSyntaxReferences.Select(r => r.GetSyntax()).SingleOrDefault() is not ConstructorDeclarationSyntax
            {
                Body.Statements.Count: 0,
                ExpressionBody: null,
                Initializer: { } initializer,
            } syntax
            || !initializer.ThisOrBaseKeyword.IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.BaseKeyword))
        {
            return false;
        }
        if (_context.Model(syntax.SyntaxTree).GetOperation(syntax) is not IConstructorBodyOperation
            {
                Initializer: IExpressionStatementOperation { Operation: IInvocationOperation chained },
            }
            || !SymbolEqualityComparer.Default.Equals(chained.TargetMethod.ContainingType, baseType))
        {
            return false;
        }
        return chained.Arguments.All(a => ConstantOrParameter(a.Value, constructor.Parameters));
    }

    private bool InSource(ISymbol symbol) =>
        SymbolEqualityComparer.Default.Equals(symbol.ContainingAssembly, _context.Compilation.Assembly);

    private static RejectedException NotVerified(ISymbol target, SyntaxNode syntax) =>
        new(new Rejection(
            DiagnosticIds.NotVerified,
            Symbols.Key(target),
            syntax.GetLocation(),
            $"Verified code may call only verified or modelled members, not {Symbols.Display(target)}."));

    private VirExpr PropertyRead(IPropertyReferenceOperation prop)
    {
        var syntax = prop.Syntax;
        var property = prop.Property;
        var owner = property.ContainingType;
        if (property.IsIndexer)
        {
            throw Reject("indexer", syntax);
        }
        if (prop.Instance is { } state && IsState(state))
        {
            throw NotACall(state, "property of a dependency");
        }
        if (prop.Instance is IInstanceReferenceOperation { Type: { } self } && Symbols.Shape(self) != TypeShape.Record)
        {
            throw MemberAccessOnThis(property, syntax);
        }
        if (IsTaskMember(property))
        {
            throw TaskMember(property, syntax);
        }
        if (owner.OriginalDefinition.SpecialType == SpecialType.System_Nullable_T && !property.IsStatic
            && property.Name is "HasValue" or "Value")
        {
            // x.HasValue is not (x is null); x.Value throws InvalidOperationException on null (KTD5).
            var value = Expr(prop.Instance ?? throw Reject("unsupported property read", syntax));
            if (value.Type is not NullableType nullable)
            {
                throw Reject("unsupported property read", syntax);
            }
            return property.Name == "HasValue"
                ? NullTest(value, negated: true, nullSyntax: syntax, syntax)
                : Unwrap(nullable.Value, UnwrapKind.Value, value, syntax);
        }
        if (Symbols.IsVerified(property) && InSource(property))
        {
            var key = Symbols.Key(property);
            var parts = new List<VirExpr>();
            if (!property.IsStatic)
            {
                parts.Add(Dereferenced(prop.Instance ?? throw Reject("unsupported call", syntax)));
            }
            var type = MapType(property.Type, Annotated(property), syntax);
            Deps.Add(key);
            Calls.Add(key);
            return Track(new CallExpr(type, key, new VirList<VirExpr>(parts)), syntax);
        }
        if (Symbols.Shape(owner) == TypeShape.ClosedClass)
        {
            if (property.IsStatic && SymbolEqualityComparer.Default.Equals(property.Type, owner))
            {
                return Track(new MemberExpr(MapType(owner, annotated: false, syntax), property.Name), syntax);
            }
            if (!property.IsStatic)
            {
                throw Reject("closed class instance member", syntax, Symbols.Display(property));
            }
        }
        if (Symbols.Shape(owner) == TypeShape.Record && !property.IsStatic && Symbols.IsPositional(property))
        {
            var target = Dereferenced(prop.Instance ?? throw Reject("unsupported property read", syntax));
            var type = MapType(property.Type, Annotated(property), syntax);
            return Track(new GetExpr(type, property.Name, target), syntax);
        }
        throw NotVerified(property, syntax);
    }

    private MemberExpr FieldRead(IFieldReferenceOperation f)
    {
        var syntax = f.Syntax;
        var field = f.Field;
        var owner = field.ContainingType;
        if (Symbols.Shape(owner) == TypeShape.ClosedClass)
        {
            if (field.IsStatic && SymbolEqualityComparer.Default.Equals(field.Type, owner))
            {
                return Track(new MemberExpr(MapType(owner, annotated: false, syntax), field.Name), syntax);
            }
            if (!field.IsStatic)
            {
                throw Reject("closed class instance member", syntax, Symbols.Display(field));
            }
        }
        if (IsState(f))
        {
            throw NotACall(f, "dependency used other than to call a member");
        }
        throw NotVerified(field, syntax);
    }

    private NewExpr Creation(IObjectCreationOperation create)
    {
        var syntax = create.Syntax;
        if (create.Type is not INamedTypeSymbol type || Symbols.Shape(type) != TypeShape.Record || create.Constructor is not { } ctor)
        {
            throw Reject("object creation", syntax, create.Type is null ? null : Symbols.Display(create.Type));
        }
        if (create.Initializer is not null)
        {
            throw Reject("object initializer", syntax);
        }
        if (!SymbolEqualityComparer.Default.Equals(Symbols.PrimaryConstructor(type), ctor))
        {
            throw Reject("constructor other than the primary constructor", syntax);
        }
        var vtype = MapType(type, annotated: false, syntax);
        return Track(new NewExpr(vtype, Arguments(ctor, create.Arguments, syntax)), syntax);
    }

    private WithExpr With(IWithOperation with)
    {
        var syntax = with.Syntax;
        if (with.Type is null || Symbols.Shape(with.Type) != TypeShape.Record)
        {
            throw Reject("with on a type that is not a record", syntax);
        }
        var type = MapType(with.Type, annotated: false, syntax);
        var @base = Dereferenced(with.Operand);
        var updates = new List<WithUpdate>();
        foreach (var init in with.Initializer.Initializers)
        {
            if (init is not ISimpleAssignmentOperation { Target: IPropertyReferenceOperation { Property: var p } } assign
                || !Symbols.IsPositional(p))
            {
                throw Reject("with on a property that is not positional", init.Syntax);
            }
            var value = FitDeclared(Expr(assign.Value), p.Type, Annotated(p), assign.Value.Syntax);
            updates.Add(new WithUpdate(p.Name, value));
        }
        return Track(new WithExpr(type, @base, new VirList<WithUpdate>(updates)), syntax);
    }

    private SwitchExpr SwitchExpression(ISwitchExpressionOperation sw)
    {
        var syntax = sw.Syntax;
        var type = MapType(sw.Type, annotated: false, syntax);
        var scrutinee = NotNullableScrutinee(Expr(sw.Value), syntax);
        var arms = new List<SwitchArm>();
        foreach (var arm in sw.Arms)
        {
            if (arm.Guard is not null)
            {
                throw Reject("switch arm guard", arm.Syntax);
            }
            arms.Add(new SwitchArm(Pattern(arm.Pattern), Expr(arm.Value)));
        }
        type = Join(type, arms.Select(a => a.Value));
        for (int i = 0; i < arms.Count; i++)
        {
            arms[i] = new SwitchArm(arms[i].Pattern, FitTo(arms[i].Value, type, sw.Arms[i].Value.Syntax));
        }

        // Without exceptions, a switch expression must match every value (KTD15).
        bool exhaustive = sw.Arms.Any(a => a.Pattern is IDiscardPatternOperation);
        var valueType = sw.Value.Type;
        if (!exhaustive && valueType is INamedTypeSymbol named && Symbols.Shape(named) == TypeShape.ClosedEnum)
        {
            var covered = new HashSet<long>();
            foreach (var arm in sw.Arms)
            {
                Cover(arm.Pattern, covered);
            }
            exhaustive = named.GetMembers().OfType<IFieldSymbol>()
                .Where(m => m.HasConstantValue)
                .All(m => covered.Contains(Symbols.ToInt64(m.ConstantValue!)));
        }
        if (!exhaustive)
        {
            throw Reject(
                valueType is not null && Symbols.Shape(valueType) == TypeShape.OpenEnum
                    ? "non-exhaustive switch over an open enum"
                    : "non-exhaustive switch expression",
                syntax);
        }
        return Track(new SwitchExpr(type, scrutinee, new VirList<SwitchArm>(arms)), syntax);
    }

    private static void Cover(IPatternOperation pattern, HashSet<long> covered)
    {
        switch (pattern)
        {
            case IConstantPatternOperation { Value.ConstantValue: { HasValue: true, Value: { } v } }:
                covered.Add(Symbols.ToInt64(v));
                break;
            case IBinaryPatternOperation { OperatorKind: BinaryOperatorKind.Or } or:
                Cover(or.LeftPattern, covered);
                Cover(or.RightPattern, covered);
                break;
        }
    }

    private VirPattern Pattern(IPatternOperation pattern)
    {
        var syntax = pattern.Syntax;
        switch (pattern)
        {
            case IDiscardPatternOperation:
                return Track(new DiscardPattern(), syntax);
            case IConstantPatternOperation c:
                return Track(new ConstPattern(Constant(c.Value)), syntax);
            case IRelationalPatternOperation r:
                {
                    if (Symbols.IsClosed(pattern.InputType) || Symbols.IsClosed(r.Value.Type))
                    {
                        throw Reject("relational pattern over a closed type", syntax);
                    }
                    var op = r.OperatorKind switch
                    {
                        BinaryOperatorKind.LessThan => RelationalOp.Lt,
                        BinaryOperatorKind.LessThanOrEqual => RelationalOp.Le,
                        BinaryOperatorKind.GreaterThan => RelationalOp.Gt,
                        BinaryOperatorKind.GreaterThanOrEqual => RelationalOp.Ge,
                        _ => throw Reject("unsupported pattern", syntax),
                    };
                    return Track(new RelationalPattern(op, Constant(r.Value)), syntax);
                }
            case IBinaryPatternOperation { OperatorKind: BinaryOperatorKind.And } when Symbols.IsClosed(pattern.InputType):
            case INegatedPatternOperation when Symbols.IsClosed(pattern.InputType):
                // A switch over a closed type is its recursor: each arm names constructors, so only
                // constants, `or` of constants and `_` can be placed (docs/m4/05).
                throw Reject("and/not pattern over a closed type", syntax);
            case IBinaryPatternOperation b:
                {
                    var l = Pattern(b.LeftPattern);
                    var r = Pattern(b.RightPattern);
                    return b.OperatorKind == BinaryOperatorKind.And
                        ? Track(new AndPattern(l, r), syntax)
                        : Track(new OrPattern(l, r), syntax);
                }
            case INegatedPatternOperation n:
                return Track(new NotPattern(Pattern(n.Pattern)), syntax);
            default:
                throw Reject("unsupported pattern", syntax, pattern.Kind.ToString());
        }
    }

    private T Track<T>(T node, SyntaxNode syntax)
        where T : VirNode
    {
        _syntax[node] = syntax;
        return node;
    }
}
