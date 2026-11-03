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
    private readonly Dictionary<object, SyntaxNode> _syntax = new(ReferenceComparer.Instance);
    private readonly bool _inTheorem;

    /// <summary>The next local ID: locals and bound variables share one numbering, unique within the unit.</summary>
    private int _nextLocal;

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

    /// <summary>Maps a declared type (a parameter, return, local or field type) to VIR, recording the type units it uses.</summary>
    public VirType MapType(ITypeSymbol? type, bool annotated, SyntaxNode? at)
    {
        if (type is null)
        {
            throw Reject("null", at);
        }
        if (type is INamedTypeSymbol { OriginalDefinition.SpecialType: SpecialType.System_Nullable_T } || (annotated && type.IsReferenceType))
        {
            throw Reject("nullable type", at, Symbols.Display(type));
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
                throw Reject("decimal", at);
            case SpecialType.System_Single or SpecialType.System_Double:
                throw Reject("floating point", at);
        }
        if (Symbols.Shape(type) != TypeShape.Other && type is INamedTypeSymbol named)
        {
            if (!SymbolEqualityComparer.Default.Equals(named.ContainingAssembly, _context.Compilation.Assembly))
            {
                throw Reject("type defined outside the compilation", at, Symbols.Display(type));
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

    /// <summary>A member's block body, whose first statement may be <c>Spec.Decreases</c>.</summary>
    public BlockStmt Body(IBlockOperation block) => Track(new BlockStmt(Statements(block.Operations, measureFirst: true)), block.Syntax);

    private VirList<VirStmt> Statements(IEnumerable<IOperation> operations, bool measureFirst = false)
    {
        var result = new List<VirStmt>();
        bool ended = false;
        bool first = true;
        foreach (var op in operations)
        {
            if (op is IEmptyOperation)
            {
                continue;
            }
            if (op is IExpressionStatementOperation { Operation: IInvocationOperation call } && IsDecreases(call))
            {
                if (!(measureFirst && first))
                {
                    throw DecreasesNotFirst(op.Syntax);
                }
                result.Add(Track(new DecreasesStmt(Measure(call)), op.Syntax));
                first = false;
                continue;
            }
            first = false;
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
            IReturnOperation => true,
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
                return [Track(new ReturnStmt(Expr(value)), r.Syntax)];
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
            case IThrowOperation:
                throw Reject("throw", op.Syntax);
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
                if (declaration.Syntax is VariableDeclarationSyntax { Type: NullableTypeSyntax })
                {
                    throw Reject("nullable type", declaration.Syntax);
                }
                MapType(declarator.Symbol.Type, annotated: false, declarator.Syntax);
                var value = Expr(init);
                int id = _nextLocal++;
                _locals.Add(declarator.Symbol, id);
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

    private AssignStmt ExpressionStatement(IExpressionStatementOperation statement)
    {
        var syntax = statement.Syntax;
        switch (statement.Operation)
        {
            case ISimpleAssignmentOperation a:
                {
                    int id = Local(a.Target, syntax);
                    return Track(new AssignStmt(id, Expr(a.Value)), syntax);
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
                        throw Reject("nullable type", syntax);
                    }
                    if (inc.IsChecked)
                    {
                        throw Reject("checked arithmetic", syntax);
                    }
                    var type = MapType(inc.Target.Type, annotated: false, syntax);
                    if (type is not PrimitiveType { Kind: VirPrimitive.Int32 or VirPrimitive.Int64 })
                    {
                        throw Reject("increment of a non-integer", syntax);
                    }
                    var one = Track(new LitExpr(type, 1), syntax);
                    var op = inc.Kind == OperationKind.Increment ? BinaryOp.Add : BinaryOp.Sub;
                    var value = Track(new BinaryExpr(type, op, VirOverflow.Wrap, Track(new LocalExpr(type, id), inc.Target.Syntax), one), syntax);
                    return Track(new AssignStmt(id, value), syntax);
                }
            case IThrowOperation:
                throw Reject("throw", syntax);
            case { } other:
                // Walk it to report what it is (a call to a theorem, an unverified member), then reject the statement itself.
                Expr(other);
                throw Reject("expression statement", syntax);
            default:
                throw Reject("expression statement", syntax);
        }
    }

    private SwitchStmt SwitchStatement(ISwitchOperation s)
    {
        var scrutinee = Expr(s.Value);
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

        // Constants of int, long and bool are what the IL contains (KTD13).
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
            case IParameterReferenceOperation p when _parameters.TryGetValue(p.Parameter, out int index):
                return Track(new ParamExpr(MapType(p.Type, annotated: false, syntax), index), syntax);
            case ILocalReferenceOperation l when _locals.TryGetValue(l.Local, out int id):
                return Track(new LocalExpr(MapType(l.Type, annotated: false, syntax), id), syntax);
            case IParameterReferenceOperation p when _bound.TryGetValue(p.Parameter, out int bound):
                return Track(new LocalExpr(MapType(p.Type, annotated: false, syntax), bound), syntax);
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
                    var type = MapType(c.Type, annotated: false, syntax);
                    return Track(new CondExpr(type, Expr(c.Condition), Expr(c.WhenTrue), Expr(whenFalse)), syntax);
                }
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
        if (b.IsLifted)
        {
            throw Reject("nullable type", syntax);
        }
        switch (b.OperatorKind)
        {
            case BinaryOperatorKind.Divide:
                throw Reject("division", syntax);
            case BinaryOperatorKind.Remainder:
                throw Reject("remainder", syntax);
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
            case BinaryOperatorKind.Add or BinaryOperatorKind.Subtract or BinaryOperatorKind.Multiply:
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

    private VirExpr Arithmetic(
        BinaryOperatorKind kind, bool isChecked, bool isLifted, VirType type, ITypeSymbol? clrType, VirExpr left, IOperation rightOp, SyntaxNode syntax)
    {
        if (isLifted)
        {
            throw Reject("nullable type", syntax);
        }
        switch (kind)
        {
            case BinaryOperatorKind.Divide:
                throw Reject("division", syntax);
            case BinaryOperatorKind.Remainder:
                throw Reject("remainder", syntax);
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
            _ => throw Reject("unsupported operator", syntax, kind.ToString()),
        };
        if (type is not PrimitiveType { Kind: VirPrimitive.Int32 or VirPrimitive.Int64 })
        {
            throw Reject(clrType?.TypeKind == TypeKind.Enum ? "enum arithmetic" : "unsupported operator", syntax, kind.ToString());
        }
        var right = Expr(rightOp);
        if (left.Type != type || right.Type != type)
        {
            throw Reject("enum arithmetic", syntax);
        }
        if (isChecked)
        {
            throw Reject("checked arithmetic", syntax);
        }
        return Track(new BinaryExpr(type, op, VirOverflow.Wrap, left, right), syntax);
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
            return Track(new CompareExpr(op, CompareKind.Closed, Expr(l), Expr(r)), syntax);
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
            return Track(new CompareExpr(op, CompareKind.Record, Expr(b.LeftOperand), Expr(b.RightOperand)), syntax);
        }
        if (equality && Symbols.Shape(type) == TypeShape.ClosedClass)
        {
            // Modelled by identity; the type unit records that its own equality agrees (KTD11).
            return Track(new CompareExpr(op, CompareKind.Closed, Expr(b.LeftOperand), Expr(b.RightOperand)), syntax);
        }
        throw Reject("user-defined operator", syntax, Symbols.Display(method));
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
            throw Reject("nullable type", syntax);
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
                    if (type is not PrimitiveType { Kind: VirPrimitive.Int32 or VirPrimitive.Int64 })
                    {
                        throw Reject("unsupported operator", syntax, u.OperatorKind.ToString());
                    }
                    if (u.OperatorKind == UnaryOperatorKind.Minus && u.IsChecked)
                    {
                        throw Reject("checked arithmetic", syntax);
                    }
                    var operand = Expr(u.Operand);
                    var op = u.OperatorKind == UnaryOperatorKind.Minus ? UnaryOp.Neg : UnaryOp.Plus;
                    return Track(new UnaryExpr(type, op, VirOverflow.Wrap, operand), syntax);
                }
            default:
                throw Reject("unsupported operator", syntax, u.OperatorKind.ToString());
        }
    }

    private VirExpr Conversion(IConversionOperation c)
    {
        var syntax = c.Syntax;
        if (c.Operand is IThrowOperation)
        {
            throw Reject("throw", syntax);
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
        var to = MapType(c.Type, annotated: false, syntax);
        var fromType = c.Operand.Type;
        var from = MapType(fromType, annotated: false, c.Operand.Syntax);
        var toType = c.Type!;
        if (from == VirType.Int32 && to == VirType.Int64)
        {
            // Widening cannot overflow, so a checked widening is accepted (KTD15).
            return Track(new ConvertExpr(from, to, VirOverflow.Wrap, Expr(c.Operand)), syntax);
        }
        if (from == VirType.Int64 && to == VirType.Int32)
        {
            if (c.IsChecked)
            {
                throw Reject("checked arithmetic", syntax);
            }
            return Track(new ConvertExpr(from, to, VirOverflow.Wrap, Expr(c.Operand)), syntax);
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
            byOrdinal[argument.Parameter.Ordinal] = Expr(argument.Value);
        }
        if (byOrdinal.Any(a => a is null))
        {
            throw Reject("unsupported call", at);
        }
        // Arguments are pure, so putting them in parameter order changes nothing.
        return new VirList<VirExpr>(byOrdinal.Select(a => a!));
    }

    private VirExpr Invocation(IInvocationOperation call)
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
            throw DecreasesNotFirst(syntax);
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
        if (!Symbols.IsVerified(target) || !InSource(target))
        {
            throw NotVerified(target, syntax);
        }
        if (target.IsGenericMethod)
        {
            throw Reject("generic member", syntax);
        }
        var key = Symbols.Key(target);
        var parts = new List<VirExpr>();
        if (!target.IsStatic)
        {
            parts.Add(Expr(call.Instance ?? throw Reject("unsupported call", syntax)));
        }
        parts.AddRange(Arguments(target, call.Arguments, syntax));
        var type = MapType(target.ReturnType, annotated: false, syntax);
        Deps.Add(key);
        Calls.Add(key);
        return Track(new CallExpr(type, key, new VirList<VirExpr>(parts)), syntax);
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
        if (Symbols.IsVerified(property) && InSource(property))
        {
            var key = Symbols.Key(property);
            var parts = new List<VirExpr>();
            if (!property.IsStatic)
            {
                parts.Add(Expr(prop.Instance ?? throw Reject("unsupported call", syntax)));
            }
            var type = MapType(property.Type, annotated: false, syntax);
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
            var target = Expr(prop.Instance ?? throw Reject("unsupported property read", syntax));
            var type = MapType(property.Type, property.NullableAnnotation == NullableAnnotation.Annotated, syntax);
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
        var @base = Expr(with.Operand);
        var updates = new List<WithUpdate>();
        foreach (var init in with.Initializer.Initializers)
        {
            if (init is not ISimpleAssignmentOperation { Target: IPropertyReferenceOperation { Property: var p } } assign
                || !Symbols.IsPositional(p))
            {
                throw Reject("with on a property that is not positional", init.Syntax);
            }
            var value = Expr(assign.Value);
            updates.Add(new WithUpdate(p.Name, value));
        }
        return Track(new WithExpr(type, @base, new VirList<WithUpdate>(updates)), syntax);
    }

    private SwitchExpr SwitchExpression(ISwitchExpressionOperation sw)
    {
        var syntax = sw.Syntax;
        var type = MapType(sw.Type, annotated: false, syntax);
        var scrutinee = Expr(sw.Value);
        var arms = new List<SwitchArm>();
        foreach (var arm in sw.Arms)
        {
            if (arm.Guard is not null)
            {
                throw Reject("switch arm guard", arm.Syntax);
            }
            arms.Add(new SwitchArm(Pattern(arm.Pattern), Expr(arm.Value)));
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
