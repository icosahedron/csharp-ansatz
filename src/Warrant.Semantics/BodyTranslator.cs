using System.Collections.Immutable;
using Warrant.Cic;
using Warrant.Kernel;
using Warrant.Vir;

namespace Warrant.Semantics;

/// <summary>
/// Translates one unit's body or statement. Terms are built with named free variables from a <see cref="LocalContext"/>
/// and closed into de Bruijn form with <see cref="LocalContext.MkLambda(IReadOnlyList{Expr}, Expr, bool)"/>, never by
/// counting indices. Each VIR node has one rule; this file holds the expression and condition rules, and
/// <c>Statements.cs</c> and <c>Switches.cs</c> the others.
/// </summary>
internal sealed partial class BodyTranslator
{
    private readonly TypeTable _types;
    private readonly LocalContext _lctx = new();
    private readonly NameGenerator _ngen = new(Name.From("_warrant"));
    private readonly Dictionary<int, DeclStmt> _locals = [];
    private readonly List<Expr> _params = [];
    private Expr? _self;

    /// <summary>
    /// Whether this is a quantified statement (one with parameters, <c>Spec.ForAll</c> or <c>Spec.Exists</c>): its
    /// <c>&gt;</c> and <c>&gt;=</c> are <c>GT.gt</c> and <c>GE.ge</c>, as Lean elaborates them, so the goals tactics show
    /// read as the C# does (M5a KTD17). Closed statements and function bodies keep M4's swapped <c>&lt;</c> and <c>&lt;=</c>.
    /// </summary>
    private bool _quantified;

    /// <summary>Which callees can raise or state a precondition (M6 KTD11); null when nothing being translated can.</summary>
    private readonly CalleeEffects? _callees;

    public BodyTranslator(TypeTable types, CalleeEffects? callees = null)
    {
        _types = types;
        _callees = callees;
    }

    /// <summary>A function unit's type (<c>∀</c> over <c>self</c> and the parameters) and value (<c>fun</c> over the same).</summary>
    public (Expr Type, Expr Value) Function(VirUnit unit)
    {
        var binders = Binders(unit);
        var returns = ReturnType(unit);
        Expr body;
        switch (unit.Body)
        {
            case BlockStmt block:
                CollectLocals(block);
                body = Statements(block.Stmts, 0, Env.Empty, new Unreachable(returns));
                break;
            case VirExpr e:
                CollectLocals(e);
                body = Value(e, Env.Empty);
                break;
            default:
                throw new TranslationException(unit.Key, "a function has no body.");
        }
        return (_lctx.MkPi(binders, returns), _lctx.MkLambda(binders, body));
    }

    /// <summary>A function's binders as free variables: <c>self</c> for an instance member, then the parameters.</summary>
    private List<Expr> Binders(VirUnit unit)
    {
        var binders = new List<Expr>();
        if (unit.Self is { } self)
        {
            _self = _lctx.MkLocalDecl(_ngen, Name.From("self"), _types.Cic(VirType.Ref(self)));
            binders.Add(_self);
        }
        foreach (var p in unit.Params ?? VirList<VirParam>.Empty)
        {
            var fvar = _lctx.MkLocalDecl(_ngen, Name.From(p.Name), _types.Cic(p.Type));
            _params.Add(fvar);
            binders.Add(fvar);
        }
        return binders;
    }

    private Expr ReturnType(VirUnit unit) =>
        _types.Cic(unit.Returns ?? throw new TranslationException(unit.Key, "a function has no return type."));

    /// <summary>
    /// A theorem's statement, translated as a condition (docs/m4/06, "The statement"). The parameters become free
    /// variables while the claim is translated, then outer <c>∀</c> binders in order, with no instance (M5a KTD17).
    /// </summary>
    public Condition Statement(VirUnit unit) => StatementAndClaim(unit).Statement;

    /// <summary>
    /// A theorem's statement, as <see cref="Statement(VirUnit)"/>, and, when the theorem has parameters and its claim has a
    /// <c>Decidable</c> instance, the claim and instance as functions of the parameters: <c>fun ps => P</c> and
    /// <c>fun ps => D</c>. The engine's counterexample search applies them to concrete values (M5a KTD25).
    /// </summary>
    public (Condition Statement, Condition? Claim) StatementAndClaim(VirUnit unit)
    {
        var statement = unit.Statement ?? throw new TranslationException(unit.Key, "a theorem has no statement.");
        foreach (var p in unit.Params ?? VirList<VirParam>.Empty)
        {
            _params.Add(_lctx.MkLocalDecl(_ngen, Name.From(p.Name), _types.Cic(p.Type)));
        }
        _quantified = _params.Count > 0 || Nodes(statement).Any(n => n is ForAllExpr or ExistsExpr);
        var claim = Cond(statement, Env.Empty);
        if (_params.Count == 0)
        {
            return (claim, null);
        }
        var decidable = claim.Instance is { } instance ? new Condition(_lctx.MkLambda(_params, claim.Prop), _lctx.MkLambda(_params, instance)) : null;
        return (new Condition(_lctx.MkPi(_params, claim.Prop), null), decidable);
    }

    // ---- Values ----

    /// <summary>
    /// An expression as a value (docs/m4/05): a <c>bool</c> expression becomes a <c>Bool</c>. Only an expression that cannot
    /// raise has a value; the monadic translation binds the others (<c>MonadicStatements.cs</c>, M6 U9).
    /// </summary>
    private Expr Value(VirExpr e, Env env)
    {
        if (Effects.Construct(e) is { } construct)
        {
            throw new TranslationException(null, $"the {construct} can raise an exception, so it is translated only in a method that can raise.");
        }
        switch (e)
        {
            case LitExpr l:
                return Literals.Of(_types.Underlying(l.Type), l.Value);
            case ParamExpr p:
                return p.Index >= 0 && p.Index < _params.Count ? _params[p.Index] : throw new TranslationException(null, $"no parameter {p.Index}.");
            case LocalExpr l:
                return env.Get(l.Id);
            case SelfExpr:
                return _self ?? throw new TranslationException(null, "self outside an instance member.");
            case UnaryExpr { Op: UnaryOp.Neg } u:
                RequireWrap(u.Overflow);
                return Operators.Neg(_types.Underlying(u.Type), Value(u.Operand, env));
            case UnaryExpr { Op: UnaryOp.Plus } u:
                return Value(u.Operand, env);
            case BinaryExpr b:
                RequireWrap(b.Overflow);
                return Operators.Binary(b.Op, _types.Underlying(b.Type), Value(b.L, env), Value(b.R, env));
            case LogicalExpr { Op: LogicalOp.And or LogicalOp.AndEager } l:
                return Operators.And(Value(l.L, env), Value(l.R, env));
            case LogicalExpr { Op: LogicalOp.Or or LogicalOp.OrEager } l:
                return Operators.Or(Value(l.L, env), Value(l.R, env));
            case LogicalExpr { Op: LogicalOp.Xor } l:
                return Operators.Xor(Value(l.L, env), Value(l.R, env));
            case NotExpr n:
                return Operators.Not(Value(n.Operand, env));
            case CompareExpr c:
                return Operators.Decide(Compare(c, env));
            case ConvertExpr c:
                return Convert(c, env);
            case CondExpr c:
                {
                    var condition = Cond(c.C, env);
                    var (hThen, hElse) = Hypotheses(condition);
                    var then = InScope(hThen, () => Value(c.Then, env));
                    var @else = InScope(hElse, () => Value(c.Else, env));
                    return IfThenElse(_types.Cic(c.Type), condition, hThen, then, hElse, @else);
                }
            case CallExpr c when _rec is { } rec && string.Equals(c.Target, rec.Key, StringComparison.Ordinal):
                return RecursiveCall(c, env);
            case CallExpr c when _callees is { } callees && callees.Analysis.IsRaising(c.Target):
                throw new TranslationException(null, $"the call to {c.Target} can raise an exception, so it is translated only in a method that can raise.");
            case CallExpr c:
                return Expr.App(Expr.Const(LeanNames.ForKey(c.Target)), [.. c.Args.Select(a => Value(a, env))]);
            case NewExpr n:
                return Expr.App(Expr.Const(LeanNames.Constructor(Key(n.Type))), [.. n.Args.Select(a => Value(a, env))]);
            case GetExpr g:
                return Get(g, Value(g.Target, env));
            case WithExpr w:
                return With(w, Value(w.Base, env), [.. w.Updates.Select(u => Value(u.Value, env))]);
            case MemberExpr m:
                return Expr.Const(LeanNames.Member(Key(m.Type), m.Name));
            case SwitchExpr s:
                return Switch(s, Value(s.Scrutinee, env), _types.Cic(s.Type), arm => Value(arm, env));
            case NullExpr n:
                return Nullables.None(_types.Cic(Nullables.ValueType(n.Type)));
            case IsNullExpr n:
                return Nullables.IsNone(_types.Cic(Nullables.ValueType(n.Operand.Type)), Value(n.Operand, env));
            case CoalesceExpr c:
                return Coalesce(c, Value(c.L, env), Value(c.R, env));
            case ModelledCallExpr m:
                return Modelled(m, [.. m.Args.Select(a => Value(a, env))]);
            case ImpliesExpr:
                throw new TranslationException(null, "Spec.Implies is valid only in a theorem statement.");
            case ForAllExpr or ExistsExpr:
                throw new TranslationException(null, "a quantified claim is not a bool value.");
            default:
                throw new TranslationException(null, $"unsupported expression {e.GetType().Name}.");
        }
    }

    /// <summary>
    /// <c>(long)a</c> is <c>Int32.toInt64 a</c>, <c>(int)a</c> on a <c>long</c> is <c>Int64.toInt32 a</c>, and a cast between an
    /// open enum and its underlying type is free. Narrowing must wrap; checked narrowing needs exceptions (M6).
    /// </summary>
    private Expr Convert(ConvertExpr c, Env env) => Convert(c, Value(c.Operand, env));

    /// <summary>
    /// A conversion that cannot raise, of the operand's value <paramref name="a"/>: as above, or, from <c>T</c> to <c>T?</c>,
    /// <c>Option.some a</c> (M6 KTD5).
    /// </summary>
    private Expr Convert(ConvertExpr c, Expr a)
    {
        if (c.To is NullableType nullable && nullable.Value == c.From)
        {
            return Nullables.Some(_types.Cic(c.From), a);
        }
        var from = _types.Underlying(c.From);
        var to = _types.Underlying(c.To);
        if (c.Overflow == VirOverflow.Checked && from == VirPrimitive.Int64 && to == VirPrimitive.Int32)
        {
            throw new TranslationException(null, "a checked narrowing conversion needs exceptions.");
        }
        return Operators.Convert(from, to, a);
    }

    /// <summary><c>r.F</c>: the field's projection of the record's value <paramref name="target"/>.</summary>
    private Expr Get(GetExpr g, Expr target) =>
        Expr.Proj(LeanNames.ForKey(Key(g.Target.Type)), _types.FieldIndex(g.Target.Type, g.Field), target);

    /// <summary>
    /// <c>r with { F = x }</c> is <c>$mk</c> applied to the updated fields and the base's projections of the others, given
    /// the base's value and each update's value in order.
    /// </summary>
    private Expr With(WithExpr w, Expr @base, IReadOnlyList<Expr> updates)
    {
        var fields = _types.Record(w.Type).Fields;
        foreach (var update in w.Updates)
        {
            _types.FieldIndex(w.Type, update.Field); // throws for a field the record does not have
        }
        var name = LeanNames.ForKey(Key(w.Type));
        var args = new Expr[fields.Count];
        for (int i = 0; i < fields.Count; i++)
        {
            int update = LastIndex(w.Updates, u => string.Equals(u.Field, fields[i].Name, StringComparison.Ordinal));
            args[i] = update < 0 ? Expr.Proj(name, i, @base) : updates[update];
        }
        return Expr.App(Expr.Const(LeanNames.Constructor(Key(w.Type))), args);
    }

    private static int LastIndex<T>(IReadOnlyList<T> items, Func<T, bool> predicate)
    {
        for (int i = items.Count - 1; i >= 0; i--)
        {
            if (predicate(items[i]))
            {
                return i;
            }
        }
        return -1;
    }

    /// <summary>
    /// <c>l ?? r</c> when <c>r</c> cannot raise (M6 KTD5): <c>Warrant.Nullable.coalesce l r</c>, or, when the result is
    /// itself nullable, <c>Option.rec r (fun v =&gt; some v) l</c>.
    /// </summary>
    private Expr Coalesce(CoalesceExpr c, Expr l, Expr r)
    {
        var type = _types.Cic(c.Type);
        if (c.Type is NullableType nullable)
        {
            var value = _types.Cic(nullable.Value);
            var v = _lctx.MkLocalDecl(_ngen, Name.From("v"), value);
            return Nullables.Match(value, type, r, _lctx.MkLambda([v], Nullables.Some(value, v)), l);
        }
        return Expr.App(Init.NullableCoalesce, type, l, r);
    }

    /// <summary><c>Math.Min</c> or <c>Math.Max</c> on <c>int</c> or <c>long</c>, which cannot raise (KTD23); <c>Math.Abs</c> raises.</summary>
    private static Expr Modelled(ModelledCallExpr m, IReadOnlyList<Expr> args) => m.Member switch
    {
        "M:System.Math.Min(System.Int32,System.Int32)" => Expr.App(Init.Int32Min, [.. args]),
        "M:System.Math.Max(System.Int32,System.Int32)" => Expr.App(Init.Int32Max, [.. args]),
        "M:System.Math.Min(System.Int64,System.Int64)" => Expr.App(Init.Int64Min, [.. args]),
        "M:System.Math.Max(System.Int64,System.Int64)" => Expr.App(Init.Int64Max, [.. args]),
        _ => throw new TranslationException(null, $"the modelled member {m.Member} is not translated{(m.Type == VirType.Decimal ? " until M6 U21" : "")}."),
    };

    // ---- Conditions ----

    /// <summary>A <c>bool</c> expression as a condition (docs/m4/05): a proposition and its fixed <c>Decidable</c> instance.</summary>
    private Condition Cond(VirExpr e, Env env) => e switch
    {
        CompareExpr c => Compare(c, env),
        LogicalExpr { Op: LogicalOp.And or LogicalOp.AndEager } l => Conditions.And(Cond(l.L, env), Cond(l.R, env)),
        LogicalExpr { Op: LogicalOp.Or or LogicalOp.OrEager } l => Conditions.Or(Cond(l.L, env), Cond(l.R, env)),
        NotExpr n => Conditions.Not(Cond(n.Operand, env)),
        ImpliesExpr i => Conditions.Implies(Cond(i.A, env), Cond(i.B, env)),
        ForAllExpr f => ForAll(f, env),
        ExistsExpr x => Exists(x, env),
        _ => Conditions.IsTrue(Value(e, env)),
    };

    /// <summary><c>Spec.ForAll&lt;T&gt;(x =&gt; p)</c>: <c>∀ (x : T), P</c>, with no instance (M5a KTD17).</summary>
    private Condition ForAll(ForAllExpr f, Env env)
    {
        var x = _lctx.MkLocalDecl(_ngen, Name.From(f.Name), _types.Cic(f.Domain));
        return new Condition(_lctx.MkPi([x], Cond(f.Body, env.Set(f.Local, x)).Prop), null);
    }

    /// <summary><c>Spec.Exists&lt;T&gt;(x =&gt; p)</c>: <c>@Exists T (fun (x : T) =&gt; P)</c>, with no instance (M5a KTD17).</summary>
    private Condition Exists(ExistsExpr e, Env env)
    {
        var x = _lctx.MkLocalDecl(_ngen, Name.From(e.Name), _types.Cic(e.Domain));
        var body = _lctx.MkLambda([x], Cond(e.Body, env.Set(e.Local, x)).Prop);
        return new Condition(Expr.App(Init.Exists, _types.Cic(e.Domain), body), null);
    }

    /// <summary>
    /// A comparison as a condition. Integers and open enums (at the underlying type) use the order and equality rows; records
    /// compare with <c>R.$eq r s = true</c>, closed types with <c>Nat.beq (T.$index r) (T.$index s) = true</c> (KTD10).
    /// </summary>
    private Condition Compare(CompareExpr c, Env env) => Compare(c, Value(c.L, env), Value(c.R, env));

    /// <summary>A comparison of the operands' values <paramref name="a"/> and <paramref name="b"/>, as above.</summary>
    private Condition Compare(CompareExpr c, Expr a, Expr b)
    {
        Condition eq;
        switch (c.Kind)
        {
            case CompareKind.Int or CompareKind.Enum:
                {
                    var t = _types.Underlying(c.L.Type);
                    switch (c.Op)
                    {
                        case CompareOp.Lt: return Conditions.Lt(t, a, b);
                        case CompareOp.Le: return Conditions.Le(t, a, b);
                        case CompareOp.Gt: return _quantified ? Conditions.Gt(t, a, b) : Conditions.Lt(t, b, a);
                        case CompareOp.Ge: return _quantified ? Conditions.Ge(t, a, b) : Conditions.Le(t, b, a);
                    }
                    eq = Conditions.Eq(t, a, b);
                    break;
                }
            case CompareKind.Bool:
                eq = Conditions.Eq(VirPrimitive.Bool, a, b);
                break;
            case CompareKind.Record:
                eq = Conditions.IsTrue(Expr.App(Expr.Const(LeanNames.Equality(Key(c.L.Type))), a, b));
                break;
            case CompareKind.Closed:
                {
                    var index = Expr.Const(LeanNames.Index(Key(c.L.Type)));
                    eq = Conditions.IsTrue(Operators.NatBeq(Expr.App(index, a), Expr.App(index, b)));
                    break;
                }
            case CompareKind.Decimal:
                throw new TranslationException(null, "a decimal comparison is not translated until M6 U21.");
            default:
                throw new TranslationException(null, $"unsupported comparison kind {c.Kind}.");
        }
        return c.Op switch
        {
            CompareOp.Eq => eq,
            CompareOp.Ne => Conditions.Not(eq),
            _ => throw new TranslationException(null, $"{c.Op} is not defined on {c.Kind} values."),
        };
    }

    // ---- Helpers ----

    /// <summary>Checks that arithmetic wraps; checked arithmetic that can overflow needs exceptions (M6).</summary>
    private static void RequireWrap(VirOverflow overflow)
    {
        if (overflow != VirOverflow.Wrap)
        {
            throw new TranslationException(null, "checked arithmetic needs exceptions.");
        }
    }

    private static string Key(VirType type) =>
        type is RefType r ? r.Key : throw new TranslationException(null, $"{type} is not a record, enum or closed type.");

    private void CollectLocals(VirNode node)
    {
        if (node is DeclStmt d && !_locals.TryAdd(d.Local, d))
        {
            throw new TranslationException(null, $"the local {d.Local} is declared twice.");
        }
        foreach (var child in VirTree.Children(node))
        {
            CollectLocals(child);
        }
    }

    /// <summary>What each C# local currently holds: a free variable bound by a parameter, a <c>let</c> or a join point.</summary>
    private sealed class Env
    {
        public static readonly Env Empty = new(ImmutableDictionary<int, Expr>.Empty);

        private readonly ImmutableDictionary<int, Expr> _values;

        private Env(ImmutableDictionary<int, Expr> values) => _values = values;

        public Expr Get(int local) =>
            _values.TryGetValue(local, out var v) ? v : throw new TranslationException(null, $"the local {local} is read before it is assigned.");

        public Env Set(int local, Expr value) => new(_values.SetItem(local, value));
    }
}
