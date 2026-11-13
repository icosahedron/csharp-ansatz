using System.Collections.Immutable;
using Warrant.Cic;
using Warrant.Kernel;
using Warrant.Vir;

namespace Warrant.Semantics;

/// <summary>
/// Which units being translated can raise, and which state a precondition (plan M6 KTD11), from the one effect inference
/// extraction and the analyzer also use (<see cref="Effects"/>).
/// </summary>
/// <param name="Analysis">The effect analysis of the units being translated.</param>
/// <param name="Requires">The keys of the functions whose body has a <c>Spec.Requires</c>.</param>
/// <param name="Units">The units being translated, by key: a <c>Spec</c> expression states a callee's precondition (KTD26).</param>
internal sealed record CalleeEffects(EffectAnalysis Analysis, IReadOnlySet<string> Requires, IReadOnlyDictionary<string, VirUnit> Units);

/// <summary>
/// The terms of the effect monad <c>Warrant.ClrM σ α := ExceptT ClrExn (StateM σ) α</c> (plan M6 KTD4), in the shapes Lean
/// 4.35.0 elaborates <c>pure</c>, <c>&gt;&gt;=</c> and <c>throw</c> to in <c>lean/Warrant/Checked.lean</c>.
/// </summary>
internal static class Monadic
{
    /// <summary><c>ClrM σ α</c>.</summary>
    public static Expr Type(Expr sigma, Expr alpha) => Expr.App(Init.ClrM, sigma, alpha);

    /// <summary>The value type <c>α</c> of a monadic type <c>ClrM σ α</c>.</summary>
    public static Expr ValueType(Expr monadic) =>
        monadic is AppExpr { Fn: AppExpr { Fn: var head } } app && head == Init.ClrM
            ? app.Arg
            : throw new InvalidOperationException($"{monadic} is not a ClrM type");

    /// <summary>
    /// <c>ClrM σ</c>'s <c>Monad</c> instance as instance resolution finds it:
    /// <c>@ExceptT.instMonad ClrExn (StateM σ) (@StateT.instMonad σ Id Id.instMonad)</c>.
    /// </summary>
    public static Expr Instance(Expr sigma) =>
        Expr.App(Init.ExceptTMonad, Init.ClrExn, Expr.App(Init.StateM, sigma), Expr.App(Init.StateTMonad, sigma, Init.Id, Init.IdMonad));

    /// <summary><c>@Pure.pure (ClrM σ) (Applicative.toPure (Monad.toApplicative inst)) α a</c>.</summary>
    public static Expr Pure(Expr sigma, Expr alpha, Expr a)
    {
        var m = Expr.App(Init.ClrM, sigma);
        var applicative = Expr.App(Init.MonadToApplicative, m, Instance(sigma));
        return Expr.App(Init.PurePure, m, Expr.App(Init.ApplicativeToPure, m, applicative), alpha, a);
    }

    /// <summary><c>@Bind.bind (ClrM σ) (Monad.toBind inst) α β x f</c>, which is <c>x &gt;&gt;= f</c>.</summary>
    public static Expr Bind(Expr sigma, Expr alpha, Expr beta, Expr x, Expr f)
    {
        var m = Expr.App(Init.ClrM, sigma);
        return Expr.App(Init.BindBind, m, Expr.App(Init.MonadToBind, m, Instance(sigma)), alpha, beta, x, f);
    }

    /// <summary><c>@Warrant.ClrM.throw σ α e</c>.</summary>
    public static Expr Throw(Expr sigma, Expr alpha, Expr exception) => Expr.App(Init.ClrMThrow, sigma, alpha, exception);

    /// <summary><c>ClrExn.thrown "key"</c>: an explicit <c>throw</c> of the exception type with that key (KTD4).</summary>
    public static Expr Thrown(string key) => Expr.App(Init.ClrExnThrown, Expr.StrLit(key));

    /// <summary>
    /// The model of a binary operation that raises (KTD6, U3): checked <c>+</c>, <c>-</c> and <c>*</c>, and <c>/</c> and
    /// <c>%</c>, as <c>Warrant.Int32.addChecked σ a b</c> and likewise; and <c>+</c> and <c>-</c> on <c>decimal</c>, which
    /// raise in any context (KTD7, KTD11), as <c>Warrant.Decimal.add σ a b</c> and <c>Warrant.Decimal.sub σ a b</c>.
    /// </summary>
    public static Expr Binary(BinaryOp op, VirPrimitive type, Expr sigma, Expr a, Expr b)
    {
        if (type == VirPrimitive.Decimal)
        {
            return op switch
            {
                BinaryOp.Add => Expr.App(Init.DecimalAdd, sigma, a, b),
                BinaryOp.Sub => Expr.App(Init.DecimalSub, sigma, a, b),
                _ => throw new TranslationException(null, $"{op} is not defined on decimal."),
            };
        }
        bool is32 = type switch
        {
            VirPrimitive.Int32 => true,
            VirPrimitive.Int64 => false,
            _ => throw new TranslationException(null, $"{op} is not defined on {type}."),
        };
        var model = op switch
        {
            BinaryOp.Add => is32 ? Init.Int32AddChecked : Init.Int64AddChecked,
            BinaryOp.Sub => is32 ? Init.Int32SubChecked : Init.Int64SubChecked,
            BinaryOp.Mul => is32 ? Init.Int32MulChecked : Init.Int64MulChecked,
            BinaryOp.Div => is32 ? Init.Int32Div : Init.Int64Div,
            BinaryOp.Rem => is32 ? Init.Int32Rem : Init.Int64Rem,
            _ => throw new ArgumentOutOfRangeException(nameof(op)),
        };
        return Expr.App(model, sigma, a, b);
    }

    /// <summary>
    /// The model of default-context <c>+</c>, <c>-</c> or <c>*</c> on <c>int</c> or <c>long</c> in a method that can raise
    /// (#244): <c>Warrant.Int32.addImplicit σ a b</c> and likewise, which is the wrapped value where the exact one is in
    /// range and fails as a <c>Spec.Assert</c> does (<c>assertFailed</c>) where the CLR would wrap.
    /// </summary>
    public static Expr Implicit(BinaryOp op, VirPrimitive type, Expr sigma, Expr a, Expr b)
    {
        bool is32 = type == VirPrimitive.Int32;
        var model = op switch
        {
            BinaryOp.Add => is32 ? Init.Int32AddImplicit : Init.Int64AddImplicit,
            BinaryOp.Sub => is32 ? Init.Int32SubImplicit : Init.Int64SubImplicit,
            BinaryOp.Mul => is32 ? Init.Int32MulImplicit : Init.Int64MulImplicit,
            _ => throw new ArgumentOutOfRangeException(nameof(op)),
        };
        return Expr.App(model, sigma, a, b);
    }

    /// <summary>The model of default-context unary <c>-</c> on <c>int</c> or <c>long</c> in a method that can raise (#244).</summary>
    public static Expr NegImplicit(VirPrimitive type, Expr sigma, Expr a) =>
        Expr.App(type == VirPrimitive.Int32 ? Init.Int32NegImplicit : Init.Int64NegImplicit, sigma, a);
}

/// <summary>Nullable values as <c>Option</c> (plan M6 KTD5, <c>lean/Warrant/Nullable.lean</c>).</summary>
internal static class Nullables
{
    /// <summary><c>Option T</c>.</summary>
    public static Expr Option(Expr type) => Expr.App(Init.Option, type);

    /// <summary>The value type <c>T</c> of a nullable type <c>T?</c>.</summary>
    public static VirType ValueType(VirType type) =>
        type is NullableType n ? n.Value : throw new TranslationException(null, $"{type} is not a nullable type.");

    /// <summary><c>null</c>: <c>@Option.none T</c>.</summary>
    public static Expr None(Expr type) => Expr.App(Init.OptionNone, type);

    /// <summary>A <c>T</c> converted to <c>T?</c>: <c>@Option.some T v</c>.</summary>
    public static Expr Some(Expr type, Expr value) => Expr.App(Init.OptionSome, type, value);

    /// <summary><c>x is null</c> as a value: <c>@Option.isNone T x</c>.</summary>
    public static Expr IsNone(Expr type, Expr value) => Expr.App(Init.OptionIsNone, type, value);

    /// <summary>
    /// <c>match x with | none =&gt; n | some v =&gt; s v</c>, as the recursor <c>@Option.rec T (fun _ =&gt; R) n s x</c>, which the
    /// VC walker cases on (KTD13). Every result type is in <c>Type</c>, so the motive's level is 1.
    /// </summary>
    public static Expr Match(Expr type, Expr result, Expr none, Expr some, Expr major) =>
        Expr.App(Init.OptionRec, type, Expr.Lam(Init.Unused, Option(type), Conditions.Closed(result)), none, some, major);
}

/// <summary>
/// The monadic translation (plan M6 U9, KTD4, KTD11): a unit that can raise is a <c>ClrM</c> program, built with
/// <c>bind</c>, <c>pure</c> and <c>throw</c> around the same statement rules as the pure translation, with its join points
/// and without its shortcuts.
/// <list type="bullet">
/// <item>An expression that cannot raise is its pure value, lifted with <c>pure</c> where a program is needed.</item>
/// <item>Otherwise its operands and arguments are bound left to right, and an operator's own check (KTD6, checked
/// overflow) runs after both operands are bound, so the left operand's exception wins.</item>
/// <item><c>&amp;</c> and <c>|</c> bind both operands; <c>&amp;&amp;</c> and <c>||</c> bind the right operand only when it is
/// evaluated.</item>
/// <item>A call to a unit that can raise is that unit's program, <c>f σ args</c>; a call to a unit with <c>Spec.Requires</c>
/// is <c>pure (f args)</c> bound, so the VC walker sees the call (KTD11, KTD12).</item>
/// <item>A non-variable switch discriminant is <c>let</c>-bound, so the walker can case on it.</item>
/// <item>An external call is its bound operation applied to its arguments, and <c>await</c> binds the awaited call's
/// program (U19, <c>Dependencies.cs</c>).</item>
/// <item><c>Spec.Assert(c)</c> is <c>if c then pure () else throw assertFailed</c> (KTD16), and a nullable value used where
/// a non-nullable one is required is <c>Warrant.Nullable.nonNull</c>, which throws <c>nullReference</c> on null (#163).</item>
/// <item>Default-context <c>+</c>, <c>-</c>, <c>*</c> and unary <c>-</c> on <c>int</c> and <c>long</c> is a site, its model
/// <c>Warrant.Int32.addImplicit</c> and likewise, which fails as a <c>Spec.Assert</c> does where the CLR would wrap, so the
/// VC walker proves it does not overflow with everything it knows there (#244); not in a <c>Spec.Assert</c>'s condition,
/// which the CLR compiles out and whose arithmetic has obligations of its own (#235).</item>
/// </list>
/// Expressions are translated in continuation-passing style: <see cref="Bound"/> hands the expression's value to a
/// continuation exactly once, so no continuation is ever copied.
/// </summary>
internal sealed partial class BodyTranslator
{
    private static readonly Name ValueName = Name.From("v");

    /// <summary>The world <c>σ</c>, while translating a unit that can raise; null otherwise.</summary>
    private Expr? _sigma;

    /// <summary>The variables <see cref="Emit"/> bound with <c>bind</c>, which an assignment can take as the local itself.</summary>
    private readonly HashSet<Expr> _bound = [];

    /// <summary>
    /// Whether each site the VC walker reports at (M6 KTD18: a raising operation, a throw, a <c>Spec.Assert</c>, a call that
    /// the walker sees) is wrapped in metadata naming its VIR node, <see cref="ContractObligation.SiteKey"/>. Such a program is the walker's
    /// view of a unit (<see cref="ContractObligation.Program"/>), never a declaration: metadata changes nothing the
    /// kernel checks, and the definition is translated without it.
    /// </summary>
    public bool TagSites { get; init; }

    /// <summary>
    /// While stating the obligations of the <c>Spec.Assert</c>s' conditions (#235, <see cref="AssertObligations"/>), what
    /// is in scope at the current point of the program, outermost first: values bound by <c>bind</c> and join points'
    /// parameters, and facts known there; null otherwise. A <c>let</c> is unfolded instead.
    /// </summary>
    private List<(Expr Value, bool IsFact)>? _facts;

    /// <summary>The number of the contract's own well-definedness obligations, which the <c>Spec.Assert</c>s' come after.</summary>
    private int _assertFirst;

    /// <summary>
    /// Whether a pure method's body is being translated for the obligations of its implicit arithmetic (#244,
    /// <see cref="OverflowObligations"/>): the whole body is then translated as a <c>Spec</c> expression is, with
    /// <see cref="_facts"/> kept.
    /// </summary>
    private bool _overflowObligations;

    /// <summary>The state the <c>Spec.Assert</c>s' conditions are translated in, while <see cref="_facts"/> is set.</summary>
    private SpecState? _assertSpec;

    /// <summary>The unit whose <c>Spec.Assert</c>s' obligations are being stated, while <see cref="_facts"/> is set.</summary>
    private VirUnit? _assertSpecUnit;

    /// <summary>Whether a <c>Spec.Assert</c>'s condition is being translated, whose arithmetic is not a site (#235, #244).</summary>
    private bool _inAssertCondition;

    /// <summary>
    /// Whether <paramref name="node"/> is default-context arithmetic that is a site of the program (#244): in a method that
    /// can raise, outside a <c>Spec</c> expression and a <c>Spec.Assert</c>'s condition.
    /// </summary>
    private bool IsImplicitSite(VirNode node) => _sigma is not null && _spec is null && !_inAssertCondition && node is VirExpr e && SpecOverflows(e);

    /// <summary>Translates with <paramref name="entries"/> in scope, while <see cref="_facts"/> is kept.</summary>
    private T WithFacts<T>(IEnumerable<(Expr Value, bool IsFact)> entries, Func<T> translate)
    {
        if (_facts is not { } facts)
        {
            return translate();
        }
        int count = facts.Count;
        facts.AddRange(entries);
        try
        {
            return translate();
        }
        finally
        {
            facts.RemoveRange(count, facts.Count - count);
        }
    }

    /// <summary>Translates under <paramref name="guard"/> inside a <c>Spec</c> expression; as is outside one.</summary>
    private T Guarded<T>(Expr guard, Func<T> translate) => _spec is null ? translate() : InGuard(guard, translate);

    /// <summary>
    /// Records, in a <c>Spec.Assert</c>'s condition (#235), that default-context arithmetic does not overflow: the checked
    /// model <paramref name="program"/> at the world does not raise.
    /// </summary>
    private void RecordOverflow(VirExpr e, Func<Expr, Expr> program)
    {
        if (_spec is { } spec && SpecOverflows(e))
        {
            spec.Operation(this, e, e.Type, program);
        }
    }

    /// <summary>The VIR node IDs of the unit being translated, while <see cref="TagSites"/> is set.</summary>
    private Dictionary<VirNode, int>? _nodeIds;

    /// <summary><paramref name="program"/>, wrapped in metadata naming <paramref name="node"/> when <see cref="TagSites"/> is set.</summary>
    private Expr Site(VirNode node, Expr program) =>
        _nodeIds is { } ids && ids.TryGetValue(node, out var id)
            ? Expr.MData(new KVMap([new KVMapEntry(ContractObligation.SiteKey, id.ToString(System.Globalization.CultureInfo.InvariantCulture))]), program)
            : program;

    /// <summary>
    /// What happens to an expression's value: <paramref name="Apply"/> builds the rest of the program from it, a term of
    /// type <paramref name="ResultM"/>, a <c>ClrM</c> type. A value bound with <c>bind</c> is named <paramref name="Name"/>.
    /// </summary>
    private sealed record Next(Expr ResultM, Func<Expr, Expr> Apply, Name? Name = null);

    /// <summary>
    /// A unit that can raise (KTD11): its type <c>∀ {σ : Type} ops params, ClrM σ R</c>, and its value, the body's program
    /// over an opaque world <c>σ</c> (KTD4), which every obligation quantifies over, and the operations of its dependencies
    /// (U19, KTD9). <c>R</c> is a task's result for an <c>async</c> method and <c>Unit</c> for one that returns no value
    /// (KTD22).
    /// </summary>
    public (Expr Type, Expr Value) MonadicFunction(VirUnit unit)
    {
        if (TagSites)
        {
            _nodeIds = new Dictionary<VirNode, int>(ReferenceEqualityComparer.Instance);
            var nodes = VirTree.PreOrder(unit);
            for (int i = 0; i < nodes.Count; i++)
            {
                _nodeIds.TryAdd(nodes[i], i);
            }
        }
        _sigma = _lctx.MkLocalDecl(_ngen, Name.From("σ"), Expr.Type, BinderInfo.Implicit);
        var operations = Operations(unit, _sigma);
        var binders = Binders(unit);
        if (_facts is not null)
        {
            _assertSpecUnit = unit;
            _assertSpec =new SpecState(unit, _lctx.MkLocalDecl(_ngen, Name.From("σ"), Expr.Type), binders, _assertFirst, () => [.. _facts]);
        }
        var returns = Monadic.Type(_sigma, ReturnType(unit));
        Expr body;
        switch (unit.Body)
        {
            case BlockStmt block:
                CollectLocals(block);
                body = Statements(block.Stmts, 0, Env.Empty, End(unit, returns));
                break;
            case VirExpr e when ReturnsNothing(unit) && e.Type != VirType.Unit:
                // `=> F(x)` in a method that returns no value: F's program run for its effects (KTD22).
                CollectLocals(e);
                body = Statements([new EvalStmt(e)], 0, Env.Empty, End(unit, returns));
                break;
            case VirExpr e:
                CollectLocals(e);
                body = Bound(e, Env.Empty, null);
                break;
            default:
                throw new TranslationException(unit.Key, "a function has no body.");
        }
        List<Expr> all = [_sigma, .. operations.Select(o => o.Op), .. binders];
        return (_lctx.MkPi(all, returns), _lctx.MkLambda(all, body));
    }

    /// <summary>Whether an expression or statement cannot raise: no raising construct and no call to a unit that can raise or has <c>Spec.Requires</c>.</summary>
    private bool IsPure(VirNode node) => !Nodes(node).Any(Raises);

    private bool Raises(VirNode node) =>
        Effects.Construct(node) is not null || (node is CallExpr call && (IsRaisingCallee(call.Target) || HasRequires(call.Target))) || IsImplicitSite(node);

    private bool IsRaisingCallee(string key) => _callees is { } c && c.Analysis.IsRaising(key);

    private bool HasRequires(string key) => _callees is { } c && c.Requires.Contains(key);

    private bool IsBound(Expr value) => _bound.Contains(value);

    private Expr M(VirType type) => Monadic.Type(_sigma!, _types.Cic(type));

    /// <summary>The type of the program an expression's translation builds: the continuation's, or the expression's own.</summary>
    private Expr ResultOf(VirExpr e, Next? k) => k?.ResultM ?? M(e.Type);

    /// <summary>The value <paramref name="v"/> of type <paramref name="type"/> handed on: <c>k v</c>, or <c>pure v</c> with no continuation.</summary>
    private Expr Finish(Expr v, VirType type, Next? k) => k is null ? Monadic.Pure(_sigma!, _types.Cic(type), v) : k.Apply(v);

    /// <summary>The program <paramref name="x"/>, whose value has type <paramref name="type"/>, then <paramref name="k"/>: <c>x &gt;&gt;= fun v =&gt; k v</c>, or <c>x</c> itself.</summary>
    private Expr Emit(Expr x, VirType type, Next? k)
    {
        if (k is null)
        {
            return x;
        }
        var alpha = _types.Cic(type);
        var v = _lctx.MkLocalDecl(_ngen, k.Name ?? ValueName, alpha);
        _bound.Add(v);
        var rest = WithFacts([(v, false)], () => k.Apply(v));
        return Monadic.Bind(_sigma!, alpha, Monadic.ValueType(k.ResultM), x, _lctx.MkLambda([v], rest));
    }

    /// <summary>
    /// Translates <paramref name="e"/> and hands its value to <paramref name="k"/>, exactly once; with no continuation, the
    /// result is <paramref name="e"/>'s own program, of type <c>ClrM σ T</c>.
    /// </summary>
    private Expr Bound(VirExpr e, Env env, Next? k)
    {
        if (IsPure(e))
        {
            return Finish(Value(e, env), e.Type, k);
        }
        var result = ResultOf(e, k);
        Next Then(Func<Expr, Expr> apply) => new(result, apply);
        switch (e)
        {
            case UnaryExpr { Op: UnaryOp.Plus } u:
                return Bound(u.Operand, env, k);
            case UnaryExpr { Op: UnaryOp.Neg } u:
                {
                    var prim = _types.Underlying(u.Type);
                    return Bound(u.Operand, env, Then(a =>
                    {
                        if (IsImplicitSite(u))
                        {
                            return Emit(Site(u, Monadic.NegImplicit(prim, _sigma!, a)), u.Type, k);
                        }
                        if (Effects.Construct(u) is null)
                        {
                            RecordOverflow(u, sigma => Expr.App(NegChecked(prim), sigma, a));
                            return Finish(Operators.Neg(prim, a), u.Type, k);
                        }
                        return Emit(Site(u, Expr.App(NegChecked(prim), _sigma!, a)), u.Type, k);
                    }));
                }
            case BinaryExpr b:
                {
                    var prim = _types.Underlying(b.Type);
                    return Bound(b.L, env, Then(l => Bound(b.R, env, Then(r =>
                    {
                        if (IsImplicitSite(b))
                        {
                            return Emit(Site(b, Monadic.Implicit(b.Op, prim, _sigma!, l, r)), b.Type, k);
                        }
                        if (Effects.Construct(b) is null)
                        {
                            RecordOverflow(b, sigma => Monadic.Binary(b.Op, prim, sigma, l, r));
                            return Finish(Operators.Binary(b.Op, prim, l, r), b.Type, k);
                        }
                        return Emit(Site(b, Monadic.Binary(b.Op, prim, _sigma!, l, r)), b.Type, k);
                    }))));
                }
            case LogicalExpr { Op: LogicalOp.And or LogicalOp.Or } l when !IsPure(l.R):
                {
                    // Short-circuit: the right operand runs only when the left one does not decide the result.
                    var boolM = M(VirType.Bool);
                    return CondBound(l.L, env, result, c =>
                    {
                        var right = Guarded(l.Op == LogicalOp.And ? c.Prop : Expr.App(Init.Not, c.Prop), () => Bound(l.R, env, null));
                        var decided = Monadic.Pure(_sigma!, Init.Bool, Literals.Bool(l.Op == LogicalOp.Or));
                        var term = l.Op == LogicalOp.And ? Operators.Ite(boolM, c, right, decided) : Operators.Ite(boolM, c, decided, right);
                        return Emit(term, VirType.Bool, k);
                    });
                }
            case LogicalExpr l:
                return Bound(l.L, env, Then(a => Bound(l.R, env, Then(b => Finish(l.Op switch
                {
                    LogicalOp.And or LogicalOp.AndEager => Operators.And(a, b),
                    LogicalOp.Or or LogicalOp.OrEager => Operators.Or(a, b),
                    _ => Operators.Xor(a, b),
                }, VirType.Bool, k)))));
            case NotExpr n:
                return Bound(n.Operand, env, Then(a => Finish(Operators.Not(a), VirType.Bool, k)));
            case CompareExpr c:
                return Bound(c.L, env, Then(a => Bound(c.R, env, Then(b => Finish(Operators.Decide(Compare(c, a, b)), VirType.Bool, k)))));
            case ConvertExpr c:
                return Bound(c.Operand, env, Then(a => Effects.Construct(c) is null
                    ? Finish(Convert(c, a), c.Type, k)
                    : Emit(Site(c, CheckedNarrowing(_sigma!, c, a)), c.Type, k)));
            case CondExpr c:
                if (IsPure(c.Then) && IsPure(c.Else))
                {
                    return CondBound(c.C, env, result, cond =>
                        Finish(Operators.Ite(
                            _types.Cic(c.Type), cond,
                            Guarded(cond.Prop, () => Value(c.Then, env)),
                            Guarded(Expr.App(Init.Not, cond.Prop), () => Value(c.Else, env))), c.Type, k));
                }
                return CondBound(c.C, env, result, cond =>
                    Emit(Operators.Ite(
                        M(c.Type), cond,
                        Guarded(cond.Prop, () => Bound(c.Then, env, null)),
                        Guarded(Expr.App(Init.Not, cond.Prop), () => Bound(c.Else, env, null))), c.Type, k));
            case ExternalCallExpr x when x.Type is not TaskType:
                return External(x, x.Type, env, result, k);
            case AwaitExpr a:
                return Await(a, env, result, k);
            case CallExpr call:
                RejectCallWithDependencies(call.Target);
                return BoundAll(call.Args, env, result, args =>
                {
                    var f = Expr.Const(LeanNames.ForKey(call.Target));
                    if (IsRaisingCallee(call.Target))
                    {
                        return Emit(Site(call, Expr.App(f, [_sigma!, .. args])), call.Type, k);
                    }
                    var value = Expr.App(f, [.. args]);
                    // A unit with Spec.Requires: the walker proves its precondition where it is called (KTD11, KTD12).
                    return HasRequires(call.Target)
                        ? Emit(Site(call, Monadic.Pure(_sigma!, _types.Cic(call.Type), value)), call.Type, k)
                        : Finish(value, call.Type, k);
                });
            case NewExpr n:
                return BoundAll(n.Args, env, result, args =>
                    Finish(Expr.App(Expr.Const(LeanNames.Constructor(Key(n.Type))), [.. args]), n.Type, k));
            case GetExpr g:
                return Bound(g.Target, env, Then(t => Finish(Get(g, t), g.Type, k)));
            case WithExpr w:
                return Bound(w.Base, env, Then(b => BoundAll([.. w.Updates.Select(u => u.Value)], env, result, updates =>
                    Finish(With(w, b, updates), w.Type, k))));
            case SwitchExpr s:
                return Discriminant(s.Scrutinee, env, result, x => s.Arms.All(a => IsPure(a.Value))
                    ? Finish(Switch(s, x, _types.Cic(s.Type), arm => Value(arm, env)), s.Type, k)
                    : Emit(Switch(s, x, M(s.Type), arm => Bound(arm, env, null)), s.Type, k));
            case IsNullExpr n:
                return Bound(n.Operand, env, Then(a =>
                    Finish(Nullables.IsNone(_types.Cic(Nullables.ValueType(n.Operand.Type)), a), VirType.Bool, k)));
            case UnwrapExpr u:
                return Bound(u.Operand, env, Then(a =>
                    Emit(Site(u, Expr.App(u.Kind == UnwrapKind.Value ? Init.NullableValue : Init.NullableNonNull, _sigma!, _types.Cic(u.Type), a)), u.Type, k)));
            case CoalesceExpr c:
                return Bound(c.L, env, Then(l =>
                {
                    var isNull = Conditions.IsTrue(Nullables.IsNone(_types.Cic(Nullables.ValueType(c.L.Type)), l)).Prop;
                    return IsPure(c.R)
                        ? Finish(Coalesce(c, l, Guarded(isNull, () => Value(c.R, env))), c.Type, k)
                        : Emit(RaisingCoalesce(c, l, Guarded(isNull, () => Bound(c.R, env, null))), c.Type, k);
                }));
            case ModelledCallExpr m:
                return BoundAll(m.Args, env, result, args => Effects.Construct(m) is null
                    ? Finish(Modelled(m, args), m.Type, k)
                    : Emit(Site(m, Expr.App(Abs(m), _sigma!, args[0])), m.Type, k));
            case ThrowExpr t:
                // Control does not reach the continuation, so the throw has the type of the program it ends.
                return Site(t, Monadic.Throw(_sigma!, Monadic.ValueType(result), Monadic.Thrown(t.Exception)));
            default:
                throw new TranslationException(null, $"unsupported expression {e.GetType().Name} in a method that can raise.");
        }
    }

    /// <summary>Binds <paramref name="items"/> left to right and hands their values to <paramref name="k"/>.</summary>
    private Expr BoundAll(IReadOnlyList<VirExpr> items, Env env, Expr result, Func<IReadOnlyList<Expr>, Expr> k)
    {
        Expr From(int i, ImmutableList<Expr> values) =>
            i == items.Count ? k(values) : Bound(items[i], env, new Next(result, v => From(i + 1, values.Add(v))));
        return From(0, []);
    }

    /// <summary>
    /// A <c>bool</c> expression as a condition, its raising parts bound first; <paramref name="k"/> builds the rest of the
    /// program, of type <paramref name="result"/>, from the condition.
    /// </summary>
    private Expr CondBound(VirExpr e, Env env, Expr result, Func<Condition, Expr> k)
    {
        if (IsPure(e))
        {
            return k(Cond(e, env));
        }
        switch (e)
        {
            case CompareExpr c:
                return Bound(c.L, env, new Next(result, a => Bound(c.R, env, new Next(result, b => k(Compare(c, a, b))))));
            case NotExpr n:
                return CondBound(n.Operand, env, result, x => k(Conditions.Not(x)));
            case LogicalExpr { Op: LogicalOp.AndEager or LogicalOp.OrEager } l:
                return CondBound(l.L, env, result, x => CondBound(l.R, env, result, y =>
                    k(l.Op == LogicalOp.AndEager ? Conditions.And(x, y) : Conditions.Or(x, y))));
            case LogicalExpr { Op: LogicalOp.And or LogicalOp.Or } l when IsPure(l.R):
                return CondBound(l.L, env, result, x =>
                    k(l.Op == LogicalOp.And
                        ? Conditions.And(x, Guarded(x.Prop, () => Cond(l.R, env)))
                        : Conditions.Or(x, Guarded(Expr.App(Init.Not, x.Prop), () => Cond(l.R, env)))));
            default:
                return Bound(e, env, new Next(result, v => k(Conditions.IsTrue(v))));
        }
    }

    /// <summary>
    /// A switch's discriminant (M6 U9): bound when it can raise, <c>let</c>-bound when it is not a variable, so the VC walker
    /// can case on it, and used as it is otherwise.
    /// </summary>
    private Expr Discriminant(VirExpr scrutinee, Env env, Expr result, Func<Expr, Expr> k)
    {
        if (!IsPure(scrutinee))
        {
            return Bound(scrutinee, env, new Next(result, k));
        }
        var value = Value(scrutinee, env);
        if (scrutinee is ParamExpr or LocalExpr or SelfExpr)
        {
            return k(value);
        }
        var x = _lctx.MkLetDecl(_ngen, Name.From("x"), _types.Cic(scrutinee.Type), value);
        return _lctx.MkLambda([x], k(x));
    }

    /// <summary>
    /// <c>Spec.Assert(c)</c> (KTD16): <c>(if c then pure () else throw assertFailed) &gt;&gt;= fun _ =&gt; k</c>. Its script is
    /// the VC walker's (U11), not translation's. While the <c>Spec.Assert</c>s' obligations are stated (#235), its condition
    /// is translated as a <c>Spec</c> expression, which records them, and the rest of the program knows <c>c</c>.
    /// </summary>
    private Expr Assert(AssertStmt a, Env env, Continuation k)
    {
        var outer = _spec;
        _spec = _assertSpec;
        _inAssertCondition = true;
        try
        {
            return CondBound(a.Condition, env, k.ResultType, c =>
            {
                var inner = _spec;
                _spec = outer;
                _inAssertCondition = false;
                try
                {
                    var sigma = _sigma!;
                    var check = Site(a, Operators.Ite(Monadic.Type(sigma, Init.Unit), c,
                        Monadic.Pure(sigma, Init.Unit, Init.UnitUnit),
                        Monadic.Throw(sigma, Init.Unit, Init.ClrExnAssertFailed)));
                    var unit = _lctx.MkLocalDecl(_ngen, Name.From("_"), Init.Unit);
                    var rest = WithFacts([(c.Prop, true)], () => k.Invoke(env));
                    return Monadic.Bind(sigma, Init.Unit, Monadic.ValueType(k.ResultType), check, _lctx.MkLambda([unit], rest));
                }
                finally
                {
                    _spec = inner;
                    _inAssertCondition = true;
                }
            });
        }
        finally
        {
            _spec = outer;
            _inAssertCondition = false;
        }
    }

    /// <summary>
    /// <c>l ?? r</c> when <c>r</c> can raise, as in <c>x ?? throw …</c>: <c>match l with | none =&gt; r | some v =&gt; pure v</c>,
    /// with <c>some v</c> when the result is nullable, so <c>r</c> runs only when <c>l</c> is null.
    /// </summary>
    private Expr RaisingCoalesce(CoalesceExpr c, Expr l, Expr r)
    {
        var value = _types.Cic(Nullables.ValueType(c.L.Type));
        var v = _lctx.MkLocalDecl(_ngen, ValueName, value);
        var result = c.Type is NullableType ? Nullables.Some(value, v) : v;
        var some = _lctx.MkLambda([v], Monadic.Pure(_sigma!, _types.Cic(c.Type), result));
        return Nullables.Match(value, M(c.Type), r, some, l);
    }

    /// <summary>A checked narrowing (KTD6) at the world <paramref name="sigma"/>: <c>Warrant.Int64.toInt32Checked σ a</c>.</summary>
    private Expr CheckedNarrowing(Expr sigma, ConvertExpr c, Expr a) =>
        _types.Underlying(c.From) == VirPrimitive.Int64 && _types.Underlying(c.To) == VirPrimitive.Int32
            ? Expr.App(Init.Int64ToInt32Checked, sigma, a)
            : throw new TranslationException(null, $"there is no checked conversion from {c.From} to {c.To}.");

    private static Expr NegChecked(VirPrimitive type) => type switch
    {
        VirPrimitive.Int32 => Init.Int32NegChecked,
        VirPrimitive.Int64 => Init.Int64NegChecked,
        _ => throw new TranslationException(null, $"checked - is not defined on {type}."),
    };

    /// <summary><c>Math.Abs</c> on <c>int</c> or <c>long</c>, which raises for <c>MinValue</c> (KTD23).</summary>
    private static Expr Abs(ModelledCallExpr m) => m.Member switch
    {
        "M:System.Math.Abs(System.Int32)" => Init.Int32Abs,
        "M:System.Math.Abs(System.Int64)" => Init.Int64Abs,
        _ => throw new TranslationException(null, $"the modelled member {m.Member} is not translated."),
    };
}
