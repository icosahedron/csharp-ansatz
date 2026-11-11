using System.Collections.Immutable;
using Warrant.Cic;
using Warrant.Kernel;
using Warrant.Vir;

namespace Warrant.Semantics;

/// <summary>What a <see cref="SpecObligation"/> states.</summary>
public enum SpecObligationKind
{
    /// <summary>
    /// A partial operation in a <c>Spec</c> expression does not raise (M6 KTD26):
    /// <c>∀ σ params [r], guards → ⦃⌜True⌝⦄ op σ args ⦃⇓_ =&gt; ⌜True⌝, allowed⦄</c>, where <c>op</c> is the operation's
    /// raising model, as the monadic translation emits it.
    /// </summary>
    WellDefinedOperation,

    /// <summary>
    /// A call in a <c>Spec</c> expression to a pure method with <c>Spec.Requires</c> is within that precondition (M6
    /// KTD26): <c>∀ params [r], guards → Requires_callee args</c>.
    /// </summary>
    CalleePrecondition,

    /// <summary>
    /// The refutation of a method's first <c>k</c> <c>Spec.Requires</c> (M6 KTD25): <c>∀ params, R₁ → … → Rₖ → False</c>.
    /// Proving it shows the contract unsatisfiable, which fails the method.
    /// </summary>
    Vacuity,
}

/// <summary>
/// An obligation a method's <c>Spec</c> expressions add to its contract (M6 KTD25, KTD26), stated by trusted translation
/// and proved, or for <see cref="SpecObligationKind.Vacuity"/> refuted, by the engine.
/// </summary>
public sealed class SpecObligation
{
    internal SpecObligation(int index, SpecObligationKind kind, TheoremShell theorem, VirNode node, int binders)
    {
        Index = index;
        Kind = kind;
        Theorem = theorem;
        Node = node;
        Binders = binders;
    }

    /// <summary>The obligation's number among the method's obligations of its kind, from 1, in source order.</summary>
    public int Index { get; }

    /// <summary>What it states.</summary>
    public SpecObligationKind Kind { get; }

    /// <summary>The theorem: <c>f.$wd_k</c>, or for a vacuity check <c>f.$vacuous_k</c>.</summary>
    public TheoremShell Theorem { get; }

    /// <summary>
    /// The node it is reported at (M6 KTD18): the partial operation, the call, or the <c>Spec.Requires</c> statement.
    /// </summary>
    public VirNode Node { get; }

    /// <summary>
    /// The number of binders in front of its claim: the world for a <see cref="SpecObligationKind.WellDefinedOperation"/>,
    /// <c>self</c> and the parameters, the result in a <c>Spec.Ensures</c>, then one hypothesis per guard (or per
    /// <c>Spec.Requires</c> of a vacuity check). A proof introduces them all.
    /// </summary>
    public int Binders { get; }
}

/// <summary>
/// A verified method's contract obligation (M6 KTD12), stated by trusted translation, the claim the engine proves:
/// <code>
/// f.$contract : ∀ (σ : Type) ops params, hyps → ⦃⌜Requires⌝⦄ program ⦃post⟨fun r =&gt; ⌜Ensures r⌝, fun e =&gt; ⌜ClrExn.Allowed e⌝⟩⦄
/// </code>
/// where <c>ops</c> and <c>hyps</c> are the operations of the method's dependencies and their contracts (M6 U19, design
/// D9, <c>Dependencies.cs</c>), none for a method without, <c>program</c> is <c>@f σ ops params</c> for a method that can
/// raise and <c>pure (f params)</c> for a pure one, a
/// missing <c>Requires</c> or <c>Ensures</c> is <c>True</c>, and the exception postcondition allows only an explicit throw
/// and an exception propagated from a dependency; with <c>Spec.NoThrow</c> (#182), a method that can raise has
/// <c>ClrExn.External</c> in place of <c>ClrExn.Allowed</c>, which allows only the latter. With it come the well-definedness obligations of its <c>Spec</c>
/// expressions (KTD26), the vacuity checks of its <c>Spec.Requires</c> (KTD25), and for a pure method with
/// <c>Spec.Ensures</c>, its contract as a proposition, <c>f.$contract_spec</c>, which call sites use.
/// </summary>
public sealed class ContractObligation
{
    internal ContractObligation(
        TheoremShell theorem,
        int binders,
        ImmutableArray<Name> binderNames,
        int operations,
        VirList<TacticNode>? script,
        TheoremShell? spec,
        int specBinders,
        ImmutableArray<SpecObligation> wellDefinedness,
        ImmutableArray<SpecObligation> vacuity,
        bool raising)
    {
        Theorem = theorem;
        Binders = binders;
        BinderNames = binderNames;
        Operations = operations;
        Script = script;
        Spec = spec;
        SpecBinders = specBinders;
        WellDefinedness = wellDefinedness;
        Vacuity = vacuity;
        Raising = raising;
    }

    /// <summary>The obligation, <c>f.$contract</c>.</summary>
    public TheoremShell Theorem { get; }

    /// <summary>
    /// The number of binders in front of the triple: the world, one operation per dependency member the method calls (M6
    /// U19, KTD9), <c>self</c> for an instance member, the parameters, then one contract hypothesis per operation.
    /// </summary>
    public int Binders { get; }

    /// <summary>The names of the <see cref="Binders"/> binders, in order, as goals show them once introduced.</summary>
    public ImmutableArray<Name> BinderNames { get; }

    /// <summary>
    /// The number of operations, the binders after the world, and so of contract hypotheses, the last binders (M6 U19,
    /// KTD9): zero for a method without dependencies.
    /// </summary>
    public int Operations { get; }

    /// <summary>
    /// The script of the method's <c>[ProofFor]</c> method, which replaces the default procedure and starts at the triple
    /// (M6 KTD16); null when it has none.
    /// </summary>
    public VirList<TacticNode>? Script { get; }

    /// <summary>
    /// For a pure method with <c>Spec.Ensures</c>, <c>f.$contract_spec : ∀ params, Requires → Ensures (f params)</c>, with
    /// no hypothesis when it has no <c>Spec.Requires</c>; null otherwise. It follows from <see cref="Theorem"/> at the world
    /// <c>Unit</c>.
    /// </summary>
    public TheoremShell? Spec { get; }

    /// <summary>The number of binders in front of <see cref="Spec"/>'s conclusion: the parameters, then the precondition if any.</summary>
    public int SpecBinders { get; }

    /// <summary>The well-definedness obligations of the <c>Spec</c> expressions (KTD26), in source order.</summary>
    public ImmutableArray<SpecObligation> WellDefinedness { get; }

    /// <summary>One vacuity check per <c>Spec.Requires</c> (KTD25), in source order.</summary>
    public ImmutableArray<SpecObligation> Vacuity { get; }

    /// <summary>Whether the method can raise, so the program is <c>@f σ params</c> rather than <c>pure (f params)</c>.</summary>
    public bool Raising { get; }

    /// <summary>
    /// For a method that can raise, its definition's value with each site the VC walker reports at wrapped in metadata
    /// naming its VIR node (M6 KTD18, <see cref="SiteKey"/>): the same term as the definition once the
    /// metadata is erased, which the walker checks before it uses it. Null for a pure method.
    /// </summary>
    public Expr? Program { get; internal set; }

    /// <summary>The metadata key under which <see cref="Program"/> names a site's VIR node ID (pre-order, docs/m4/04).</summary>
    public const string SiteKey = "warrant.node";
}

/// <summary>
/// <c>Std.Do</c> triples over <c>ClrM σ</c> (M6 KTD12, <c>lean/Warrant/Effect.lean</c>), in the shapes Lean 4.35.0
/// elaborates <c>⦃⌜P⌝⦄ x ⦃⇓r =&gt; ⌜Q r⌝; allowed⦄</c> to: the post-shape <c>.except ClrExn (.arg σ .pure)</c>, the
/// <c>WP</c> instance instance resolution finds for <c>ClrM σ</c>, and one-state assertions as <c>SPred.pure</c> at
/// <c>PostShape.args</c> of the shape.
/// </summary>
internal static class Triples
{
    /// <summary><c>.arg σ .pure</c>, the world's layer.</summary>
    public static Expr ArgShape(Expr sigma) => Expr.App(Init.PostShapeArg, sigma, Init.PostShapePure);

    /// <summary><c>.except ClrExn (.arg σ .pure)</c>, the post-shape of <c>ClrM σ</c>.</summary>
    public static Expr Shape(Expr sigma) => Expr.App(Init.PostShapeExcept, Init.ClrExn, ArgShape(sigma));

    /// <summary><c>@ExceptT.instWP (StateM σ) (.arg σ .pure) ClrExn (@State.instWP σ)</c>: <c>WP (ClrM σ) (Shape σ)</c>.</summary>
    public static Expr Wp(Expr sigma) =>
        Expr.App(Init.ExceptTInstWP, Expr.App(Init.StateM, sigma), ArgShape(sigma), Init.ClrExn, Expr.App(Init.StateInstWP, sigma));

    /// <summary><c>⌜p⌝ : Assertion (Shape σ)</c>: <c>@SPred.pure (PostShape.args (Shape σ)) p</c>.</summary>
    public static Expr Pure(Expr sigma, Expr p) => Expr.App(Init.SPredPure, Expr.App(Init.PostShapeArgs, Shape(sigma)), p);

    /// <summary><c>⌜p⌝</c> at the world's layer, the type of an exception condition's assertion.</summary>
    private static Expr PureArg(Expr sigma, Expr p) => Expr.App(Init.SPredPure, Expr.App(Init.PostShapeArgs, ArgShape(sigma)), p);

    /// <summary>
    /// KTD12's postcondition, <c>(ok, (fun e =&gt; ⌜ClrExn.Allowed e⌝, ()))</c>: <paramref name="ok"/>, a function from the
    /// result to an assertion, on normal return, and for an exception, only an explicit throw or one propagated from a
    /// dependency. With <paramref name="noThrow"/> (<c>Spec.NoThrow</c>, #182) the exception half is
    /// <c>ClrExn.External</c>: only one propagated from a dependency.
    /// </summary>
    public static Expr Post(Expr sigma, Expr alpha, Expr ok, bool noThrow = false)
    {
        var shape = Shape(sigma);
        var arg = ArgShape(sigma);
        var allowed = Expr.Lam(Name.From("e"), Init.ClrExn, PureArg(sigma, Expr.App(noThrow ? Init.ClrExnIsExternal : Init.ClrExnAllowed, Expr.BVar(0))));
        var exceptions = Expr.App(Init.ProdMk,
            Expr.Forall(Name.From("e"), Init.ClrExn, Expr.App(Init.Assertion, arg)),
            Expr.App(Init.ExceptConds, arg),
            allowed,
            Init.PUnitUnit);
        return Expr.App(Init.ProdMk,
            Expr.Forall(Name.From("r"), alpha, Expr.App(Init.Assertion, shape)),
            Expr.App(Init.ExceptConds, shape),
            ok,
            exceptions);
    }

    /// <summary><c>⦃pre⦄ x ⦃post⦄</c> for <c>x : ClrM σ α</c>: <c>@Triple (ClrM σ) (Shape σ) (Wp σ) α x pre post</c>.</summary>
    public static Expr Triple(Expr sigma, Expr alpha, Expr x, Expr pre, Expr post) =>
        Expr.App(Init.Triple, Expr.App(Init.ClrM, sigma), Shape(sigma), Wp(sigma), alpha, x, pre, post);

    /// <summary>The conjunction of <paramref name="props"/>, right-nested; <c>True</c> when there are none.</summary>
    public static Expr Conjunction(IReadOnlyList<Expr> props)
    {
        if (props.Count == 0)
        {
            return Init.PropTrue;
        }
        var result = props[^1];
        for (int i = props.Count - 2; i >= 0; i--)
        {
            result = Expr.App(Init.And, props[i], result);
        }
        return result;
    }
}

/// <summary>
/// Contract obligations (M6 U10, KTD12, KTD25, KTD26). <c>Spec</c> expressions translate as pure propositions: a partial
/// operation in one is the total Lean operation, which agrees with C# wherever the operation does not raise, and adds a
/// well-definedness obligation that it does not raise, under the guards of its enclosing <c>&amp;&amp;</c>,
/// <c>||</c>, <c>?:</c>, <c>??</c> and <c>Spec.Implies</c>; a call to a pure method with <c>Spec.Requires</c> adds that
/// precondition at its arguments. Each <c>Spec.Requires</c> is under the ones before it, and each <c>Spec.Ensures</c> under
/// every <c>Spec.Requires</c> and the <c>Spec.Ensures</c> before it.
/// </summary>
internal sealed partial class BodyTranslator
{
    /// <summary>
    /// Whether the unit's contract obligation is stated beside its body, so the body may pass over its <c>Spec.Requires</c>
    /// and <c>Spec.Ensures</c>, which are claims, not steps; a body translated without it would drop them unread.
    /// </summary>
    public bool Contracted { get; init; }

    /// <summary>The state of a <c>Spec</c> expression's translation; null outside one.</summary>
    private SpecState? _spec;

    /// <summary>The methods whose <c>Spec.Requires</c> is being stated, outermost first, so a precondition that calls its own method is caught.</summary>
    private ImmutableHashSet<string> _specCallers = ImmutableHashSet.Create<string>(StringComparer.Ordinal);

    private static readonly Name GuardName = Name.From("h");

    /// <summary>
    /// The contract obligation of a function unit (KTD12), or null when it needs none: a pure method with neither
    /// <c>Spec.Requires</c> nor <c>Spec.Ensures</c>.
    /// </summary>
    /// <param name="unit">The function unit.</param>
    /// <param name="function">The unit's constant.</param>
    /// <param name="raising">Whether the unit can raise (KTD11), so its constant is a <c>ClrM</c> program.</param>
    public ContractObligation? Contract(VirUnit unit, Name function, bool raising)
    {
        var stmts = unit.Body is BlockStmt block ? block.Stmts : VirList<VirStmt>.Empty;
        var requires = stmts.OfType<RequiresStmt>().ToList();
        var ensures = stmts.OfType<EnsuresStmt>().ToList();
        // Spec.NoThrow (#182) narrows the exception postcondition of a method that can raise; a pure one raises nothing, so
        // it already holds and the obligation is the one without it.
        bool noThrow = raising && stmts.Any(s => s is NoThrowStmt);
        if (!raising && requires.Count == 0 && ensures.Count == 0)
        {
            return null;
        }
        _quantified = true;
        var sigma = _lctx.MkLocalDecl(_ngen, Name.From("σ"), Expr.Type);
        var operations = Operations(unit, sigma);
        var binders = Binders(unit);
        var returns = ReturnType(unit);
        // One contract hypothesis per operation, at every argument and every world (M6 U19, KTD9, design D9).
        var hypotheses = operations.Select(o => _lctx.MkLocalDecl(_ngen, ContractHypothesisName(o), Hypothesis(o, sigma, noThrow))).ToList();
        var spec = _spec = new SpecState(unit, sigma, binders);
        var vacuity = new List<SpecObligation>();

        // Each Spec.Requires under the ones before it, as if joined by &&.
        var pre = new List<Expr>();
        foreach (var req in requires)
        {
            var prop = InGuards(pre, () => Cond(req.Condition, Env.Empty)).Prop;
            pre.Add(prop);
            var hyps = pre.Select(p => _lctx.MkLocalDecl(_ngen, GuardName, p)).ToList();
            var refutation = _lctx.MkPi([.. binders, .. hyps], Init.PropFalse);
            vacuity.Add(new SpecObligation(
                vacuity.Count + 1, SpecObligationKind.Vacuity,
                new TheoremShell(LeanNames.Vacuity(unit.Key, vacuity.Count + 1), new Condition(Closed(refutation), null), null, null),
                req, binders.Count + hyps.Count));
        }

        // Each Spec.Ensures under every Spec.Requires and the Spec.Ensures before it, with the result bound.
        var r = _lctx.MkLocalDecl(_ngen, Name.From(ensures.Select(e => e.Name).FirstOrDefault(n => n is not null) ?? "r"), returns);
        spec.Result = r;
        var post = new List<Expr>();
        foreach (var ens in ensures)
        {
            var env = ens.Local is { } local ? Env.Empty.Set(local, r) : Env.Empty;
            var prop = InGuards([.. pre, .. post], () => Cond(ens.Condition, env)).Prop;
            post.Add(prop);
        }
        spec.Result = null;
        _spec = null;

        var requiresProp = Triples.Conjunction(pre);
        var ensuresProp = Triples.Conjunction(post);
        var call = Expr.App(Expr.Const(function), [.. binders]);
        List<Expr> ops = [.. operations.Select(o => o.Op)];
        var program = raising ? Expr.App(Expr.Const(function), [sigma, .. ops, .. binders]) : Monadic.Pure(sigma, returns, call);
        var triple = Triples.Triple(sigma, returns, program, Triples.Pure(sigma, requiresProp),
            Triples.Post(sigma, returns, _lctx.MkLambda([r], Triples.Pure(sigma, ensuresProp)), noThrow));
        List<Expr> all = [sigma, .. ops, .. binders, .. hypotheses];
        var statement = Closed(_lctx.MkPi(all, triple));
        var theorem = new TheoremShell(LeanNames.Contract(unit.Key), new Condition(statement, null), null, null);

        TheoremShell? specLemma = null;
        int specBinders = 0;
        if (!raising && ensures.Count > 0)
        {
            // Ensures at the result f params, under the Requires conjunction when there is one.
            var conclusion = ExprOps.InstantiateRev(ExprOps.Abstract(ensuresProp, [r]), [call]);
            List<Expr> specFVars = [.. binders];
            if (requires.Count > 0)
            {
                specFVars.Add(_lctx.MkLocalDecl(_ngen, GuardName, requiresProp));
            }
            specBinders = specFVars.Count;
            specLemma = new TheoremShell(LeanNames.ContractSpec(unit.Key), new Condition(Closed(_lctx.MkPi(specFVars, conclusion)), null), null, null);
        }

        return new ContractObligation(
            theorem, all.Count, [.. all.Select(x => _lctx.Get(x).UserName)], operations.Count, unit.Script, specLemma, specBinders,
            [.. spec.WellDefinedness], [.. vacuity], raising);
    }

    /// <summary>A statement must mention no free variable: everything it names is bound in it.</summary>
    private static Expr Closed(Expr statement) =>
        statement.HasFVar ? throw new TranslationException(null, "a contract obligation refers to a value it cannot name.") : statement;

    /// <summary>Translates with <paramref name="guards"/> added to the <c>Spec</c> expression's guards.</summary>
    private T InGuards<T>(IReadOnlyList<Expr> guards, Func<T> translate)
    {
        var spec = _spec!;
        int count = spec.Guards.Count;
        spec.Guards.AddRange(guards);
        try
        {
            return translate();
        }
        finally
        {
            spec.Guards.RemoveRange(count, spec.Guards.Count - count);
        }
    }

    private T InGuard<T>(Expr guard, Func<T> translate) => InGuards([guard], translate);

    /// <summary>
    /// A partial operation in a <c>Spec</c> expression (KTD26): its total Lean value, recording that it does not raise.
    /// </summary>
    private Expr SpecPartial(VirExpr e, Env env, string construct)
    {
        var spec = _spec!;
        switch (e)
        {
            case BinaryExpr b:
                {
                    var prim = _types.Underlying(b.Type);
                    var l = Value(b.L, env);
                    var r = Value(b.R, env);
                    spec.Operation(this, e, b.Type, sigma => Monadic.Binary(b.Op, prim, sigma, l, r));
                    return Operators.Binary(b.Op, prim, l, r);
                }
            case UnaryExpr { Op: UnaryOp.Neg } u:
                {
                    var prim = _types.Underlying(u.Type);
                    var a = Value(u.Operand, env);
                    spec.Operation(this, e, u.Type, sigma => Expr.App(NegChecked(prim), sigma, a));
                    return Operators.Neg(prim, a);
                }
            case ConvertExpr c:
                {
                    var a = Value(c.Operand, env);
                    spec.Operation(this, e, c.Type, sigma => CheckedNarrowing(sigma, c, a));
                    return Operators.Convert(_types.Underlying(c.From), _types.Underlying(c.To), a);
                }
            case UnwrapExpr u:
                {
                    var a = Value(u.Operand, env);
                    var type = _types.Cic(u.Type);
                    spec.Operation(this, e, u.Type, sigma => Expr.App(u.Kind == UnwrapKind.Value ? Init.NullableValue : Init.NullableNonNull, sigma, type, a));
                    // The value when it is there; the default is never read where the obligation holds.
                    return Expr.App(Init.NullableCoalesce, type, a, Default(u.Type));
                }
            case ModelledCallExpr m when m.Args.Count == 1:
                {
                    var prim = _types.Underlying(m.Type);
                    var a = Value(m.Args[0], env);
                    spec.Operation(this, e, m.Type, sigma => Expr.App(Abs(m), sigma, a));
                    var negative = Conditions.Lt(prim, a, Literals.Of(prim, 0));
                    return Operators.Ite(Literals.Type(prim), negative, Operators.Neg(prim, a), a);
                }
            default:
                throw new TranslationException(null, $"the {construct} cannot appear in a Spec expression, which is a proposition (M6 KTD26).");
        }
    }

    /// <summary>
    /// Whether <paramref name="e"/> is <c>+</c>, <c>-</c> or <c>*</c> on <c>int</c> or <c>long</c>, or unary <c>-</c> on
    /// one, which a <c>Spec</c> expression treats as partial even where C# would wrap (#183): its value is the wrapped one,
    /// and its well-definedness obligation says it does not overflow. An explicit cast is left as written.
    /// </summary>
    private static bool SpecOverflows(VirExpr e) => e switch
    {
        BinaryExpr { Op: BinaryOp.Add or BinaryOp.Sub or BinaryOp.Mul } b => b.Type == VirType.Int32 || b.Type == VirType.Int64,
        UnaryExpr { Op: UnaryOp.Neg } u => u.Type == VirType.Int32 || u.Type == VirType.Int64,
        _ => false,
    };

    /// <summary>
    /// A condition of two operands in a <c>Spec</c> expression, <paramref name="right"/> translated under the guard
    /// <paramref name="guard"/> gives of <paramref name="left"/>'s condition.
    /// </summary>
    private Condition SpecCond(VirExpr left, Env env, Func<Condition, Condition, Condition> combine, Func<Condition, Expr> guard, VirExpr right)
    {
        var x = Cond(left, env);
        return combine(x, InGuard(guard(x), () => Cond(right, env)));
    }

    /// <summary>
    /// The value of an expression in a <c>Spec</c> expression whose parts are evaluated only under a guard (<c>&amp;&amp;</c>,
    /// <c>||</c>, <c>?:</c> and <c>??</c>), or that calls a method (KTD26); null for any other, which translates as it does
    /// in a body.
    /// </summary>
    private Expr? SpecGuarded(VirExpr e, Env env)
    {
        switch (e)
        {
            case LogicalExpr { Op: LogicalOp.And or LogicalOp.Or } l:
                {
                    var a = Value(l.L, env);
                    var isTrue = Conditions.IsTrue(a).Prop;
                    var b = InGuard(l.Op == LogicalOp.And ? isTrue : Expr.App(Init.Not, isTrue), () => Value(l.R, env));
                    return l.Op == LogicalOp.And ? Operators.And(a, b) : Operators.Or(a, b);
                }
            case CondExpr c:
                {
                    var condition = Cond(c.C, env);
                    var then = InGuard(condition.Prop, () => Value(c.Then, env));
                    var @else = InGuard(Expr.App(Init.Not, condition.Prop), () => Value(c.Else, env));
                    return Operators.Ite(_types.Cic(c.Type), condition, then, @else);
                }
            case CoalesceExpr c:
                {
                    var l = Value(c.L, env);
                    var isNull = Conditions.IsTrue(Nullables.IsNone(_types.Cic(Nullables.ValueType(c.L.Type)), l)).Prop;
                    return Coalesce(c, l, InGuard(isNull, () => Value(c.R, env)));
                }
            case CallExpr c when _callees is { } callees && callees.Analysis.IsRaising(c.Target):
                throw new TranslationException(null, $"a Spec expression calls {c.Target}, which can raise: a program cannot sit inside a proposition (M6 KTD26).");
            case CallExpr c when HasRequires(c.Target):
                return SpecCall(c, env);
            default:
                return null;
        }
    }

    /// <summary>
    /// A call in a <c>Spec</c> expression to a pure method with <c>Spec.Requires</c> (KTD26): its value, recording that the
    /// arguments satisfy the precondition.
    /// </summary>
    private Expr SpecCall(CallExpr c, Env env)
    {
        var args = c.Args.Select(a => Value(a, env)).ToList();
        var callee = _callees?.Units.GetValueOrDefault(c.Target) ?? throw new TranslationException(null, $"the precondition of {c.Target} is not being translated.");
        _spec!.CalleePrecondition(this, c, CalleeRequires(callee, args));
        return Expr.App(Expr.Const(LeanNames.ForKey(c.Target)), [.. args]);
    }

    /// <summary>
    /// The conjunction of a callee's <c>Spec.Requires</c> at <paramref name="args"/>, as its own contract states it, by a
    /// translator of its own whose parameters are the arguments, sharing this one's local context and name generator.
    /// The callee's own <c>Spec</c> obligations are its own.
    /// </summary>
    private Expr CalleeRequires(VirUnit callee, IReadOnlyList<Expr> args)
    {
        if (_specCallers.Contains(callee.Key))
        {
            throw new TranslationException(null, $"the Spec.Requires of {callee.Key} calls {callee.Key} again, so its precondition has no meaning.");
        }
        // In this translator's context and with its name generator, so a variable the callee's Requires binds can never
        // share an id with a free variable of the arguments and capture it when abstracted.
        var nested = new BodyTranslator(_types, _callees, _lctx, _ngen) { _quantified = true, _specCallers = _specCallers.Add(callee.Key) };
        int i = 0;
        if (callee.Self is not null)
        {
            nested._self = args[i++];
        }
        for (; i < args.Count; i++)
        {
            nested._params.Add(args[i]);
        }
        nested._spec = new SpecState(callee, null, []);
        var stmts = callee.Body is BlockStmt block ? block.Stmts : VirList<VirStmt>.Empty;
        return Triples.Conjunction([.. stmts.OfType<RequiresStmt>().Select(r => nested.Cond(r.Condition, Env.Empty).Prop)]);
    }

    /// <summary>
    /// A value of a type that a total <c>Spec</c> translation can stand in where C# would raise (KTD26): never read where
    /// the well-definedness obligation holds.
    /// </summary>
    private Expr Default(VirType type)
    {
        switch (type)
        {
            case NullableType n:
                return Nullables.None(_types.Cic(n.Value));
            case PrimitiveType { Kind: VirPrimitive.Bool }:
                return Literals.Bool(false);
            case PrimitiveType { Kind: VirPrimitive.Int32 or VirPrimitive.Int64 } p:
                return Literals.Of(p.Kind, 0);
            case PrimitiveType { Kind: VirPrimitive.Decimal }:
                return Literals.Decimal(new DecimalLitExpr(false, 0, 0));
            case RefType r when _types.IsRecord(type):
                return Expr.App(Expr.Const(LeanNames.Constructor(r.Key)), [.. _types.Record(type).Fields.Select(f => Default(f.Type))]);
            case RefType r when _types.IsClosed(type):
                return _types.Closed(type).Members.Count > 0
                    ? Expr.Const(LeanNames.Member(r.Key, _types.Closed(type).Members[0].Name))
                    : throw new TranslationException(null, $"{r.Key} has no members, so no value of it is read in a Spec expression.");
            case RefType:
                return Literals.Of(_types.Underlying(type), 0);
            default:
                throw new TranslationException(null, $"a {type} value is not read in a Spec expression.");
        }
    }

    /// <summary>The state of a <c>Spec</c> expression's translation: its guards, and the obligations it has recorded.</summary>
    private sealed class SpecState(VirUnit unit, Expr? sigma, IReadOnlyList<Expr> binders)
    {
        /// <summary>The conditions under which the expression being translated is evaluated, outermost first.</summary>
        public List<Expr> Guards { get; } = [];

        /// <summary>The result, while translating a <c>Spec.Ensures</c>; null otherwise.</summary>
        public Expr? Result { get; set; }

        /// <summary>The well-definedness obligations recorded so far, in source order.</summary>
        public List<SpecObligation> WellDefinedness { get; } = [];

        /// <summary>
        /// Records that the partial operation <paramref name="node"/> of type <paramref name="type"/> does not raise: its
        /// model, from <paramref name="program"/> at the world, under the current guards. Nothing is recorded for a
        /// callee's precondition, whose own obligations are its own.
        /// </summary>
        public void Operation(BodyTranslator t, VirNode node, VirType type, Func<Expr, Expr> program)
        {
            if (sigma is null)
            {
                return;
            }
            var alpha = t._types.Cic(type);
            var truth = Triples.Pure(sigma, Init.PropTrue);
            var claim = Triples.Triple(sigma, alpha, program(sigma), truth,
                Triples.Post(sigma, alpha, Expr.Lam(Name.From("r"), alpha, truth)));
            Add(t, SpecObligationKind.WellDefinedOperation, node, [sigma], claim);
        }

        /// <summary>Records that the call <paramref name="node"/> is within its callee's precondition <paramref name="requires"/>.</summary>
        public void CalleePrecondition(BodyTranslator t, VirNode node, Expr requires)
        {
            if (sigma is null)
            {
                return;
            }
            Add(t, SpecObligationKind.CalleePrecondition, node, [], requires);
        }

        private void Add(BodyTranslator t, SpecObligationKind kind, VirNode node, IReadOnlyList<Expr> world, Expr claim)
        {
            var hyps = Guards.Select(g => t._lctx.MkLocalDecl(t._ngen, GuardName, g)).ToList();
            List<Expr> fvars = [.. world, .. binders, .. Result is { } r ? [r] : Array.Empty<Expr>(), .. hyps];
            int index = WellDefinedness.Count + 1;
            var statement = Closed(t._lctx.MkPi(fvars, claim));
            var shell = new TheoremShell(LeanNames.WellDefined(unit.Key, index), new Condition(statement, null), null, null);
            WellDefinedness.Add(new SpecObligation(index, kind, shell, node, fvars.Count));
        }
    }
}
