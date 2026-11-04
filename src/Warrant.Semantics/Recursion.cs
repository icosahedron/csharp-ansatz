using System.Collections.Immutable;
using Warrant.Cic;
using Warrant.Kernel;
using Warrant.Vir;

namespace Warrant.Semantics;

/// <summary>
/// The decrease obligation of one recursive call (M5a KTD15, docs/m5a/03 "Decrease theorems"): the theorem
/// <c>f.$dec_k</c>, whose statement translation builds and whose proof the engine finds.
/// </summary>
public sealed class DecreaseObligation
{
    internal DecreaseObligation(int index, TheoremShell theorem, CallExpr call, VirExpr measure, int binders)
    {
        Index = index;
        Theorem = theorem;
        Call = call;
        Measure = measure;
        Binders = binders;
    }

    /// <summary>The call's number among the method's recursive calls, from 1, in source order.</summary>
    public int Index { get; }

    /// <summary>
    /// The theorem <c>f.$dec_k : ∀ params, (scope at the call) → μ(args) &lt; μ(params)</c>, with
    /// <c>μ(v) = Int.toNat (T.toInt measure[v])</c>.
    /// </summary>
    public TheoremShell Theorem { get; }

    /// <summary>The recursive call, a node of the unit's body.</summary>
    public CallExpr Call { get; }

    /// <summary>The measure, the argument of the body's <c>Spec.Decreases</c>.</summary>
    public VirExpr Measure { get; }

    /// <summary>
    /// The number of binders in front of the statement's conclusion, <c>∀</c> and <c>let</c> alike: the parameters, then
    /// what is in scope at the call. A proof introduces them all, so that the goal shows them as hypotheses.
    /// </summary>
    public int Binders { get; }
}

/// <summary>
/// What a recursive method adds to its definition (M5a KTD14, KTD15): its decrease theorems, admitted before the
/// definition, which refers to them; and its equation lemma, admitted after it.
/// </summary>
public sealed class RecursiveDefinition
{
    internal RecursiveDefinition(ImmutableArray<DecreaseObligation> decreases, TheoremShell equation, Expr equationProof)
    {
        Decreases = decreases;
        Equation = equation;
        EquationProof = equationProof;
    }

    /// <summary>One obligation per recursive call, in source order.</summary>
    public ImmutableArray<DecreaseObligation> Decreases { get; }

    /// <summary>
    /// <c>f.$eq_def : ∀ p, f p = body</c>, whose right side is exactly M4's translation of the body with <c>f</c> as a
    /// constant and <c>ite</c> throughout.
    /// </summary>
    public TheoremShell Equation { get; }

    /// <summary>
    /// The equation lemma's proof, the bare <c>Nat.fix_eq</c> instance <c>fun p => @WellFounded.Nat.fix_eq P M μ F ⟨p⟩</c>;
    /// the kernel checks it against the statement by definitional unfolding (docs/m5a/03, "The equation lemma").
    /// </summary>
    public Expr EquationProof { get; }
}

/// <summary>
/// Well-founded recursion (M5a KTD14, KTD15; docs/m5a/03). A method whose block body starts with
/// <c>Spec.Decreases(e)</c> is the term Lean 4.35.0 builds for <c>termination_by e.toInt.toNat</c>:
/// <code>
/// f := fun p => @WellFounded.Nat.fix P (fun _ => T) (fun x => Int.toNat (T'.toInt e[x])) F ⟨p…⟩
/// F := fun x rec => body[p ↦ x's projections, f a ↦ rec ⟨a…⟩ (f.$dec_k …)]
/// </code>
/// One parameter is not packed (<c>P</c> is its type); several are a right-nested <c>PSigma</c> read by projections. On the
/// way to a recursive call, a branch is a <c>dite</c> whose hypothesis the call's decrease theorem takes.
/// </summary>
internal sealed partial class BodyTranslator
{
    /// <summary>The recursion being translated, while translating a recursive method's functional; null otherwise.</summary>
    private RecursionState? _rec;

    /// <summary>
    /// The free variables in scope at the current point of the body, outermost first: <c>let</c>s, join points and their
    /// parameters, and <c>dite</c> hypotheses. Kept only while translating a recursive method's functional.
    /// </summary>
    private readonly List<Expr> _scope = [];

    /// <summary>The decrease obligations of the recursive calls translated so far.</summary>
    private readonly List<DecreaseObligation> _recDecreases = [];

    private static readonly Name HypothesisName = Name.From("h");

    /// <summary><c>fun (a b : Nat) => @LT.lt Nat instLTNat a b</c>, the relation <c>InvImage</c> pulls back.</summary>
    private static readonly Expr NatLtRelation =
        Expr.Lam(Name.From("a"), Init.Nat, Expr.Lam(Name.From("b"), Init.Nat, NatLt(Expr.BVar(1), Expr.BVar(0))));

    /// <summary>Whether a unit is a recursive method: a function whose block body starts with <c>Spec.Decreases</c>.</summary>
    public static bool IsRecursive(VirUnit unit) =>
        unit.Kind == VirUnitKind.Function && unit.Body is BlockStmt { Stmts.Count: > 0 } block && block.Stmts[0] is DecreasesStmt;

    /// <summary>
    /// A recursive method's type, its <c>Nat.fix</c> value, its decrease obligations and its equation lemma's proof.
    /// </summary>
    /// <param name="unit">The unit, for which <see cref="IsRecursive"/> holds.</param>
    public (Expr Type, Expr Value, ImmutableArray<DecreaseObligation> Decreases, Expr EquationProof) Recursive(VirUnit unit)
    {
        var binders = Binders(unit);
        var returns = ReturnType(unit);
        var block = (BlockStmt)unit.Body!;
        var measure = ((DecreasesStmt)block.Stmts[0]).Measure;
        CollectLocals(block);
        var toInt = _types.Underlying(measure.Type) switch
        {
            VirPrimitive.Int32 => Init.Int32ToInt,
            VirPrimitive.Int64 => Init.Int64ToInt,
            var other => throw new TranslationException(null, $"the measure of Spec.Decreases is {other}, not int or long."),
        };
        var measureTerm = ExprOps.Abstract(Value(measure, Env.Empty), [.. binders]);
        Expr Measure(IReadOnlyList<Expr> values) => Expr.App(Init.IntToNat, Expr.App(toInt, ExprOps.InstantiateRev(measureTerm, [.. values])));

        var types = binders.Select(b => _lctx.Get(b).Type).ToList();
        var domain = PackedType(types, 0);
        var x = binders.Count == 1 ? binders[0] : _lctx.MkLocalDecl(_ngen, Name.From("x"), domain);
        var mu = _lctx.MkLambda([x], Measure(Projections(x, binders.Count)));
        var y = _lctx.MkLocalDecl(_ngen, Name.From("y"), domain);
        var decreasing = Expr.App(Init.InvImage, domain, Init.Nat, NatLtRelation, mu, y, x);
        var rec = _lctx.MkLocalDecl(_ngen, Name.From("rec"), _lctx.MkPi([y], Expr.Forall(Init.Unused, decreasing, Conditions.Closed(returns))));

        _rec = new RecursionState(unit, (FVarExpr)rec, binders, types, Measure, measure);
        var body = Statements(block.Stmts, 0, Env.Empty, new Unreachable(returns));
        _rec = null;
        if (binders.Count > 1)
        {
            body = ExprOps.InstantiateRev(ExprOps.Abstract(body, [.. binders]), [.. Projections(x, binders.Count)]);
        }
        var functional = _lctx.MkLambda([x, rec], body);
        var motive = Expr.Lam(Init.Unused, domain, Conditions.Closed(returns));
        var packed = Pack(binders, types);
        var value = _lctx.MkLambda(binders, Expr.App(Init.NatFix, domain, motive, mu, functional, packed));
        var proof = _lctx.MkLambda(binders, Expr.App(Init.NatFixEq, domain, motive, mu, functional, packed));
        return (_lctx.MkPi(binders, returns), value, [.. _recDecreases.OrderBy(d => d.Index)], proof);
    }

    /// <summary>
    /// A recursive method's equation lemma statement, <c>∀ p, f p = body</c>: the body as M4 translates it, with the
    /// method itself as an ordinary constant (KTD15). Translated by a fresh translator, so it shares nothing with the
    /// functional.
    /// </summary>
    public Condition Equation(VirUnit unit, Name name)
    {
        var binders = Binders(unit);
        var returns = ReturnType(unit);
        var block = (BlockStmt)unit.Body!;
        CollectLocals(block);
        var body = Statements(block.Stmts, 0, Env.Empty, new Unreachable(returns));
        var lhs = Expr.App(Expr.Const(name), [.. binders]);
        return new Condition(_lctx.MkPi(binders, Expr.App(Init.Eq, returns, lhs, body)), null);
    }

    /// <summary>
    /// A call of the method to itself inside its functional: <c>rec ⟨args⟩ (f.$dec_k params scope)</c>, recording the
    /// obligation <c>f.$dec_k</c>. Its binders are the parameters and what is in scope at the call: a <c>let</c> stays a
    /// <c>let</c> unless its value contains a recursive call, which a theorem stated outside the functional cannot name,
    /// so it becomes a plain <c>∀</c> binder; a hypothesis that mentions a recursive result is left out.
    /// </summary>
    private Expr RecursiveCall(CallExpr call, Env env)
    {
        var rec = _rec!;
        var args = call.Args.Select(a => Value(a, env)).ToList();
        if (args.Any(rec.Mentions))
        {
            throw new TranslationException(null, "nested recursion: a recursive call inside another recursive call's argument is not supported.");
        }
        if (args.Count != rec.Binders.Count)
        {
            throw new TranslationException(null, $"a recursive call has {args.Count} arguments, not {rec.Binders.Count}.");
        }
        int index = rec.IndexOf(call);
        if (_recDecreases.Any(d => d.Index == index))
        {
            throw new InvalidOperationException("a recursive call was translated twice");
        }
        var scope = _scope.Where(f => !rec.Mentions(_lctx.Get(f).Type)).ToList();
        List<Expr> binders = [.. rec.Binders, .. scope];
        var goal = NatLt(rec.Measure(args), rec.Measure(rec.Binders));
        var statement = Close(binders, goal, rec);
        if (statement.HasFVar)
        {
            throw new TranslationException(null, "a decrease obligation refers to a value it cannot name.");
        }
        var name = LeanNames.Decrease(rec.Key, index);
        _recDecreases.Add(new DecreaseObligation(index, new TheoremShell(name, new Condition(statement, null), null, null), call, rec.MeasureNode, binders.Count));
        var proof = Expr.App(Expr.Const(name), [.. binders.Where(f => !KeepsValue(f, rec))]);
        return Expr.App(rec.Fvar, Pack(args, rec.Types), proof);
    }

    /// <summary>Whether a binder of a decrease theorem stays a <c>let</c>: a local definition whose value has no recursive call.</summary>
    private bool KeepsValue(Expr fvar, RecursionState rec) => _lctx.Get(fvar).Value is { } value && !rec.Mentions(value);

    /// <summary>
    /// <see cref="LocalContext.MkPi(IReadOnlyList{Expr}, Expr, bool)"/>, except that a local definition whose value
    /// mentions the recursive call is bound by <c>∀</c>, without its value.
    /// </summary>
    private Expr Close(IReadOnlyList<Expr> fvars, Expr body, RecursionState rec)
    {
        var arr = fvars.ToArray();
        var r = ExprOps.Abstract(body, arr);
        for (int i = arr.Length - 1; i >= 0; i--)
        {
            var decl = _lctx.Get(arr[i]);
            var prefix = arr.AsSpan(0, i);
            var type = ExprOps.Abstract(decl.Type, prefix);
            r = KeepsValue(arr[i], rec)
                ? Expr.Let(decl.UserName, type, ExprOps.Abstract(decl.Value!, prefix), r)
                : Expr.Forall(decl.UserName, type, r);
        }
        return r;
    }

    /// <summary>
    /// The hypotheses of a two-way branch on <paramref name="c"/>, <c>h : P</c> and <c>h : ¬P</c>, while translating a
    /// recursive method's functional; nulls otherwise.
    /// </summary>
    private (Expr? Then, Expr? Else) Hypotheses(Condition c) =>
        _rec is null ? (null, null) : (_lctx.MkLocalDecl(_ngen, HypothesisName, c.Prop), _lctx.MkLocalDecl(_ngen, HypothesisName, Expr.App(Init.Not, c.Prop)));

    /// <summary>
    /// The hypotheses of a chain of tests <c>if t₀ … else if t₁ … else …</c>: <c>h : tᵢ</c> and <c>h : ¬tᵢ</c> for each test,
    /// while translating a recursive method's functional; null otherwise.
    /// </summary>
    private (Expr[] Pos, Expr[] Neg)? ChainHypotheses(IReadOnlyList<Condition> tests)
    {
        if (_rec is null)
        {
            return null;
        }
        var pos = new Expr[tests.Count];
        var neg = new Expr[tests.Count];
        for (int i = 0; i < tests.Count; i++)
        {
            var (then, @else) = Hypotheses(tests[i]);
            (pos[i], neg[i]) = (then!, @else!);
        }
        return (pos, neg);
    }

    /// <summary>The hypotheses in scope in the chain's <paramref name="i"/>-th branch, or in its fallback when i is the length.</summary>
    private static IReadOnlyList<Expr> ChainScope((Expr[] Pos, Expr[] Neg)? hyps, int i) =>
        hyps is not { } h ? [] : i < h.Pos.Length ? [.. h.Neg[..i], h.Pos[i]] : h.Neg;

    /// <summary>
    /// <c>@dite T P D (fun h => a) (fun h => b)</c> when either branch makes a recursive call, else M4's <c>@ite T P D a b</c>
    /// (KTD15). The two are definitionally equal, which the equation lemma's proof relies on.
    /// </summary>
    private Expr IfThenElse(Expr type, Condition c, Expr? hThen, Expr a, Expr? hElse, Expr b)
    {
        if (_rec?.Fvar is { } rec && hThen is not null && hElse is not null && (Mentions(a, rec) || Mentions(b, rec)))
        {
            return Expr.App(Init.Dite, type, c.Prop, c.DecidableInstance, _lctx.MkLambda([hThen], a), _lctx.MkLambda([hElse], b));
        }
        return Operators.Ite(type, c, a, b);
    }

    /// <summary>A chain <c>if t₀ then v₀ else if t₁ then v₁ … else fallback</c>, each level as <see cref="IfThenElse"/>.</summary>
    private Expr Chain(Expr type, IReadOnlyList<Condition> tests, IReadOnlyList<Expr> values, Expr fallback, (Expr[] Pos, Expr[] Neg)? hyps)
    {
        var result = fallback;
        for (int i = tests.Count - 1; i >= 0; i--)
        {
            result = IfThenElse(type, tests[i], hyps?.Pos[i], values[i], hyps?.Neg[i], result);
        }
        return result;
    }

    /// <summary>Translates with <paramref name="fvars"/> in scope.</summary>
    private T InScope<T>(IReadOnlyList<Expr> fvars, Func<T> translate)
    {
        int count = _scope.Count;
        _scope.AddRange(fvars);
        try
        {
            return translate();
        }
        finally
        {
            _scope.RemoveRange(count, _scope.Count - count);
        }
    }

    private T InScope<T>(Expr? fvar, Func<T> translate) => InScope(fvar is null ? [] : [fvar], translate);

    private static bool Mentions(Expr e, FVarExpr fvar) =>
        e.HasFVar && ExprOps.Find(e, (x, _) => x is FVarExpr f && f.Id == fvar.Id) is not null;

    /// <summary><c>@LT.lt Nat instLTNat a b</c>.</summary>
    private static Expr NatLt(Expr a, Expr b) => Expr.App(Init.Lt, Init.Nat, Init.LtNat, a, b);

    /// <summary>The domain of the functional: the one type, or <c>(_ : A) ×' ((_ : B) ×' C)</c>, right-nested.</summary>
    private static Expr PackedType(IReadOnlyList<Expr> types, int from) =>
        from == types.Count - 1
            ? types[from]
            : Expr.App(Init.PSigma, types[from], Expr.Lam(Init.Unused, types[from], Conditions.Closed(PackedType(types, from + 1))));

    /// <summary>The packed value of <paramref name="values"/>: the one value, or <c>⟨a, ⟨b, c⟩⟩</c>.</summary>
    private static Expr Pack(IReadOnlyList<Expr> values, IReadOnlyList<Expr> types, int from = 0)
    {
        if (from == values.Count - 1)
        {
            return values[from];
        }
        var rest = Expr.Lam(Init.Unused, types[from], Conditions.Closed(PackedType(types, from + 1)));
        return Expr.App(Init.PSigmaMk, types[from], rest, values[from], Pack(values, types, from + 1));
    }

    /// <summary>The parameters read from the packed <paramref name="x"/>: <c>x</c> itself for one, else <c>x.1</c>, <c>x.2.1</c>, …, <c>x.2…2</c>.</summary>
    private static List<Expr> Projections(Expr x, int count)
    {
        var result = new List<Expr>();
        var rest = x;
        for (int i = 0; i < count - 1; i++)
        {
            result.Add(Expr.Proj(Init.PSigmaName, 0, rest));
            rest = Expr.Proj(Init.PSigmaName, 1, rest);
        }
        result.Add(rest);
        return result;
    }

    /// <summary>The state of one recursive method's translation.</summary>
    private sealed class RecursionState
    {
        private readonly Dictionary<CallExpr, int> _calls = new(ReferenceEqualityComparer.Instance);

        public RecursionState(VirUnit unit, FVarExpr fvar, IReadOnlyList<Expr> binders, IReadOnlyList<Expr> types, Func<IReadOnlyList<Expr>, Expr> measure, VirExpr measureNode)
        {
            Key = unit.Key;
            Fvar = fvar;
            Binders = binders;
            Types = types;
            Measure = measure;
            MeasureNode = measureNode;
            Number(unit.Body!);
        }

        public string Key { get; }

        /// <summary>The functional's <c>rec</c>.</summary>
        public FVarExpr Fvar { get; }

        /// <summary>The method's binders: <c>self</c> for an instance member, then the parameters.</summary>
        public IReadOnlyList<Expr> Binders { get; }

        public IReadOnlyList<Expr> Types { get; }

        /// <summary><c>μ(v) = Int.toNat (T.toInt measure[v])</c>, for values of the binders.</summary>
        public Func<IReadOnlyList<Expr>, Expr> Measure { get; }

        public VirExpr MeasureNode { get; }

        public bool Mentions(Expr e) => BodyTranslator.Mentions(e, Fvar);

        /// <summary>The call's number among the method's calls to itself, from 1, in pre-order (source order).</summary>
        public int IndexOf(CallExpr call) =>
            _calls.TryGetValue(call, out var index) ? index : throw new InvalidOperationException("a recursive call is not among the unit's nodes");

        private void Number(VirNode node)
        {
            if (node is CallExpr call && string.Equals(call.Target, Key, StringComparison.Ordinal))
            {
                _calls.TryAdd(call, _calls.Count + 1);
            }
            foreach (var child in VirTree.Children(node))
            {
                Number(child);
            }
        }
    }
}
