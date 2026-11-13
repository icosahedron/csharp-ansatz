using Warrant.Cic;
using Warrant.Vir;

namespace Warrant.Semantics;

/// <summary>
/// Statements, in continuation-passing style with the five placement rules of docs/m4/05 ("Statements and control flow",
/// KTD7). A statement list is translated together with its continuation, "the rest of the block". A continuation that is
/// more than a single leaf is never copied: where two branches both fall through into it, it becomes a <c>let</c>-bound
/// join point, so the size of a translated method is linear in the size of its source.
/// </summary>
internal sealed partial class BodyTranslator
{
    private static readonly BlockStmt EmptyBlock = new(VirList<VirStmt>.Empty);

    /// <summary>Translates <c>stmts[i..]</c>, then <paramref name="k"/> if control falls off the end.</summary>
    private Expr Statements(IReadOnlyList<VirStmt> stmts, int i, Env env, Continuation k)
    {
        if (i == stmts.Count)
        {
            return k.Invoke(env);
        }
        var rest = i + 1 == stmts.Count ? k : new Rest(this, stmts, i + 1, k);
        return stmts[i] switch
        {
            // `return e` is `e`, or in a method that can raise, `e`'s program; extraction rejects anything after it as
            // unreachable.
            ReturnStmt r => _sigma is null ? Value(r.Value, env) : Bound(r.Value, env, null),
            DeclStmt d => Assign(d.Local, d.Init, env, rest),
            AssignStmt a => Assign(a.Local, a.Value, env, rest),
            BlockStmt b => Statements(b.Stmts, 0, env, rest),
            IfStmt s => If(s, env, rest),
            SwitchStmt s => SwitchStatement(s, env, rest),
            // The measure is read on entry; it is the recursion's, not a statement of the body (M5a KTD14).
            DecreasesStmt when _sigma is null => rest.Invoke(env),
            // `throw new E(…)` raises `thrown "T:E"` (M6 KTD4); control does not reach the rest.
            ThrowStmt t when _sigma is not null => Site(t, Monadic.Throw(_sigma, Monadic.ValueType(k.ResultType), Monadic.Thrown(t.Exception))),
            AssertStmt a when _sigma is not null => Assert(a, env, rest),
            // A call run for its effects (M6 U19): its program bound and its value dropped. A call that cannot raise has
            // no effect to keep.
            EvalStmt e when _sigma is not null => Bound(e.Value, env, new Next(rest.ResultType, _ => rest.Invoke(env))),
            // A call that cannot raise has no effect to keep, though its arguments' arithmetic still must not overflow (#244).
            EvalStmt e when IsPure(e.Value) && _overflowObligations => Discard(Value(e.Value, env), () => rest.Invoke(env)),
            EvalStmt e when IsPure(e.Value) => rest.Invoke(env),
            // Claims, never run: the contract obligation states them (M6 KTD12, Contracts.cs). A Spec.Requires is a fact for
            // the obligations of the Spec.Asserts after it (#235).
            RequiresStmt r when Contracted && _facts is not null => WithFacts([(RequiresFact(r, env), true)], () => rest.Invoke(env)),
            RequiresStmt or EnsuresStmt when Contracted => rest.Invoke(env),
            // A claim about the exception postcondition, which the obligation states when the method can raise; a pure
            // method raises nothing, so it holds already (#182).
            NoThrowStmt => rest.Invoke(env),
            RequiresStmt or EnsuresStmt => throw new TranslationException(null, "a contract would be dropped unread: the unit's obligation is not being stated."),
            var other => throw new TranslationException(null, $"unsupported statement {other.GetType().Name}."),
        };
    }

    /// <summary>
    /// <c>x = e</c> or <c>var x = e</c>, then <paramref name="k"/>: <c>let x := e; k</c>, or, when <c>e</c> can raise,
    /// <c>e</c>'s program bound to <c>x</c> (M6 U9).
    /// </summary>
    private Expr Assign(int local, VirExpr value, Env env, Continuation k)
    {
        if (_sigma is null || IsPure(value))
        {
            return Let(local, Value(value, env), env, k);
        }
        return Bound(value, env, new Next(k.ResultType, v => IsBound(v) ? k.Invoke(env.Set(local, v)) : Let(local, v, env, k), Name.From(Local(local).Name)));
    }

    /// <summary>
    /// An <c>if</c> statement: <c>ite</c>, or, on the way to a recursive call, <c>dite</c>, whose hypotheses are in scope in
    /// the branches (M5a KTD15). In a method that can raise, a condition that can raise is bound first (M6 U9).
    /// </summary>
    private Expr If(IfStmt s, Env env, Continuation k) =>
        _sigma is null || IsPure(s.C) ? If(s, Cond(s.C, env), env, k) : CondBound(s.C, env, k.ResultType, c => If(s, c, env, k));

    private Expr If(IfStmt s, Condition c, Env env, Continuation k)
    {
        var (hThen, hElse) = Hypotheses(c);
        return Branches(
            [s.Then, s.Else ?? EmptyBlock],
            hThen is null ? null : [[hThen], [hElse!]],
            (terms, type) => IfThenElse(type, c, hThen, terms[0], hElse, terms[1]),
            env,
            k,
            [[c.Prop], [Expr.App(Init.Not, c.Prop)]]);
    }

    /// <summary>
    /// A <c>Spec.Requires</c>'s condition as a proposition, for the obligations of the <c>Spec.Assert</c>s after it (#235),
    /// translated as the contract states it, recording nothing.
    /// </summary>
    private Expr RequiresFact(RequiresStmt r, Env env)
    {
        var outer = _spec;
        _spec = new SpecState(_assertSpecUnit!, null, []);
        try
        {
            return Cond(r.Condition, env).Prop;
        }
        finally
        {
            _spec = outer;
        }
    }

    /// <summary><paramref name="then"/>, after a value that is translated only for the obligations it records.</summary>
    private static Expr Discard(Expr value, Func<Expr> then)
    {
        _ = value;
        return then();
    }

    /// <summary>One statement, then <paramref name="k"/>.</summary>
    private Expr Statement(VirStmt s, Env env, Continuation k) =>
        s is BlockStmt b ? Statements(b.Stmts, 0, env, k) : Statements([s], 0, env, k);

    /// <summary><c>let x := value</c>, with <c>x</c> holding the new value in <paramref name="k"/>.</summary>
    private Expr Let(int local, Expr value, Env env, Continuation k)
    {
        var decl = Local(local);
        var fvar = _lctx.MkLetDecl(_ngen, Name.From(decl.Name), _types.Cic(decl.Init.Type), value);
        return _lctx.MkLambda([fvar], InScope(fvar, () => k.Invoke(env.Set(local, fvar))));
    }

    /// <summary>
    /// A branching statement (an <c>if</c>, or a <c>switch</c> with one branch per section) followed by
    /// <paramref name="k"/>. <paramref name="combine"/> builds the <c>ite</c> or recursor from the branches' terms and
    /// their type. The first rule that applies:
    /// 1. no branch falls through: the branches alone, and <paramref name="k"/> is unreachable;
    /// 2. one branch falls through: <paramref name="k"/> is translated once, into that branch;
    /// 3. neither contains a <c>return</c>, and they change exactly one local <c>x</c> that <paramref name="k"/> reads:
    ///    <c>let x := combine(x after each branch); k</c>;
    /// 4. neither contains a <c>return</c> or a call of the recursive method being translated, and they change no local
    ///    <paramref name="k"/> reads: <paramref name="k"/> alone (a skipped call would leave its decrease unchecked; nor,
    ///    while a pure body's obligations are stated, implicit arithmetic, which must not overflow even unread, #244, or a
    ///    call to a method with <c>Spec.Requires</c>, whose precondition must hold even unread, #256);
    /// 5. otherwise a join point over the locals <paramref name="k"/> reads and some branch changes.
    /// Each branch is translated with its <paramref name="hypotheses"/> in scope, when there are any. In a method that can
    /// raise, rules 3 and 4 do not apply: a branch that can raise can be neither dropped nor reduced to a value, so the
    /// monadic translation keeps the join points and drops the shortcuts (docs/m4/05, M6 U9).
    /// </summary>
    private Expr Branches(
        IReadOnlyList<VirStmt> branches,
        IReadOnlyList<IReadOnlyList<Expr>>? hypotheses,
        Func<IReadOnlyList<Expr>, Expr, Expr> combine,
        Env env,
        Continuation k,
        IReadOnlyList<IReadOnlyList<Expr>>? facts = null)
    {
        Expr Branch(int i, Continuation then) =>
            InScope(hypotheses?[i] ?? [], () => WithFacts((facts?[i] ?? []).Select(f => (f, true)), () => Statement(branches[i], env, then)));

        int falling = branches.Count(FallsThrough);
        if (falling <= 1)
        {
            var unreachable = new Unreachable(k.ResultType);
            return combine([.. branches.Select((b, i) => Branch(i, FallsThrough(b) ? k : unreachable))], k.ResultType);
        }
        bool returns = branches.Any(b => Nodes(b).Any(n => n is ReturnStmt));
        var live = branches
            .SelectMany(b => Nodes(b).OfType<AssignStmt>().Select(a => a.Local))
            .Where(k.Reads.Contains)
            .Distinct()
            .Order()
            .ToList();
        bool recurses = _selfKey is { } selfKey && branches.Any(b => Nodes(b).Any(n => n is CallExpr c && string.Equals(c.Target, selfKey, StringComparison.Ordinal)));
        // While a pure body's obligations are stated, a branch is never dropped while it has implicit arithmetic (#244) or a
        // call to a method with Spec.Requires, which can only be the method's call to itself (#256): each has an obligation.
        recurses |= _overflowObligations && branches.Any(b => BodyNodes(b).Any(n =>
            (n is VirExpr e && SpecOverflows(e)) || (n is CallExpr c && HasRequires(c.Target))));
        if (_sigma is not null)
        {
            return JoinPoint(branches, Branch, combine, live, env, k);
        }
        if (!returns && !recurses && live.Count == 0)
        {
            return k.Invoke(env);
        }
        if (!returns && live.Count == 1)
        {
            var leaf = new Leaf(live[0], _types.Cic(Local(live[0]).Init.Type));
            var value = combine([.. branches.Select((_, i) => Branch(i, leaf))], leaf.ResultType);
            return Let(live[0], value, env, k);
        }
        return JoinPoint(branches, Branch, combine, live, env, k);
    }

    /// <summary>
    /// Rule 5: <c>let jp := fun (x₁ … xₙ) =&gt; k; combine(branches)</c>, where every point a branch falls through becomes
    /// <c>jp</c> applied to the current values of <c>x₁ … xₙ</c>.
    /// </summary>
    private Expr JoinPoint(
        IReadOnlyList<VirStmt> branches,
        Func<int, Continuation, Expr> branch,
        Func<IReadOnlyList<Expr>, Expr, Expr> combine,
        List<int> live,
        Env env,
        Continuation k)
    {
        var parameters = live.Select(x => (Expr)_lctx.MkLocalDecl(_ngen, Name.From(Local(x).Name), _types.Cic(Local(x).Init.Type))).ToList();
        var inner = env;
        for (int i = 0; i < live.Count; i++)
        {
            inner = inner.Set(live[i], parameters[i]);
        }
        if (_overflowObligations)
        {
            return KnownJoinPoint(branches, branch, combine, live, parameters, inner, k);
        }
        var body = _lctx.MkLambda(parameters, InScope(parameters, () => WithFacts(parameters.Select(p => (p, false)), () => k.Invoke(inner))));
        var jp = _lctx.MkLetDecl(_ngen, JoinPointName, _lctx.MkPi(parameters, k.ResultType), body);
        var jump = new Jump(jp, live, k.ResultType);
        var unreachable = new Unreachable(k.ResultType);
        var term = InScope(jp, () => combine([.. Enumerable.Range(0, branches.Count).Select(i => branch(i, FallsThrough(branches[i]) ? jump : unreachable))], k.ResultType));
        return _lctx.MkLambda([jp], term);
    }

    /// <summary>
    /// Rule 5 while a pure body's obligations are stated (#244, #255): the branches first, each jump recording what its path
    /// knows, then <paramref name="k"/>, whose obligations know that one of the incoming paths was taken, with its values.
    /// Each path gives <c>∃ ys, facts ∧ x₁ = v₁ ∧ … ∧ xₙ = vₙ</c> over the facts added on it since the branch point and
    /// the values its jump passes, an <c>int</c> or <c>long</c> compared by <c>toInt</c>; <c>ys</c> are the parameters of
    /// join points inside the branch, out of scope at this one. The parameters are bound with their disjunction as a fact.
    /// The term is <c>(fun jp =&gt; combine(branches)) (fun x₁ … xₙ =&gt; k)</c>, which only the obligations read.
    /// </summary>
    private Expr KnownJoinPoint(
        IReadOnlyList<VirStmt> branches,
        Func<int, Continuation, Expr> branch,
        Func<IReadOnlyList<Expr>, Expr, Expr> combine,
        List<int> live,
        List<Expr> parameters,
        Env inner,
        Continuation k)
    {
        var jp = _lctx.MkLocalDecl(_ngen, JoinPointName, _lctx.MkPi(parameters, k.ResultType));
        var paths = new List<Expr>();
        var jump = new KnownJump(this, jp, live, parameters, _facts!.Count, paths, k.ResultType);
        var unreachable = new Unreachable(k.ResultType);
        var term = combine([.. Enumerable.Range(0, branches.Count).Select(i => branch(i, FallsThrough(branches[i]) ? jump : unreachable))], k.ResultType);
        IEnumerable<(Expr, bool)> known = parameters.Select(p => (p, false));
        if (paths.Count > 0)
        {
            known = [.. known, (paths.Skip(1).Aggregate(paths[0], (a, b) => Expr.App(Init.Or, a, b)), true)];
        }
        var body = _lctx.MkLambda(parameters, WithFacts(known, () => k.Invoke(inner)));
        return Expr.App(_lctx.MkLambda([jp], term), body);
    }

    /// <summary>
    /// What one path knows where it jumps to a join point (#255): <c>∃ ys, facts ∧ x₁ = v₁ ∧ …</c>, as
    /// <see cref="KnownJoinPoint"/> states it, from the facts after the first <paramref name="from"/>.
    /// </summary>
    private Expr PathFact(List<int> live, List<Expr> parameters, Env env, int from)
    {
        var entries = _facts!.Skip(from).ToList();
        var parts = new List<Expr>();
        // The exact values this path's implicit operations were found to have (`(a + 15).toInt = a.toInt + 15`, #244): an
        // int parameter's value is stated through them, `x.toInt = a.toInt + 15`, so omega need not read the operation
        // through the wrap-around (#272), and such a fact is kept only where something else still mentions its operation.
        // Exact-value facts are told apart by where they came from (SpecState.Known), never by their shape.
        var exact = new Dictionary<Expr, Expr>();
        foreach (var entry in entries.Where(e => e.IsFact))
        {
            var known = Zeta(entry.Value);
            if (_exactFacts.Contains(entry.Value) && known.GetAppArgs() is [_, var lhs, var rhs])
            {
                exact.TryAdd(lhs, rhs);
            }
            else
            {
                parts.Add(known);
            }
        }
        Expr Exactly(Expr e) => Warrant.Kernel.ExprOps.Replace(e, (x, _) => exact.TryGetValue(x, out var v) ? Exactly(v) : null);
        for (int i = 0; i < live.Count; i++)
        {
            var type = Local(live[i]).Init.Type;
            var value = Zeta(env.Get(live[i]));
            parts.Add(type == VirType.Int32 || type == VirType.Int64
                ? Expr.App(Init.Eq, Init.Int, ToInt(_types.Underlying(type), parameters[i]), Exactly(ToInt(_types.Underlying(type), value)))
                : Expr.App(Init.Eq, _types.Cic(type), parameters[i], value));
        }
        // Kept: every exact-value fact whose operation something kept still mentions, to a fixpoint, so a kept fact's own
        // operands keep theirs.
        var kept = new List<KeyValuePair<Expr, Expr>>();
        bool Mentions(Expr p, Expr lhs) => Warrant.Kernel.ExprOps.Find(p, (y, _) => y == lhs.GetAppArgs()[0]) is not null;
        for (bool grew = true; grew;)
        {
            grew = false;
            foreach (var x in exact.Where(x => !kept.Contains(x)).ToList())
            {
                if (parts.Any(p => Mentions(p, x.Key)) || kept.Any(k => Mentions(k.Value, x.Key)))
                {
                    kept.Add(x);
                    grew = true;
                }
            }
        }
        parts.InsertRange(0, kept.Select(x => Expr.App(Init.Eq, Init.Int, x.Key, x.Value)));
        var fact = parts.Count == 0 ? Init.PropTrue : parts.SkipLast(1).Reverse().Aggregate(parts[^1], (acc, p) => Expr.App(Init.And, p, acc));
        foreach (var y in entries.Where(e => !e.IsFact).Select(e => e.Value).Reverse())
        {
            fact = Expr.App(Init.Exists, _lctx.Get(y).Type, _lctx.MkLambda([y], fact));
        }
        return fact;
    }

    /// <summary>A jump to a join point whose incoming paths are recorded (#255): <c>jp</c> applied, as <see cref="Jump"/>.</summary>
    private sealed class KnownJump(BodyTranslator owner, Expr joinPoint, List<int> locals, List<Expr> parameters, int from, List<Expr> paths, Expr type)
        : Continuation(type)
    {
        public override IReadOnlySet<int> Reads { get; } = locals.ToHashSet();

        public override Expr Invoke(Env env)
        {
            paths.Add(owner.PathFact(locals, parameters, env, from));
            return Expr.App(joinPoint, [.. locals.Select(env.Get)]);
        }
    }

    private static readonly Name JoinPointName = Name.From("jp");

    /// <summary>Whether control can reach the end of a statement, as extraction's reachability check decides it.</summary>
    private static bool FallsThrough(VirStmt s) => s switch
    {
        ReturnStmt or ThrowStmt => false,
        BlockStmt b => b.Stmts.All(FallsThrough),
        IfStmt i => i.Else is null || FallsThrough(i.Then) || FallsThrough(i.Else),
        SwitchStmt sw => !sw.Sections.Any(IsDefault) || sw.Sections.Any(section => section.Body.All(FallsThrough)),
        _ => true,
    };

    private static bool IsDefault(SwitchSection section) => section.Labels.Any(l => l is DiscardPattern);

    private DeclStmt Local(int id) =>
        _locals.TryGetValue(id, out var d) ? d : throw new TranslationException(null, $"the local {id} is not declared.");

    /// <summary>A node and all its descendants.</summary>
    private static IEnumerable<VirNode> Nodes(VirNode node)
    {
        var stack = new Stack<VirNode>();
        stack.Push(node);
        while (stack.Count > 0)
        {
            var n = stack.Pop();
            yield return n;
            foreach (var child in VirTree.Children(n))
            {
                stack.Push(child);
            }
        }
    }

    // ---- Continuations ----

    /// <summary>What happens when control falls off the end of a statement list.</summary>
    private abstract class Continuation(Expr resultType)
    {
        /// <summary>The type of the term the continuation produces.</summary>
        public Expr ResultType { get; } = resultType;

        /// <summary>The locals the continuation may read (syntactically; an over-approximation is safe).</summary>
        public abstract IReadOnlySet<int> Reads { get; }

        /// <summary>The continuation's term, given the locals' values at the point control reaches it.</summary>
        public abstract Expr Invoke(Env env);
    }

    /// <summary>The rest of a block, then the block's own continuation. It is translated at most once.</summary>
    private sealed class Rest(BodyTranslator owner, IReadOnlyList<VirStmt> stmts, int start, Continuation outer) : Continuation(outer.ResultType)
    {
        private HashSet<int>? _reads;
        private bool _invoked;

        public override IReadOnlySet<int> Reads =>
            _reads ??= [.. stmts.Skip(start).SelectMany(Nodes).OfType<LocalExpr>().Select(l => l.Id), .. outer.Reads];

        public override Expr Invoke(Env env)
        {
            if (_invoked)
            {
                throw new InvalidOperationException("a continuation was translated twice");
            }
            _invoked = true;
            return owner.Statements(stmts, start, env, outer);
        }
    }

    /// <summary>Rule 3's continuation: the single local's current value, a leaf that may be copied.</summary>
    private sealed class Leaf(int local, Expr type) : Continuation(type)
    {
        public override IReadOnlySet<int> Reads { get; } = new HashSet<int> { local };

        public override Expr Invoke(Env env) => env.Get(local);
    }

    /// <summary>A jump to a join point: <c>jp</c> applied to the current values of its locals.</summary>
    private sealed class Jump(Expr joinPoint, List<int> locals, Expr type) : Continuation(type)
    {
        public override IReadOnlySet<int> Reads { get; } = locals.ToHashSet();

        public override Expr Invoke(Env env) => Expr.App(joinPoint, [.. locals.Select(env.Get)]);
    }

    /// <summary>
    /// What control reaching the end of a method body means: returning nothing, <c>()</c> or <c>pure ()</c>, for a method
    /// that returns no value (M6 KTD22, U19), and otherwise a translation error, since extraction rejects a body that can
    /// fall off its end.
    /// </summary>
    private Continuation End(VirUnit unit, Expr returns) =>
        !ReturnsNothing(unit) ? new Unreachable(returns)
        : _sigma is null ? new Returns(returns, Init.UnitUnit)
        : new Returns(returns, Monadic.Pure(_sigma, Init.Unit, Init.UnitUnit));

    /// <summary>The end of a method that returns no value: its fixed result, a leaf that may be copied.</summary>
    private sealed class Returns(Expr type, Expr value) : Continuation(type)
    {
        public override IReadOnlySet<int> Reads { get; } = new HashSet<int>();

        public override Expr Invoke(Env env) => value;
    }

    /// <summary>The end of a method body or of a branch that returns on every path; reaching it is a translation error.</summary>
    private sealed class Unreachable(Expr type) : Continuation(type)
    {
        public override IReadOnlySet<int> Reads { get; } = new HashSet<int>();

        public override Expr Invoke(Env env) =>
            throw new TranslationException(null, "control reaches the end of a block that must return a value.");
    }
}
