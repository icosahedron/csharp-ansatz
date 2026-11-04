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
            // `return e` is `e`; extraction rejects anything after it as unreachable.
            ReturnStmt r => Value(r.Value, env),
            DeclStmt d => Let(d.Local, Value(d.Init, env), env, rest),
            AssignStmt a => Let(a.Local, Value(a.Value, env), env, rest),
            BlockStmt b => Statements(b.Stmts, 0, env, rest),
            IfStmt s => If(s, env, rest),
            SwitchStmt s => SwitchStatement(s, env, rest),
            // The measure is read on entry; it is the recursion's, not a statement of the body (M5a KTD14).
            DecreasesStmt => rest.Invoke(env),
            var other => throw new TranslationException(null, $"unsupported statement {other.GetType().Name}."),
        };
    }

    /// <summary>
    /// An <c>if</c> statement: <c>ite</c>, or, on the way to a recursive call, <c>dite</c>, whose hypotheses are in scope in
    /// the branches (M5a KTD15).
    /// </summary>
    private Expr If(IfStmt s, Env env, Continuation k)
    {
        var c = Cond(s.C, env);
        var (hThen, hElse) = Hypotheses(c);
        return Branches(
            [s.Then, s.Else ?? EmptyBlock],
            hThen is null ? null : [[hThen], [hElse!]],
            (terms, type) => IfThenElse(type, c, hThen, terms[0], hElse, terms[1]),
            env,
            k);
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
    /// 4. neither contains a <c>return</c>, and they change no local <paramref name="k"/> reads: <paramref name="k"/> alone;
    /// 5. otherwise a join point over the locals <paramref name="k"/> reads and some branch changes.
    /// Each branch is translated with its <paramref name="hypotheses"/> in scope, when there are any.
    /// </summary>
    private Expr Branches(
        IReadOnlyList<VirStmt> branches,
        IReadOnlyList<IReadOnlyList<Expr>>? hypotheses,
        Func<IReadOnlyList<Expr>, Expr, Expr> combine,
        Env env,
        Continuation k)
    {
        Expr Branch(int i, Continuation then) => InScope(hypotheses?[i] ?? [], () => Statement(branches[i], env, then));

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
        if (!returns && live.Count == 0)
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
        var body = _lctx.MkLambda(parameters, InScope(parameters, () => k.Invoke(inner)));
        var jp = _lctx.MkLetDecl(_ngen, JoinPointName, _lctx.MkPi(parameters, k.ResultType), body);
        var jump = new Jump(jp, live, k.ResultType);
        var unreachable = new Unreachable(k.ResultType);
        var term = InScope(jp, () => combine([.. Enumerable.Range(0, branches.Count).Select(i => branch(i, FallsThrough(branches[i]) ? jump : unreachable))], k.ResultType));
        return _lctx.MkLambda([jp], term);
    }

    private static readonly Name JoinPointName = Name.From("jp");

    /// <summary>Whether control can reach the end of a statement, as extraction's reachability check decides it.</summary>
    private static bool FallsThrough(VirStmt s) => s switch
    {
        ReturnStmt => false,
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

    /// <summary>The end of a method body or of a branch that returns on every path; reaching it is a translation error.</summary>
    private sealed class Unreachable(Expr type) : Continuation(type)
    {
        public override IReadOnlySet<int> Reads { get; } = new HashSet<int>();

        public override Expr Invoke(Env env) =>
            throw new TranslationException(null, "control reaches the end of a block that must return a value.");
    }
}
