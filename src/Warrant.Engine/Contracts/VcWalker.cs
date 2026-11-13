using System.Collections.Immutable;
using System.Globalization;
using Warrant.Cic;
using Warrant.Kernel;
using Warrant.Meta;
using Warrant.Semantics;
using Warrant.Vir;

namespace Warrant.Engine.Contracts;

/// <summary>What a verification condition states (plan M6 U11 step 5, #90, #163): the first words of its failure.</summary>
public enum VcKind
{
    /// <summary>A <c>/</c> or <c>%</c> whose divisor may be zero.</summary>
    DivisionByZero,

    /// <summary>A checked operation, a narrowing, <c>MinValue / -1</c>, <c>Math.Abs(MinValue)</c> or decimal arithmetic that may overflow.</summary>
    Overflow,

    /// <summary><c>Value</c> of a null <c>Nullable&lt;T&gt;</c>, or a member access through a null reference.</summary>
    NullRead,

    /// <summary>A nullable value used where a non-null one is required (#163), such as a call argument.</summary>
    NullPassed,

    /// <summary>A verified callee's <c>Spec.Requires</c> at its call.</summary>
    CalleePrecondition,

    /// <summary>The method's <c>Spec.Ensures</c>.</summary>
    Postcondition,

    /// <summary>A <c>Spec.Assert</c>'s condition.</summary>
    Assert,

    /// <summary>That an operation in a <c>Spec</c> expression does not raise (KTD26).</summary>
    WellDefinedness,

    /// <summary>A program shape the walker has no rule for (KTD13): the triple itself is left to simp and omega.</summary>
    Unsupported,

    /// <summary>A dependency member's <c>Spec.Requires</c> at its call (M6 U20, KTD9), as its contract class states it.</summary>
    DependencyPrecondition,

    /// <summary>An explicit <c>throw</c> of a method with <c>Spec.NoThrow</c> that the walk could not show unreachable (#182).</summary>
    ReachableThrow,

    /// <summary>
    /// A call, in a method with <c>Spec.NoThrow</c>, to a verified callee that may throw explicitly: one without
    /// <c>Spec.NoThrow</c> (#182).
    /// </summary>
    CalleeMayThrow,

    /// <summary>
    /// <c>+</c>, <c>-</c>, <c>*</c> or unary <c>-</c> on <c>int</c> or <c>long</c> in C#'s default context, in a verified
    /// method's body, that may overflow (#244): the CLR would wrap, which Warrant treats as a mistake unless the code says
    /// <c>unchecked</c>.
    /// </summary>
    ArithmeticOverflow,
}

/// <summary>A verification condition the default procedure did not prove (#90): WRT0001 at its node.</summary>
/// <param name="Kind">What it states.</param>
/// <param name="Node">The VIR node ID of the operation or <c>Spec</c> call that produced it (KTD18); null when it has none.</param>
/// <param name="Message">Its kind, then why it was not proved; the first line is complete on its own.</param>
/// <param name="Goals">Its goal after the VC simp set, with the path conditions as hypotheses, as Lean shows goals.</param>
public sealed record VcFailure(VcKind Kind, int? Node, string Message, string Goals);

/// <summary>The words that start a failing VC's message.</summary>
public static class VcKinds
{
    /// <summary>The kind's text, e.g. <c>division by zero</c>.</summary>
    /// <param name="kind">The kind.</param>
    /// <returns>The text.</returns>
    public static string Text(VcKind kind) => kind switch
    {
        VcKind.DivisionByZero => "division by zero",
        VcKind.Overflow => "overflow in a checked operation",
        VcKind.NullRead => "null read",
        VcKind.NullPassed => "null passed where a non-null value is required",
        VcKind.CalleePrecondition => "precondition of a callee at this call",
        VcKind.Postcondition => "postcondition of the method",
        VcKind.Assert => "Spec.Assert",
        VcKind.WellDefinedness => "well-definedness of a Spec expression",
        VcKind.Unsupported => "a program shape the VC walker has no rule for",
        VcKind.DependencyPrecondition => "precondition of a dependency member at this call",
        VcKind.ReachableThrow => "an explicit throw is reachable under the Requires (Spec.NoThrow)",
        VcKind.CalleeMayThrow => "a callee without Spec.NoThrow may throw explicitly at this call (Spec.NoThrow)",
        VcKind.ArithmeticOverflow => "arithmetic overflow: this int/long operation may overflow, where C# would wrap (write unchecked(...) if wrapping is intended)",
        _ => throw new ArgumentOutOfRangeException(nameof(kind)),
    };
}

/// <summary>An explicit throw the walker could not show unreachable (#92): a <c>MayThrow</c> of the method (KTD20).</summary>
/// <param name="Node">The throw's VIR node ID; null when the program carries none.</param>
/// <param name="Type">The thrown type's key, e.g. <c>T:System.ArgumentException</c>.</param>
internal sealed record VcThrow(int? Node, string Type);

/// <summary>A goal the walker leaves to the VC simp set and omega, with what it states.</summary>
/// <param name="Goal">The goal.</param>
/// <param name="Kind">What it states.</param>
/// <param name="Node">The VIR node it is reported at.</param>
/// <param name="Failure">Why it already failed (a <c>Spec.Assert</c>'s own script); null when it is still to be tried.</param>
internal sealed record VcLeftover(MVarId Goal, VcKind Kind, int? Node, string? Failure = null);

/// <summary>
/// The VC walker (plan M6 KTD13, U11): proves a contract obligation <c>⦃⌜Requires⌝⦄ prog ⦃Q⦄</c> by walking the program's
/// structure with <see cref="SpecTable"/>'s rules through <see cref="MetaM.Apply"/>, leaving the goals no rule covers to the
/// VC simp set and omega (KTD14). It is untrusted (design D11): the kernel checks the proof it builds.
/// <list type="bullet">
/// <item>The precondition becomes a hypothesis (<c>Vc.pre</c>), so every goal after it is a triple from <c>⌜True⌝</c>,
/// and each fact a step learns, a branch's condition, a model operation's case, a callee's <c>Ensures</c>, is a
/// hypothesis of the goals after it: the path conditions.</item>
/// <item>A program that can raise is replaced by its body as <see cref="ContractObligation.Program"/> states it, whose sites
/// name their VIR nodes in metadata (KTD18); a pure unit under proof is unfolded in its postcondition VC instead (#173).</item>
/// <item><c>bind</c>, <c>pure</c>, <c>throw</c>, <c>ite</c>, <c>dite</c>, a match on a nullable value, a <c>Spec.Assert</c>
/// check, a verified callee, a call to a dependency member (its contract hypothesis at the current world, M6 U20) and a
/// model operation each have a rule; a closed enum's recursor is split with <c>Cases</c> when its discriminant is a
/// variable; anything else is a leftover VC, never a guessed rule, reported where the walk stopped (#223).</item>
/// <item>At an explicit throw, the walker first tries to show the path unreachable (#92); otherwise it is a
/// <see cref="VcThrow"/>.</item>
/// </list>
/// </summary>
internal sealed class VcWalker
{
    private static readonly Name BindName = Name.Parse("Bind.bind");
    private static readonly Name PureName = Name.Parse("Pure.pure");
    private static readonly Name IteName = Name.Parse("ite");
    private static readonly Name DiteName = Name.Parse("dite");
    private static readonly Name ThrowName = Name.Parse("Warrant.ClrM.throw");
    private static readonly Name OptionRecName = Name.Parse("Option.rec");
    private static readonly Name TripleName = Name.Parse("Std.Do.Triple");
    private static readonly Name ULiftDown = Name.Parse("ULift.down");
    private static readonly Name PredTransApply = Name.Parse("Std.Do.PredTrans.apply");
    private static readonly Name AndName = Name.Parse("And");
    private static readonly Name EqName = Name.Parse("Eq");
    private static readonly Name H = Name.From("h");
    private static readonly Name S = Name.From("s");
    private static readonly Name Sigma = Name.From("σ");
    private static readonly Name TrueName = Name.Parse("True");

    private readonly MetaM _m;
    private readonly VirUnit _unit;
    private readonly IReadOnlyList<VirNode> _nodes;
    private readonly Dictionary<VirNode, VirNode> _parents = new(ReferenceEqualityComparer.Instance);
    private readonly Dictionary<Name, Name> _models;
    private readonly VcKind _kind;
    private readonly int? _node;
    private readonly Name? _self;
    private readonly SimpContext _light;

    /// <summary>
    /// Whether the obligation is a contract of a method with <c>Spec.NoThrow</c> (#182), whose exception postcondition is
    /// <c>ClrExn.External</c>: an explicit throw it cannot show unreachable is a VC, not a <see cref="VcThrow"/>. A pure
    /// method's contract keeps <c>ClrExn.Allowed</c>, but its walk meets no throw and no dependency, and a pure callee's
    /// <c>Vc.callPure</c> uses no exception postcondition, so the flag changes nothing there.
    /// </summary>
    private readonly bool _noThrow;

    /// <summary>
    /// The bound operations of the method's dependencies (M6 U19, U20, KTD9), by their free variable once introduced: the
    /// contract hypothesis that states each one's triple, and the member's key.
    /// </summary>
    private readonly Dictionary<FVarId, (FVarExpr Hypothesis, string Member)> _operations = [];

    /// <summary>The last site the walk reached, where a shape it has no rule for is reported when that has no node of its own (#223).</summary>
    private int? _lastNode;

    /// <summary>A walker for one obligation of <paramref name="unit"/>.</summary>
    /// <param name="m">The Meta state the proof is built in.</param>
    /// <param name="attributes">The attribute sidecar, whose <c>spec</c> entries are the model operations' rules (KTD15).</param>
    /// <param name="unit">The unit whose obligation is walked: its nodes are the ones the program's sites name.</param>
    /// <param name="kind">
    /// What a leftover states when no site says otherwise: the method's postcondition, or for a well-definedness
    /// obligation, that.
    /// </param>
    /// <param name="node">Where such a leftover is reported: the first <c>Spec.Ensures</c>, or the partial operation.</param>
    /// <param name="self">For a pure unit under proof, its constant, unfolded in its postcondition VCs (#173); else null.</param>
    public VcWalker(MetaM m, Sidecar? attributes, VirUnit unit, VcKind kind, int? node, Name? self)
    {
        _m = m;
        _unit = unit;
        _nodes = VirTree.PreOrder(unit);
        foreach (var parent in _nodes)
        {
            foreach (var child in VirTree.Children(parent))
            {
                _parents.TryAdd(child, parent);
            }
        }
        _models = ModelSpecs(m.Env, attributes);
        _kind = kind;
        _node = node;
        _self = self;
        _light = VcSimpSet.Light(m);
        _noThrow = !IsOperation(kind) && HasNoThrow(unit);
    }

    /// <summary>
    /// Whether a walker of this kind proves that one operation does not raise (KTD26) or overflow (#244), so every leftover
    /// is that, at the operation.
    /// </summary>
    private static bool IsOperation(VcKind kind) => kind is VcKind.WellDefinedness or VcKind.ArithmeticOverflow;

    /// <summary>Whether a function's body has <c>Spec.NoThrow</c> (#182).</summary>
    public static bool HasNoThrow(VirUnit unit) => unit.Body is BlockStmt block && block.Stmts.Any(s => s is NoThrowStmt);

    /// <summary>The goals left to the VC simp set and omega, in the order the walk met them.</summary>
    public List<VcLeftover> Leftovers { get; } = [];

    /// <summary>The explicit throws the walk could not show unreachable (#92).</summary>
    public List<VcThrow> Throws { get; } = [];

    /// <summary>The verified callees whose contracts the walk used (KTD20), with the call's node.</summary>
    public List<(string Callee, int? Node)> Calls { get; } = [];

    /// <summary>
    /// The calls to dependency members the walk used a contract hypothesis at (M6 U20), with the call's node: each may
    /// propagate an exception from the member, which the contract allows (KTD12, KTD20).
    /// </summary>
    public List<(string Member, int? Node)> ExternalCalls { get; } = [];

    /// <summary>
    /// The pure verified callees, by constant, whose <c>f.$contract_spec</c> <see cref="Prepare"/> made a hypothesis of a
    /// leftover (#173): the proof may rest on their contracts, so the report lists them (KTD20, #223).
    /// </summary>
    public HashSet<Name> PureCallees { get; } = [];

    /// <summary>
    /// The model operations' rules: each <c>@[spec]</c> triple of the sidecar by the head constant of its program (KTD15),
    /// the highest priority first.
    /// </summary>
    private static Dictionary<Name, Name> ModelSpecs(KernelEnvironment env, Sidecar? attributes)
    {
        var table = new Dictionary<Name, Name>();
        foreach (var entry in (attributes?.SpecEntries ?? []).Where(e => e.Form == SpecForm.Triple).OrderByDescending(e => e.Priority))
        {
            if (env.Find(entry.Name) is not { } info)
            {
                continue;
            }
            var type = info.Type;
            while (type is ForallExpr f)
            {
                type = f.Body;
            }
            if (type.HeadIs(TripleName) && type.GetAppArgs() is { Length: 7 } args && args[4].GetAppFn() is ConstExpr head)
            {
                table.TryAdd(head.Name, entry.Name);
            }
        }
        return table;
    }

    // ------------------------------------------------------------------ entry points

    /// <summary>
    /// A contract obligation's triple, its binders already introduced: <c>Vc.pre</c> turns <c>Requires</c> into a
    /// hypothesis, a raising unit's program is replaced by its body (tagged when <paramref name="program"/> agrees with the
    /// definition), and the walk starts. <paramref name="operations"/> is the number of dependency operations the statement
    /// binds after the world, whose contract hypotheses are its last binders (M6 U19, <see cref="ContractObligation.Operations"/>).
    /// </summary>
    public void Contract(MVarId goal, Expr? program, Name function, bool raising, int operations = 0)
    {
        BindOperations(goal, operations);
        var g = Introduced(Rule(goal, () => _m.ApplyConst(goal, SpecTable.Pre)) ?? throw Failed(goal, "the obligation is not a triple from a precondition"));
        if (raising && _m.Env.Find(function) is DefinitionInfo definition)
        {
            var target = _m.InstantiateMVars(_m.GetMVarType(g));
            if (target.HeadIs(TripleName) && target.GetAppArgs() is { Length: 7 } args && args[4].HeadIs(function))
            {
                var body = program is not null && Strip(program) == definition.DefinitionValue ? program : definition.DefinitionValue;
                args[4] = ExprOps.HeadBetaReduce(ExprOps.MkApp(body, args[4].GetAppArgs()));
                g = _m.ReplaceTargetDefEq(g, ExprOps.MkApp(target.GetAppFn(), args));
            }
        }
        Walk(g);
    }

    /// <summary>
    /// Pairs each introduced operation with its contract hypothesis (KTD9): the statement binds the world, then the
    /// operations in dependency and member order, then <c>self</c> and the parameters, then one hypothesis per operation
    /// in the same order; the member keys come in that order from the unit's dependencies.
    /// </summary>
    private void BindOperations(MVarId goal, int operations)
    {
        if (operations == 0)
        {
            return;
        }
        var decls = (_m.MCtx.FindDecl(goal)?.LCtx.Decls ?? []).Where(d => !d.IsImplementationDetail).ToList();
        var members = (_unit.Dependencies ?? VirList<VirDependency>.Empty).SelectMany(d => d.Members).ToList();
        if (decls.Count < 1 + 2 * operations || members.Count != operations)
        {
            throw new InvalidOperationException($"the obligation binds {decls.Count} values, too few for {operations} operations and their contracts");
        }
        for (int i = 0; i < operations; i++)
        {
            _operations[decls[1 + i].FVarId] = (decls[decls.Count - operations + i].ToExpr(), members[i]);
        }
    }

    /// <summary>A well-definedness obligation's triple (KTD26), its binders already introduced: <c>⦃⌜True⌝⦄ op ⦃…⦄</c>.</summary>
    public void WellDefined(MVarId goal) => Walk(goal);

    /// <summary>The single goal of <paramref name="goals"/>, introduced once: a rule's <c>p → …</c> premise.</summary>
    private MVarId Introduced(IReadOnlyList<MVarId> goals) => _m.Intro1(Single(goals), H).Goal;

    private MVarId Single(IReadOnlyList<MVarId> goals)
    {
        var open = goals.Where(g => !_m.IsAssigned(g)).ToList();
        return open.Count == 1 ? open[0] : throw new InvalidOperationException($"the walker expected one goal, got {open.Count}");
    }

    private static TacticException Failed(MVarId goal, string why) => new("vcgen", goal, why);

    /// <summary>The name a binder is introduced under: its own, or <c>h</c> for an anonymous or hygienic one.</summary>
    private static Name Hypothesis(Name binder) =>
        binder.IsAnonymous || binder.ToString().Contains("_hyg", StringComparison.Ordinal) ? H : binder;

    // ------------------------------------------------------------------ the walk

    /// <summary>A goal <c>⦃⌜True⌝⦄ prog ⦃Q⦄</c>: the rule for <c>prog</c>'s head, or a leftover.</summary>
    private void Walk(MVarId g)
    {
        _m.Budget.Tick();
        var target = _m.InstantiateMVars(_m.GetMVarType(g));
        if (!target.HeadIs(TripleName) || target.GetAppArgs() is not { Length: 7 } args)
        {
            Unsupported(g, null);
            return;
        }
        var (prog, node) = Normalize(args[4]);
        _lastNode = node ?? _lastNode;
        if (prog != args[4])
        {
            args[4] = prog;
            g = _m.ReplaceTargetDefEq(g, ExprOps.MkApp(target.GetAppFn(), args));
        }
        Step(g, prog, node);
    }

    private void Step(MVarId g, Expr prog, int? node)
    {
        var a = prog.GetAppArgs();
        var head = prog.GetAppFn() as ConstExpr;
        switch (head?.Name)
        {
            case var n when n == BindName && a.Length == 6:
                Each(Rule(g, () => _m.ApplyConst(g, SpecTable.Bind)), g, node, Walk);
                return;
            case var n when n == PureName && a.Length == 4:
                if (CalleeContract(node, a[3]) is { } pureCallee && SigmaOf(a[0]) is { } sigma)
                {
                    Call(g, pureCallee, [sigma, .. a[3].GetAppArgs()], node, pure: true);
                    return;
                }
                Each(Rule(g, () => _m.ApplyConst(g, SpecTable.Pure)), g, node, h => Leaf(h, null));
                return;
            case var n when n == IteName && a.Length == 5:
                if (NodeAt(node) is AssertStmt assert)
                {
                    Assert(g, assert, node);
                    return;
                }
                Each(Rule(g, () => _m.ApplyConst(g, SpecTable.Ite)), g, node, Branch);
                return;
            case var n when n == DiteName && a.Length == 5:
                Each(Rule(g, () => _m.ApplyConst(g, SpecTable.Dite)), g, node, Branch);
                return;
            case var n when n == ThrowName && a.Length == 3:
                Throw(g, a[2], node);
                return;
            case var n when n == OptionRecName && a.Length == 5:
                Each(Rule(g, () => _m.ApplyConst(g, SpecTable.OptionRec)), g, node, Branch);
                return;
            case { } n when _models.TryGetValue(n, out var lemma):
                Each(Rule(g, () => Spec(g, lemma)), g, node, h => Leaf(h, node));
                return;
            case { } n when _m.Env.Find(n) is RecursorInfo rec:
                Recursor(g, prog, rec, node);
                return;
            case { } n when CalleeContract(node, prog) is { } callee:
                Call(g, callee, a, node);
                return;
            case null when prog.GetAppFn() is FVarExpr op && _operations.TryGetValue(op.Id, out var external):
                External(g, external.Hypothesis, external.Member, a, node);
                return;
            default:
                Unsupported(g, node);
                return;
        }
    }

    /// <summary>A goal no rule covers, a leftover at its node, or where the walk last was when it has none (#223).</summary>
    private void Unsupported(MVarId g, int? node) => Leftovers.Add(new(g, VcKind.Unsupported, node ?? _lastNode));

    /// <summary>
    /// <paramref name="e"/> with the steps the next rule needs taken: a site's metadata read and removed, <c>let</c>s
    /// substituted (a join point among them) and β-redexes reduced.
    /// </summary>
    private (Expr Program, int? Node) Normalize(Expr e)
    {
        int? node = null;
        e = _m.InstantiateMVars(e);
        while (true)
        {
            switch (e)
            {
                case MDataExpr md:
                    node ??= NodeOf(md);
                    e = md.Expr;
                    continue;
                case LetExpr l:
                    e = ExprOps.Instantiate(l.Body, l.Value);
                    continue;
                case AppExpr when e.GetAppFn() is LamExpr:
                    e = ExprOps.HeadBetaReduce(e);
                    continue;
                case AppExpr when e.GetAppFn() is MDataExpr fn:
                    e = ExprOps.MkApp(fn.Expr, e.GetAppArgs());
                    continue;
                default:
                    return (e, node);
            }
        }
    }

    private static int? NodeOf(MDataExpr md) =>
        md.Data.Entries.FirstOrDefault(e => e.Key == ContractObligation.SiteKey) is { } entry
        && int.TryParse(entry.Value, NumberStyles.None, CultureInfo.InvariantCulture, out var id) ? id : null;

    /// <summary><paramref name="e"/> without the walker's site metadata, which no proof keeps.</summary>
    public static Expr Strip(Expr e) =>
        ExprOps.Replace(e, (x, _) => x is MDataExpr md && NodeOf(md) is not null ? Strip(md.Expr) : null);

    private VirNode? NodeAt(int? node) => node is { } id && id >= 0 && id < _nodes.Count ? _nodes[id] : null;

    /// <summary>
    /// Applies a rule; null when it does not apply, with the Meta state as it was, so the goal becomes a leftover rather
    /// than an exception (KTD13).
    /// </summary>
    private IReadOnlyList<MVarId>? Rule(MVarId g, Func<IReadOnlyList<MVarId>> apply)
    {
        var saved = _m.SaveState();
        try
        {
            return [.. apply().Where(x => !_m.IsAssigned(x))];
        }
        catch (MetaException ex) when (ex is not MetaResourceException)
        {
            _m.Restore(saved);
            return null;
        }
    }

    /// <summary>Continues on each goal a rule left, or leaves <paramref name="g"/> when the rule did not apply.</summary>
    private void Each(IReadOnlyList<MVarId>? goals, MVarId g, int? node, Action<MVarId> next)
    {
        if (goals is null)
        {
            Unsupported(g, node);
            return;
        }
        foreach (var goal in goals)
        {
            next(goal);
        }
    }

    /// <summary>A branch's goal <c>∀ h, ⦃⌜True⌝⦄ x ⦃Q⦄</c>: its hypotheses introduced as path conditions, then the walk.</summary>
    private void Branch(MVarId g)
    {
        while (_m.InstantiateMVars(_m.GetMVarType(g)) is ForallExpr f)
        {
            g = _m.Intro1(g, Hypothesis(f.BinderName)).Goal;
        }
        Walk(g);
    }

    /// <summary>A model operation (KTD15): <c>Vc.spec</c> with its <c>@[spec]</c> lemma, leaving its precondition at every world.</summary>
    private IReadOnlyList<MVarId> Spec(MVarId g, Name lemma)
    {
        var goals = _m.ApplyConst(g, SpecTable.Spec);
        var triple = goals.Single(x => !_m.IsAssigned(x) && _m.InstantiateMVars(_m.GetMVarType(x)).HeadIs(TripleName));
        if (_m.ApplyConst(triple, lemma).Any(x => !_m.IsAssigned(x)))
        {
            throw Failed(triple, $"the spec lemma {lemma} left goals");
        }
        return goals;
    }

    /// <summary>
    /// <c>Spec.Assert(c)</c>'s check (KTD16): <c>c</c> is a VC at the <c>Spec.Assert</c>, proved by its script when it has
    /// one, and the rest is walked knowing <c>c</c>.
    /// </summary>
    private void Assert(MVarId g, AssertStmt assert, int? node)
    {
        if (Rule(g, () => _m.ApplyConst(g, SpecTable.Assert)) is not [var fact, var rest])
        {
            Unsupported(g, node);
            return;
        }
        if (assert.Script.Count == 0)
        {
            Leftovers.Add(new(fact, VcKind.Assert, node));
        }
        else
        {
            var runner = new TacticRunner(new TacticM(_m, [fact]));
            var saved = _m.SaveState();
            try
            {
                foreach (var tactic in assert.Script)
                {
                    runner.Run(tactic);
                }
                if (runner.State.GetUnsolvedGoals() is { IsEmpty: false } unsolved)
                {
                    Leftovers.Add(new(unsolved[0], VcKind.Assert, node, "the Spec.Assert's script left unsolved goals"));
                }
            }
            catch (Exception ex) when (ex is (MetaException and not MetaResourceException) or TacticUnavailableException)
            {
                _m.Restore(saved);
                Leftovers.Add(new(fact, VcKind.Assert, node, $"the Spec.Assert's script failed: {ex.Message}"));
            }
        }
        Branch(rest);
    }

    /// <summary>
    /// An explicit <c>throw</c>, or an exception the walker raises itself: the exception postcondition at <c>e</c>. An
    /// allowed exception (KTD12) is first tried for an unreachable path (#92), and is a <see cref="VcThrow"/> when it is not
    /// shown so; any other is a VC. Under <c>Spec.NoThrow</c> an explicit throw not shown unreachable is a VC too (#182).
    /// </summary>
    private void Throw(MVarId g, Expr e, int? node)
    {
        if (Rule(g, () => _m.ApplyConst(g, SpecTable.Throw)) is not [var h])
        {
            Unsupported(g, node);
            return;
        }
        e = Strip(_m.InstantiateMVars(e));
        var ctor = (e.GetAppFn() as ConstExpr)?.Name;
        if (ctor is null || (ctor != ClrExnNames.Thrown && ctor != ClrExnNames.ExternalException))
        {
            Leaf(h, node);
            return;
        }
        var g1 = _m.Intro1(h, S).Goal;
        if (Unreachable(g1))
        {
            return;
        }
        if (_noThrow && ctor == ClrExnNames.Thrown)
        {
            // ClrExn.External (thrown T) is False: the VC is that the path conditions are contradictory, stated without
            // the world, so the failure shows only them.
            if (_m.SimpTarget(g1, VcSimpSet.Context(_m)) is { } reachable)
            {
                Leftovers.Add(new(reachable, VcKind.ReachableThrow, node));
            }
            return;
        }
        Throws.Add(new(node, e.GetAppArgs() is [StrLitExpr key] ? key.Value : "external"));
        if (_m.SimpTarget(g1, VcSimpSet.Context(_m)) is { } rest)
        {
            Unsupported(rest, node);
        }
    }

    /// <summary>Whether the goal's path conditions are contradictory, which omega shows; the goal is closed when they are.</summary>
    private bool Unreachable(MVarId g)
    {
        var saved = _m.SaveState();
        try
        {
            foreach (var goal in _m.ApplyConst(g, SpecTable.FalseElim).Where(x => !_m.IsAssigned(x)))
            {
                Discharge(goal, VcSimpSet.Context(_m));
            }
            return true;
        }
        catch (MetaException ex) when (ex is not MetaResourceException)
        {
            _m.Restore(saved);
            return false;
        }
    }

    /// <summary>
    /// A verified callee whose contract is proved (KTD12): <c>Vc.call</c> with <c>f.$contract σ args</c>; its
    /// <c>Requires</c> is a VC at the call, and the rest is walked with its <c>Ensures</c> as a hypothesis.
    /// </summary>
    private void Call(MVarId g, Name contract, Expr[] args, int? node, bool pure = false)
    {
        // A callee with Spec.NoThrow states ClrExn.External as its exception postcondition (#182).
        bool external = _m.Env.Find(contract)?.Type is { } type
            && ExprOps.Find(type, (x, _) => x is ConstExpr { Name: var n } && n == ClrExnNames.External) is not null;
        var rule = pure && _noThrow ? SpecTable.CallPure : external ? SpecTable.CallExternal : SpecTable.Call;
        Consequence(g, rule, ExprOps.MkApp(Expr.Const(contract), args), contract.ToString(), VcKind.CalleePrecondition, node, () =>
        {
            if (NodeAt(node) is CallExpr site)
            {
                Calls.Add((site.Target, node));
            }
        });
    }

    /// <summary>
    /// A call to a dependency member (M6 U20, KTD9, design D9): <c>Vc.call</c> with the member's contract hypothesis at the
    /// call's arguments, which holds at every world, so at the current one (KTD4); its <c>Requires</c> is a VC at the call,
    /// the rest is walked with its <c>Ensures</c> as a hypothesis, and an exception from it is one the contract allows,
    /// propagated from the dependency (KTD12, KTD20).
    /// </summary>
    private void External(MVarId g, FVarExpr hypothesis, string member, Expr[] args, int? node) =>
        // Under Spec.NoThrow the hypothesis states ClrExn.External as its exception postcondition, as the method does (#182).
        Consequence(g, _noThrow ? SpecTable.CallExternal : SpecTable.Call, ExprOps.MkApp(hypothesis, args), member, VcKind.DependencyPrecondition, node, () => ExternalCalls.Add((member, node)));

    /// <summary>
    /// <c>Vc.call</c>, the consequence rule, with <paramref name="triple"/>, a proof of the call's triple: its precondition
    /// is a VC of kind <paramref name="pre"/> at <paramref name="node"/>, <paramref name="used"/> records the contract, the
    /// rest is walked knowing its postcondition, and an exception it allows is allowed in the caller's contract too.
    /// <paramref name="rule"/> is <c>Vc.call</c>, <c>Vc.callExternal</c> for a contract with <c>Spec.NoThrow</c>, or
    /// <c>Vc.callPure</c> for a pure callee under a caller's <c>Spec.NoThrow</c>, which needs nothing of its exceptions
    /// (#182) and so leaves no exception goal.
    /// </summary>
    private void Consequence(MVarId g, Name rule, Expr triple, string what, VcKind pre, int? node, Action used)
    {
        var goals = Rule(g, () =>
        {
            var gs = _m.ApplyConst(g, rule);
            var hx = gs.First(x => !_m.IsAssigned(x) && _m.InstantiateMVars(_m.GetMVarType(x)).HeadIs(TripleName));
            if (_m.Apply(hx, triple, what).Any(x => !_m.IsAssigned(x)))
            {
                throw Failed(hx, $"the contract of {what} does not state this call's triple");
            }
            return gs;
        });
        if (rule == SpecTable.CallPure && goals is [var p, var o])
        {
            Leftovers.Add(new(p, pre, node));
            used();
            Leaf(o, null);
            return;
        }
        if (goals is not [var precondition, var ok, var raised])
        {
            Unsupported(g, node);
            return;
        }
        Leftovers.Add(new(precondition, pre, node));
        used();
        Leaf(ok, null);
        // An exception the callee may raise is allowed in the caller's contract too: the caller's postcondition has the same
        // exception half (KTD12), or a wider one than a NoThrow callee's (ClrExn.allowed_of_external, #182).
        var (_, rest) = _m.IntroN(raised, 3, [Name.From("e"), H, S]);
        if (_m.SimpTarget(rest, _light) is not { } allowed)
        {
            return;
        }
        var saved = _m.SaveState();
        try
        {
            _m.Assumption(allowed);
            return;
        }
        catch (MetaException ex) when (ex is not MetaResourceException)
        {
            _m.Restore(saved);
        }
        try
        {
            foreach (var h in _m.ApplyConst(allowed, SpecTable.AllowedOfExternal).Where(x => !_m.IsAssigned(x)))
            {
                _m.Assumption(h);
            }
            return;
        }
        catch (MetaException ex) when (ex is not MetaResourceException)
        {
            _m.Restore(saved);
        }
        if (_noThrow)
        {
            // The callee's contract allows an explicit throw, which this method's does not.
            Leftovers.Add(new(allowed, VcKind.CalleeMayThrow, node,
                $"the contract of {what} allows an explicit throw, which this method's Spec.NoThrow does not; give the callee Spec.NoThrow too"));
            return;
        }
        Unsupported(allowed, node);
    }

    /// <summary>
    /// The contract a call site uses: that of the verified callee the site's node names, when it is admitted; null for
    /// anything else, such as the pure unit under proof.
    /// </summary>
    private Name? CalleeContract(int? node, Expr value)
    {
        if (value.GetAppFn() is not ConstExpr { Name: var callee } || callee == _self)
        {
            return null;
        }
        // Only a call the translation marks as one (a raising callee, or one with Spec.Requires): a pure callee's value is
        // known through its $contract_spec in the leftover VCs instead (#173).
        return NodeAt(node) is CallExpr call && LeanNames.Contract(call.Target) is var contract && contract == callee.Append(LeanNames.ContractComponent)
            && _m.Env.Find(contract) is not null
            ? contract
            : null;
    }

    /// <summary>The world <c>σ</c> of a monad <c>ClrM σ</c>.</summary>
    private static Expr? SigmaOf(Expr monad) => monad.GetAppArgs() is [var sigma] ? sigma : null;

    /// <summary>
    /// A closed type's recursor (a <c>switch</c>, M4 KTD9): reduced when its discriminant is a constructor, split with
    /// <c>Cases</c> when it is a variable, and a leftover otherwise.
    /// </summary>
    private void Recursor(MVarId g, Expr prog, RecursorInfo rec, int? node)
    {
        var major = prog.GetAppArgs()[^1];
        if (major.GetAppFn() is ConstExpr c && _m.Env.Find(c.Name) is ConstructorInfo)
        {
            var reduced = _m.WhnfCore(prog);
            if (reduced != prog)
            {
                var target = _m.InstantiateMVars(_m.GetMVarType(g));
                var args = target.GetAppArgs();
                args[4] = reduced;
                Walk(_m.ReplaceTargetDefEq(g, ExprOps.MkApp(target.GetAppFn(), args)));
                return;
            }
        }
        if (major is FVarExpr fv && prog.GetAppNumArgs() == rec.NumParams + rec.NumMotives + rec.NumMinors + rec.NumIndices + 1)
        {
            var saved = _m.SaveState();
            IReadOnlyList<CasesSubgoal> cases;
            try
            {
                cases = _m.Cases(g, fv.Id);
            }
            catch (MetaException ex) when (ex is not MetaResourceException)
            {
                _m.Restore(saved);
                Unsupported(g, node);
                return;
            }
            foreach (var c1 in cases)
            {
                Walk(c1.MVarId);
            }
            return;
        }
        Unsupported(g, node);
    }

    /// <summary>
    /// A rule's premise at every world: its binders and implications introduced as path conditions, its conjunctions split,
    /// and each part either the rest of the program, <c>wp⟦k⟧ Q s</c>, walked on through <c>Vc.resume</c>, or a VC. A VC
    /// about an exception the contract excludes has the kind of that exception at <paramref name="site"/>; any other is the
    /// walker's default, the postcondition.
    /// </summary>
    private void Leaf(MVarId g, int? site)
    {
        bool reduced = false;
        while (true)
        {
            var target = _m.InstantiateMVars(_m.GetMVarType(g));
            if (target is ForallExpr f)
            {
                g = _m.Intro1(g, Hypothesis(f.BinderName)).Goal;
                reduced = false;
                continue;
            }
            if (!reduced)
            {
                if (_m.SimpTarget(g, _light) is not { } next)
                {
                    return;
                }
                g = next;
                reduced = true;
                continue;
            }
            if (target.HeadIs(AndName) && target.GetAppNumArgs() == 2)
            {
                Each(Rule(g, () => _m.ApplyConst(g, SpecTable.AndIntro)), g, site, x => Leaf(x, site));
                return;
            }
            if (target.HeadIs(ULiftDown) && target.GetAppArgs() is { Length: > 0 } down && down[^1].HeadIs(PredTransApply))
            {
                Each(Rule(g, () => _m.ApplyConst(g, SpecTable.Resume)), g, site, Walk);
                return;
            }
            var exception = Exception(target);
            var (kind, node) = exception switch
            {
                null => (_kind, _node),
                _ when exception == ClrExnNames.Overflow => (VcKind.Overflow, site),
                _ when exception == ClrExnNames.DivideByZero => (VcKind.DivisionByZero, site),
                _ when exception == ClrExnNames.InvalidOperation => (VcKind.NullRead, site),
                _ when exception == ClrExnNames.NullReference => (NullKind(site), site),
                // A default-context operation's model fails as a Spec.Assert does where the CLR would wrap (#244).
                _ when exception == ClrExnNames.AssertFailed => (NodeAt(site) is BinaryExpr or UnaryExpr ? VcKind.ArithmeticOverflow : VcKind.Assert, site),
                _ => (VcKind.Unsupported, site ?? _lastNode),
            };
            Leftovers.Add(new(g, IsOperation(_kind) ? _kind : kind, IsOperation(_kind) ? _node : node));
            return;
        }
    }

    /// <summary>
    /// The <c>ClrExn</c> constructor a goal <c>ClrExn.Allowed e</c>, or <c>ClrExn.External e</c> under <c>Spec.NoThrow</c>
    /// (#182), names (one of <see cref="ClrExnNames.Constructors"/>, a name under <see cref="ClrExnNames.Type"/>); null when
    /// the goal is not one.
    /// </summary>
    private static Name? Exception(Expr target)
    {
        Name? found = null;
        ExprOps.Replace(target, (x, _) =>
        {
            if (found is null && (x.HeadIs(ClrExnNames.Allowed) || x.HeadIs(ClrExnNames.External)) && x.GetAppArgs() is [var e] && e.GetAppFn() is ConstExpr c && c.Name.Prefix == ClrExnNames.Type)
            {
                found = c.Name;
            }
            return null;
        });
        return found;
    }

    /// <summary>
    /// A null reference (#163): a member access through a nullable value is a null read; any other use of it where a
    /// non-null value is required, such as a call argument, passes null.
    /// </summary>
    private VcKind NullKind(int? site) =>
        NodeAt(site) is UnwrapExpr u && _parents.TryGetValue(u, out var parent) && parent is GetExpr get && ReferenceEquals(get.Target, u)
            ? VcKind.NullRead
            : VcKind.NullPassed;

    // ------------------------------------------------------------------ leftovers

    /// <summary>
    /// A leftover readied for the VC simp set and omega (#173): the pure unit under proof unfolded in its postcondition,
    /// and for each application of a pure verified callee with <c>Spec.Ensures</c>, its <c>f.$contract_spec</c> at those
    /// arguments as a hypothesis, since nothing else brings a pure callee's <c>Ensures</c> into scope.
    /// </summary>
    public MVarId Prepare(VcLeftover leftover)
    {
        var g = Tidy(leftover.Goal);
        if (_self is { } self && leftover.Kind == VcKind.Postcondition)
        {
            var saved = _m.SaveState();
            try
            {
                g = _m.UnfoldTarget(g, self);
            }
            catch (MetaException ex) when (ex is not MetaResourceException)
            {
                _m.Restore(saved);
            }
        }
        var facts = new List<(Name, Expr, Expr)>();
        var seen = new HashSet<Expr>();
        _m.WithContext(g, () =>
        {
            var terms = (_m.MCtx.FindDecl(g)?.LCtx.Decls ?? []).Select(d => d.Type).Append(_m.GetMVarType(g));
            foreach (var term in terms)
            {
                ExprOps.Replace(_m.InstantiateMVars(term), (x, _) =>
                {
                    if (x.GetAppFn() is ConstExpr { Name: var callee } && callee != _self
                        && _m.Env.Find(callee.Append("$contract_spec")) is { } spec
                        && _m.Env.Find(callee) is DefinitionInfo definition
                        && Arity(definition.Type) == x.GetAppNumArgs()
                        && !x.HasLooseBVars
                        && seen.Add(x))
                    {
                        var value = ExprOps.MkApp(Expr.Const(spec.Name), x.GetAppArgs());
                        facts.Add((Name.From("hspec"), _m.InferType(value), value));
                        PureCallees.Add(callee);
                    }
                    return null;
                });
            }
            return 0;
        });
        return facts.Count == 0 ? g : _m.AssertHypotheses(g, facts).Goal;
    }

    /// <summary>
    /// The goal without what states nothing about the path: a <c>True</c> precondition, and the world <c>s</c> and its type
    /// <c>σ</c> when nothing mentions them, so a failure shows its path conditions and goal only.
    /// </summary>
    private MVarId Tidy(MVarId g)
    {
        var decls = (_m.MCtx.FindDecl(g)?.LCtx.Decls ?? []).Where(d => !d.IsImplementationDetail).Reverse().ToList();
        foreach (var d in decls)
        {
            var type = _m.InstantiateMVars(d.Type);
            if (type.HeadIs(TrueName) && type.GetAppNumArgs() == 0 || d.UserName == S || d.UserName == Sigma)
            {
                g = _m.TryClear(g, d.FVarId);
            }
        }
        return g;
    }

    private static int Arity(Expr type)
    {
        int n = 0;
        while (type is ForallExpr f)
        {
            n++;
            type = f.Body;
        }
        return n;
    }

    /// <summary>
    /// The default procedure's last steps (KTD14): each leftover readied, then the VC simp set, then omega. Every one that
    /// is not proved is a <see cref="VcFailure"/>, with its goal after the VC simp set.
    /// </summary>
    public List<VcFailure> Close(Func<MVarId, string> print)
    {
        var failures = new List<VcFailure>();
        var simp = VcSimpSet.Context(_m);
        foreach (var leftover in Leftovers)
        {
            if (leftover.Failure is { } failure)
            {
                failures.Add(new(leftover.Kind, leftover.Node, $"{VcKinds.Text(leftover.Kind)}: {failure}", print(leftover.Goal)));
                continue;
            }
            var g = Prepare(leftover);
            try
            {
                Discharge(g, simp);
            }
            catch (MetaException ex) when (ex is not MetaResourceException)
            {
                // omega names the goal it was given: the VC after the VC simp set.
                var shown = ex is TacticException { Goal: { } r } && _m.MCtx.FindDecl(r) is not null ? r : g;
                failures.Add(new(leftover.Kind, leftover.Node, $"{VcKinds.Text(leftover.Kind)}: {FirstLine(ex.Message)}", print(shown)));
            }
        }
        return failures;
    }

    /// <summary>
    /// The VC simp set at the goal and every hypothesis, each rewriting the others (Lean's <c>simp_all</c>), so a path
    /// condition such as <c>p = none</c> meets the guard <c>¬p.isNone</c>; then omega. Throws when they do not prove it.
    /// </summary>
    /// <returns>The goal omega was given, or null when simp closed it.</returns>
    private MVarId? Discharge(MVarId g, SimpContext simp)
    {
        if (_m.SimpAll(g, simp) is not { } rest)
        {
            return null;
        }
        if (Substitute(rest.Goal, simp) is not { } substituted)
        {
            return null;
        }
        // Two reads of one nullable value are two cases of it, `r = some v₁` and `r = some v₂`, which substitution turns
        // into `some v₁ = some v₂`; `v₁ = v₂` then makes a fact about v₁ one about v₂ (#226).
        for (int round = 0; round < 4 && Inject(substituted) is (var injected, { Length: > 0 } values); round++)
        {
            if (Substitute(injected, simp, values) is not { } again)
            {
                return null;
            }
            substituted = again;
        }
        _m.OmegaTactic(substituted);
        return substituted;
    }

    /// <summary>
    /// Each path condition <c>x = e</c> about a variable rewrites the other hypotheses and the goal (as Lean's
    /// <c>simp_all</c> uses its hypotheses), so a model operation's case <c>p = none</c> meets the branch's guard on
    /// <c>p</c>. Null when that closes the goal.
    /// </summary>
    // `only`: the equations to rewrite with, when given; then they rewrite every other hypothesis, the path conditions
    // that are equations among them (#226).
    private MVarId? Substitute(MVarId g, SimpContext simp, FVarId[]? only = null) => _m.WithContext(g, () =>
    {
        var decls = (_m.MCtx.FindDecl(g)?.LCtx.Decls ?? []).Where(d => !d.IsImplementationDetail).ToList();
        var equations = only is not null
            ? decls.Where(d => only.Contains(d.FVarId)).ToList()
            : decls.Where(d => _m.InstantiateMVars(d.Type) is var t && t.HeadIs(EqName) && t.GetAppArgs() is [_, var x, var rhs]
                && IsAtom(x) && ExprOps.Find(rhs, (y, _) => y == x) is null).ToList();
        if (equations.Count == 0)
        {
            return g;
        }
        var theorems = new SimpTheorems();
        foreach (var eq in equations)
        {
            theorems.AddRange(_m.MkSimpTheoremsFromProof(eq.ToExpr()));
        }
        var others = decls.Where(d => !equations.Contains(d) && _m.IsProp(d.Type)).Select(d => d.FVarId).ToList();
        var context = simp with { Theorems = simp.Theorems.Insert(0, theorems) };
        return _m.SimpGoal(g, context, simplifyTarget: true, others)?.Goal;
    });

    /// <summary>
    /// For each hypothesis <c>h : some a = some b</c> not yet injected, the hypothesis <c>a = b</c>, proved by
    /// <c>congrArg (fun o =&gt; Nullable.coalesce o a) h</c>, whose type <c>coalesce (some a) a = coalesce (some b) a</c> is
    /// <c>a = b</c> by computation (#226), with the new hypotheses. The kernel checks the term.
    /// </summary>
    private (MVarId Goal, FVarId[] Values) Inject(MVarId g) => _m.WithContext(g, () =>
    {
        var decls = (_m.MCtx.FindDecl(g)?.LCtx.Decls ?? []).Where(d => !d.IsImplementationDetail).ToList();
        var known = decls.Select(d => _m.InstantiateMVars(d.Type)).ToHashSet();
        var facts = new List<(Name, Expr, Expr)>();
        foreach (var d in decls)
        {
            if (_m.InstantiateMVars(d.Type) is var t && t.HeadIs(EqName) && t.GetAppArgs() is [_, var lhs, var rhs]
                && lhs.HeadIs(OptionSomeName) && rhs.HeadIs(OptionSomeName)
                && lhs.GetAppArgs() is [var type, var a] && rhs.GetAppArgs() is [_, var b] && a != b)
            {
                var equation = Expr.App(Expr.Const(EqName, Level.One), type, a, b);
                if (!known.Add(equation))
                {
                    continue;
                }
                var option = Expr.App(Expr.Const(OptionName, Level.Zero), type);
                var read = Expr.Lam(Name.From("o"), option, Expr.App(Expr.Const(CoalesceName), type, Expr.BVar(0), a));
                var proof = Expr.App(Expr.Const(CongrArgName, Level.One, Level.One), option, type, lhs, rhs, read, d.ToExpr());
                facts.Add((H, equation, proof));
            }
        }
        if (facts.Count == 0)
        {
            return (g, Array.Empty<FVarId>());
        }
        var (values, goal) = _m.AssertHypotheses(g, facts);
        return (goal, values);
    });

    private static readonly Name OptionName = Name.Parse("Option");
    private static readonly Name OptionSomeName = Name.Parse("Option.some");
    private static readonly Name CoalesceName = Name.Parse("Warrant.Nullable.coalesce");
    private static readonly Name CongrArgName = Name.Parse("congrArg");

    /// <summary>
    /// What a path condition <c>x = e</c> may rewrite: a variable, or a field of one (<c>refund.Days = none</c>, a null test
    /// of a record's nullable field, #218).
    /// </summary>
    private static bool IsAtom(Expr e) => e is FVarExpr || (e is ProjExpr p && IsAtom(p.Struct));

    private static string FirstLine(string text) => text.IndexOf('\n', StringComparison.Ordinal) is var i and >= 0 ? text[..i] : text;
}

/// <summary>Term tests the walker reads programs with.</summary>
internal static class VcExprs
{
    /// <summary>Lean's <c>isAppOf</c>: the head is the constant <paramref name="name"/>.</summary>
    public static bool HeadIs(this Expr e, Name name) => e.GetAppFn() is ConstExpr c && c.Name == name;
}
