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
/// check, a verified callee and a model operation each have a rule; a closed enum's recursor is split with <c>Cases</c>
/// when its discriminant is a variable; anything else is a leftover VC, never a guessed rule.</item>
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
    private static readonly Name AllowedName = Name.Parse("Warrant.ClrExn.Allowed");
    private static readonly Name ClrExnName = Name.Parse("Warrant.ClrExn");
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
    }

    /// <summary>The goals left to the VC simp set and omega, in the order the walk met them.</summary>
    public List<VcLeftover> Leftovers { get; } = [];

    /// <summary>The explicit throws the walk could not show unreachable (#92).</summary>
    public List<VcThrow> Throws { get; } = [];

    /// <summary>The verified callees whose contracts the walk used (KTD20), with the call's node.</summary>
    public List<(string Callee, int? Node)> Calls { get; } = [];

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
    /// definition), and the walk starts.
    /// </summary>
    public void Contract(MVarId goal, Expr? program, Name function, bool raising)
    {
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
            Leftovers.Add(new(g, VcKind.Unsupported, null));
            return;
        }
        var (prog, node) = Normalize(args[4]);
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
                    Call(g, pureCallee, [sigma, .. a[3].GetAppArgs()], node);
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
            default:
                Leftovers.Add(new(g, VcKind.Unsupported, node));
                return;
        }
    }

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
            Leftovers.Add(new(g, VcKind.Unsupported, node));
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
            Leftovers.Add(new(g, VcKind.Unsupported, node));
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
    /// shown so; any other is a VC.
    /// </summary>
    private void Throw(MVarId g, Expr e, int? node)
    {
        if (Rule(g, () => _m.ApplyConst(g, SpecTable.Throw)) is not [var h])
        {
            Leftovers.Add(new(g, VcKind.Unsupported, node));
            return;
        }
        e = Strip(_m.InstantiateMVars(e));
        var ctor = (e.GetAppFn() as ConstExpr)?.Name;
        if (ctor is null || ctor.ToString() is not ("Warrant.ClrExn.thrown" or "Warrant.ClrExn.external"))
        {
            Leaf(h, node);
            return;
        }
        var g1 = _m.Intro1(h, S).Goal;
        if (Unreachable(g1))
        {
            return;
        }
        Throws.Add(new(node, e.GetAppArgs() is [StrLitExpr key] ? key.Value : "external"));
        if (_m.SimpTarget(g1, VcSimpSet.Context(_m)) is { } rest)
        {
            Leftovers.Add(new(rest, VcKind.Unsupported, node));
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
    private void Call(MVarId g, Name contract, Expr[] args, int? node)
    {
        var goals = Rule(g, () =>
        {
            var gs = _m.ApplyConst(g, SpecTable.Call);
            var triple = gs.First(x => !_m.IsAssigned(x) && _m.InstantiateMVars(_m.GetMVarType(x)).HeadIs(TripleName));
            if (_m.Apply(triple, ExprOps.MkApp(Expr.Const(contract), args), contract.ToString()).Any(x => !_m.IsAssigned(x)))
            {
                throw Failed(triple, $"{contract} does not state this call's triple");
            }
            return gs;
        });
        if (goals is not [var pre, var ok, var raised])
        {
            Leftovers.Add(new(g, VcKind.Unsupported, node));
            return;
        }
        Leftovers.Add(new(pre, VcKind.CalleePrecondition, node));
        if (NodeAt(node) is CallExpr site)
        {
            Calls.Add((site.Target, node));
        }
        Leaf(ok, null);
        // An exception the callee may raise is allowed in the caller's contract too: the caller's postcondition has the same
        // exception half (KTD12).
        var (_, rest) = _m.IntroN(raised, 3, [Name.From("e"), H, S]);
        if (_m.SimpTarget(rest, _light) is { } allowed)
        {
            try
            {
                _m.Assumption(allowed);
            }
            catch (MetaException ex) when (ex is not MetaResourceException)
            {
                Leftovers.Add(new(allowed, VcKind.Unsupported, node));
            }
        }
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
                Leftovers.Add(new(g, VcKind.Unsupported, node));
                return;
            }
            foreach (var c1 in cases)
            {
                Walk(c1.MVarId);
            }
            return;
        }
        Leftovers.Add(new(g, VcKind.Unsupported, node));
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
            var (kind, node) = Exception(target) switch
            {
                null => (_kind, _node),
                "overflow" => (VcKind.Overflow, site),
                "divideByZero" => (VcKind.DivisionByZero, site),
                "invalidOperation" => (VcKind.NullRead, site),
                "nullReference" => (NullKind(site), site),
                "assertFailed" => (VcKind.Assert, site),
                _ => (VcKind.Unsupported, site),
            };
            Leftovers.Add(new(g, _kind == VcKind.WellDefinedness ? VcKind.WellDefinedness : kind, _kind == VcKind.WellDefinedness ? _node : node));
            return;
        }
    }

    /// <summary>The <c>ClrExn</c> constructor a goal <c>ClrExn.Allowed e</c> names, as its last name component; null when the goal is not one.</summary>
    private static string? Exception(Expr target)
    {
        string? found = null;
        ExprOps.Replace(target, (x, _) =>
        {
            if (found is null && x.HeadIs(AllowedName) && x.GetAppArgs() is [var e] && e.GetAppFn() is ConstExpr c && c.Name.Prefix == ClrExnName)
            {
                found = c.Name.ToString()[(ClrExnName.ToString().Length + 1)..];
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
        _m.OmegaTactic(substituted);
        return substituted;
    }

    /// <summary>
    /// Each path condition <c>x = e</c> about a variable rewrites the other hypotheses and the goal (as Lean's
    /// <c>simp_all</c> uses its hypotheses), so a model operation's case <c>p = none</c> meets the branch's guard on
    /// <c>p</c>. Null when that closes the goal.
    /// </summary>
    private MVarId? Substitute(MVarId g, SimpContext simp) => _m.WithContext(g, () =>
    {
        var decls = (_m.MCtx.FindDecl(g)?.LCtx.Decls ?? []).Where(d => !d.IsImplementationDetail).ToList();
        var equations = decls.Where(d => _m.InstantiateMVars(d.Type) is var t && t.HeadIs(EqName) && t.GetAppArgs() is [_, FVarExpr x, var rhs]
            && ExprOps.Find(rhs, (y, _) => y is FVarExpr f && f.Id == x.Id) is null).ToList();
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

    private static string FirstLine(string text) => text.IndexOf('\n', StringComparison.Ordinal) is var i and >= 0 ? text[..i] : text;
}

/// <summary>Term tests the walker reads programs with.</summary>
internal static class VcExprs
{
    /// <summary>Lean's <c>isAppOf</c>: the head is the constant <paramref name="name"/>.</summary>
    public static bool HeadIs(this Expr e, Name name) => e.GetAppFn() is ConstExpr c && c.Name == name;
}
