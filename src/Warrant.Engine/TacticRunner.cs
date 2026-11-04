using Warrant.Cic;
using Warrant.Meta;
using Warrant.Semantics;
using Warrant.Vir;

namespace Warrant.Engine;

/// <summary>
/// Runs a theorem's VIR proof script as <see cref="TacticM"/> calls (M5a KTD6, KTD18). Each tactic is looked up by its
/// Lean name in <see cref="Tactics"/>; a later unit adds a tactic by adding its entry. A name with no entry fails the
/// script with "Tactic `x` is not available yet", which no <c>try</c> hides.
/// </summary>
internal sealed class TacticRunner(TacticM tactics, EngineUnit unit)
{
    /// <summary>A tactic's implementation: runs <paramref name="node"/> on <paramref name="runner"/>'s goals.</summary>
    private delegate void Handler(TacticRunner runner, TacticNode node);

    /// <summary>The tactics this engine runs, by the name VIR gives them (Lean's).</summary>
    private static readonly Dictionary<string, Handler> Tactics = new(StringComparer.Ordinal)
    {
        ["intro"] = Intro,
        ["exact"] = Exact,
        ["apply"] = Apply,
        ["unfold"] = Unfold,
        ["cases"] = Cases,
        ["induction"] = Induction,
        ["simp"] = Simp,
        ["all_goals"] = AllGoals,
        ["try"] = Try,
    };

    /// <summary>The tactic state.</summary>
    public TacticM State => tactics;

    /// <summary>
    /// The innermost tactic whose failure is propagating, for the diagnostic's location; cleared when a <c>try</c>
    /// recovers from it.
    /// </summary>
    public TacticNode? FailedAt { get; private set; }

    /// <summary>Runs one tactic and drops the goals it solved.</summary>
    /// <exception cref="MetaException">The tactic failed; <see cref="FailedAt"/> says which.</exception>
    /// <exception cref="TacticUnavailableException">The tactic is not implemented yet.</exception>
    public void Run(TacticNode node)
    {
        tactics.Step();
        if (!Tactics.TryGetValue(node.Name, out var handler))
        {
            FailedAt ??= node;
            throw new TacticUnavailableException(node.Name, $"Tactic `{node.Name}` is not available yet");
        }
        try
        {
            handler(this, node);
        }
        catch (Exception ex) when (ex is MetaException or TacticUnavailableException)
        {
            FailedAt ??= node;
            throw;
        }
        tactics.PruneSolvedGoals();
    }

    // ---- The tactics ----

    /// <summary><c>Tactic.Intro(names)</c>: one binder per name, or one binder under its own name when there is none.</summary>
    private static void Intro(TacticRunner r, TacticNode node)
    {
        var names = node.Args.OfType<StringArg>().Select(a => Name.From(a.Value)).ToList();
        r.State.LiftMetaTactic1(g => r.State.Meta.IntroN(g, Math.Max(1, names.Count), names).Goal);
    }

    /// <summary><c>Tactic.Exact(h)</c>: a hypothesis by name, or a lemma by <c>nameof</c> or <c>Lean.Const</c>.</summary>
    private static void Exact(TacticRunner r, TacticNode node)
    {
        var arg = r.Single(node);
        var term = arg is StringArg h
            ? r.State.WithMainContext(() => (Expr)r.State.Meta.GetLocalDeclFromUserName(Name.From(h.Value)).ToExpr())
            : r.State.Meta.MkConstWithFreshMVarLevels(r.Constant(node, arg));
        r.State.Exact(term);
    }

    /// <summary><c>Tactic.Apply(c)</c>: a lemma by <c>nameof</c> or <c>Lean.Const</c>, or a hypothesis by name.</summary>
    private static void Apply(TacticRunner r, TacticNode node)
    {
        var arg = r.Single(node);
        var m = r.State.Meta;
        if (arg is StringArg h)
        {
            r.State.LiftMetaTactic(g => m.Apply(g, m.GetLocalDeclFromUserName(Name.From(h.Value)).ToExpr(), $"'{h.Value}'"));
        }
        else
        {
            var c = r.Constant(node, arg);
            r.State.LiftMetaTactic(g => m.ApplyConst(g, c));
        }
    }

    /// <summary>
    /// <c>Tactic.Unfold(f, …)</c>, each name in turn, for non-recursive definitions (delta expansion); a recursive one
    /// unfolds through its equation lemma, which needs simp's rewriting (chapter 5).
    /// </summary>
    private static void Unfold(TacticRunner r, TacticNode node)
    {
        foreach (var arg in node.Args.Where(a => a is not OptionArg))
        {
            var c = r.Constant(node, arg);
            if (r.State.Meta.Env.Find(c.Append("$eq_def")) is not null)
            {
                throw new TacticUnavailableException(node.Name, $"Tactic `unfold` is not available yet for the recursive definition `{r.State.Meta.PpConst(c)}`");
            }
            r.State.LiftMetaTactic1(g => r.State.Meta.UnfoldTarget(g, c));
        }
    }

    /// <summary><c>Tactic.Cases(x)</c>: one goal per constructor of the hypothesis <c>x</c>'s type, through <c>T.casesOn</c> (KTD8).</summary>
    private static void Cases(TacticRunner r, TacticNode node)
    {
        var m = r.State.Meta;
        r.State.LiftMetaTactic(g => [.. m.Cases(g, r.Hypothesis(node).FVarId).Select(s => s.MVarId)]);
    }

    /// <summary>
    /// <c>Tactic.Induction(x)</c>: <c>T.rec</c> on the hypothesis <c>x</c>, as Lean's <c>induction</c> does when the type has
    /// no custom eliminator (KTD6), which Warrant never has.
    /// </summary>
    private static void Induction(TacticRunner r, TacticNode node)
    {
        var m = r.State.Meta;
        r.State.LiftMetaTactic(g =>
        {
            var major = r.Hypothesis(node);
            // Lean's getElimNameInfo (Lean/Elab/Tactic/Induction.lean 817) takes T.rec and refuses mutual and nested types.
            if (m.WhnfD(major.Type).GetAppFn() is not ConstExpr { Name: var typeName } || m.Env.Find(typeName) is not InductiveInfo ival)
            {
                throw TacticException.Failed("induction", g, $"major premise type is not an inductive type\n  {m.Pp(major.Type)}");
            }
            var kind = ival.All.Count != 1 ? "mutually inductive" : ival.NumNested > 0 ? "a nested inductive type" : null;
            if (kind is not null)
            {
                throw new TacticException("induction", g, $"The `induction` tactic does not support the type `{m.PpConst(ival.Name)}` because it is {kind}");
            }
            var rec = ival.Name.Append("rec");
            return [.. m.Induction(g, major.FVarId, rec).Select(s => s.MVarId)];
        });
    }

    /// <summary>
    /// <c>Tactic.Simp(lemmas…)</c> with options from <c>.With(decide:, contextual:)</c>: Warrant's default simp set and
    /// configuration (plan Key Decisions, KTD11), the named lemmas added, on the goal's target.
    /// </summary>
    private static void Simp(TacticRunner r, TacticNode node)
    {
        var m = r.State.Meta;
        var config = SimpConfig.Default;
        foreach (var option in node.Args.OfType<OptionArg>())
        {
            config = (option.Name, option.Value) switch
            {
                ("decide", BoolArg b) => config with { Decide = b.Value },
                ("contextual", BoolArg b) => config with { Contextual = b.Value },
                _ => throw TacticException.Failed(node.Name, r.State.GetMainGoal(), $"unknown option '{option.Name}'"),
            };
        }
        var lemmas = node.Args.Where(a => a is not OptionArg).Select(a => r.Constant(node, a)).ToList();
        r.State.LiftMetaTactic(g =>
        {
            SimpTheorems? extra = null;
            if (lemmas.Count > 0)
            {
                extra = new SimpTheorems();
                foreach (var lemma in lemmas)
                {
                    try
                    {
                        extra.AddRange(m.MkSimpTheoremsFromConst(lemma));
                    }
                    catch (MetaException ex) when (ex is not MetaResourceException)
                    {
                        throw TacticException.Failed(node.Name, g, $"cannot use `{m.PpConst(lemma)}` as a simp lemma: {ex.Message}");
                    }
                }
            }
            return m.SimpGoal(g, DefaultSimpSet.Context(m, config, extra)) is { } result ? [result.Goal] : [];
        });
    }

    /// <summary><c>Tactic.AllGoals(t)</c>.</summary>
    private static void AllGoals(TacticRunner r, TacticNode node)
    {
        var nested = r.Nested(node);
        r.State.AllGoals(() => r.Run(nested));
    }

    /// <summary><c>Tactic.Try(t)</c>: a failure of <c>t</c> leaves the goals as they were; an unavailable tactic still fails.</summary>
    private static void Try(TacticRunner r, TacticNode node)
    {
        var nested = r.Nested(node);
        if (!r.State.Try(() => r.Run(nested)))
        {
            r.FailedAt = null;
        }
    }

    // ---- Arguments ----

    private VirTacticArg Single(TacticNode node)
    {
        var args = node.Args.Where(a => a is not OptionArg).ToList();
        return args.Count == 1 ? args[0] : throw TacticException.Failed(node.Name, tactics.GetMainGoal(), $"expected one argument, got {args.Count}");
    }

    /// <summary>The hypothesis a tactic's one string argument names, in the main goal's context (the U9 surface).</summary>
    private LocalDecl Hypothesis(TacticNode node) =>
        Single(node) is StringArg h
            ? tactics.WithMainContext(() => tactics.Meta.GetLocalDeclFromUserName(Name.From(h.Value)))
            : throw TacticException.Failed(node.Name, tactics.GetMainGoal(), "expected the name of a hypothesis");

    private TacticNode Nested(TacticNode node) =>
        Single(node) is TacticArg { Tactic: var nested } ? nested : throw TacticException.Failed(node.Name, tactics.GetMainGoal(), "expected a tactic");

    /// <summary>The constant a lemma argument names: a <c>nameof</c>'s unit, or a <c>Lean.Const</c>.</summary>
    private Name Constant(TacticNode node, VirTacticArg arg)
    {
        var name = arg switch
        {
            UnitRefArg u => LeanNames.ForKey(u.Key),
            LeanRefArg l => Cic.Name.Parse(l.Name),
            _ => throw TacticException.Failed(node.Name, tactics.GetMainGoal(), "expected a lemma"),
        };
        return tactics.Meta.Env.Find(name) is not null ? name : throw TacticException.Failed(node.Name, tactics.GetMainGoal(), $"unknown constant '{tactics.Meta.PpConst(name)}'");
    }

    /// <summary>The span of a tactic node, when the unit came with spans.</summary>
    public VirSpan? SpanOf(TacticNode node) =>
        unit.Spans is { } spans && VirTree.IdOf(unit.Unit, node) is { } id && spans.TryGetSpan(id, out var span) ? span : null;
}

/// <summary>A script names a tactic this engine does not implement yet (WRT0001, "Tactic `x` is not available yet").</summary>
internal sealed class TacticUnavailableException : Exception
{
    public TacticUnavailableException()
    {
    }

    public TacticUnavailableException(string message)
        : base(message)
    {
    }

    public TacticUnavailableException(string message, Exception innerException)
        : base(message, innerException)
    {
    }

    public TacticUnavailableException(string tactic, string message)
        : base(message)
    {
        Tactic = tactic;
    }

    /// <summary>The tactic's name.</summary>
    public string? Tactic { get; }
}
