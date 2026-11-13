using System.Numerics;
using Warrant.Cic;
using Warrant.Kernel;
using Warrant.Meta.Omega;

namespace Warrant.Meta;

/// <summary>
/// What <c>Tactic.Omega()</c> tries when <c>omega</c> alone fails (#217, #237, #257): facts that are true in every case
/// and that <c>omega</c> cannot find itself, each one proved, so the step can only make a true goal provable. It runs only
/// after a failure, so a goal <c>omega</c> proves alone gets the same proof as before. Every nested proof it makes is a
/// plain <c>Tactic.Omega()</c> (the prep step and <c>omega</c>), never strengthened again, so the step costs a bounded
/// number of <c>omega</c> runs.
/// <list type="bullet">
/// <item>A product <c>x * y</c> of two integer terms, an atom to <c>omega</c>, gets the linear bounds that follow from
/// literal bounds on its factors (<c>Warrant.Int.mul_ge_of_ge_of_ge</c> and its siblings, McCormick's inequalities, #257),
/// each as an implication from the factor bounds, which <c>omega</c> itself discharges or drops. They are added first, so
/// the range proofs below can use them.</item>
/// <item>An <c>int</c> or <c>long</c> <c>+</c>, <c>-</c>, <c>*</c> or unary <c>-</c> whose exact result <c>omega</c> proves
/// in range has that exact value, by <c>Warrant.Int32.toInt_mul_of_range</c> and its siblings, instead of the
/// wrap-around's <c>Int.bmod</c>, whose case split <c>omega</c> cannot always close (#237).</item>
/// <item>A <c>decimal</c> literal's <c>units</c> is a closed integer, stated as <c>units (lit …) = n</c> and proved by
/// <c>rfl</c>: the kernel computes it (#217).</item>
/// </list>
/// </summary>
public sealed partial class MetaM
{
    /// <summary>
    /// How many terms of each kind the step looks at (operations for exact values, products, decimal literals), so a large
    /// goal does not run <c>omega</c> many times.
    /// </summary>
    private const int StrengthenLimit = 8;

    private static readonly Name DecimalUnits = Name.Parse("Warrant.Decimal.units");
    private static readonly Name DecimalLit = Name.Parse("Warrant.Decimal.lit");
    private static readonly Name Int32Name = Name.Parse("Int32");
    private static readonly Name Int64Name = Name.Parse("Int64");
    private static readonly Name IntInstLE = Name.Parse("Int.instLEInt");
    private static readonly Name[] ProductBounds =
    [
        Name.Parse("Warrant.Int.mul_ge_of_ge_of_ge"), Name.Parse("Warrant.Int.mul_ge_of_le_of_le"),
        Name.Parse("Warrant.Int.mul_le_of_ge_of_le"), Name.Parse("Warrant.Int.mul_le_of_le_of_ge"),
    ];

    /// <summary>
    /// <c>Tactic.Omega()</c> with the strengthening facts: an <c>if</c> over a product split on its condition, the product
    /// bounds before the omega-prep step, the in-range exact values in it, the decimal literal values after it (the prep
    /// step's <c>decide</c> would turn a literal's equation into <c>True</c>), then <c>omega</c>.
    /// </summary>
    /// <param name="mvarId">The goal.</param>
    private void OmegaStrengthened(MVarId mvarId)
    {
        // The goal's premises become hypotheses first, so a bound or range proof can use them.
        if (FalseOrByContra(mvarId) is not { } start)
        {
            return;
        }
        SplitIfs(start, MaxIfSplits);
    }

    /// <summary>How many <c>if</c>s over a product one goal is split on: at most 2^2 cases.</summary>
    private const int MaxIfSplits = 2;

    /// <summary>
    /// <c>if c then t else e</c> over a product (a pure method's <c>if (a &lt; 0) return 0; return a * b;</c>) is split on
    /// <c>c</c> by <c>dite</c>, and each case rewritten with <c>c</c> or <c>¬c</c>, so the product step sees the branch's
    /// condition as a fact, a bound on a factor; <c>omega</c> would split the <c>if</c> too, but inside its own search,
    /// where no bound can be read. Then <see cref="StrengthenedCase"/>.
    /// </summary>
    private void SplitIfs(MVarId g, int splits)
    {
        if (splits == 0 || IfOverProduct(g) is not var (c, instance))
        {
            StrengthenedCase(g);
            return;
        }
        var cases = WithContext(g, () =>
        {
            var target = this.InstantiateMVars(GetMVarType(g));
            var onTrue = MkFreshExprSyntheticOpaqueMVar(Expr.Forall(Name.From("h"), c, target));
            var onFalse = MkFreshExprSyntheticOpaqueMVar(Expr.Forall(Name.From("h"), Expr.App(Expr.Const(OmegaNames.Not), c), target));
            Assign(g, Expr.App(Expr.Const(DiteName, Level.Zero), target, c, instance, onTrue, onFalse));
            return new[] { onTrue.Id, onFalse.Id };
        });
        foreach (var branch in cases)
        {
            var (fvars, goal) = IntroN(branch, 1, [Name.From("h")]);
            var condition = new SimpTheorems();
            WithContext(goal, () => { condition.AddRange(MkSimpTheoremsFromProof(Expr.FVar(fvars[0]))); return 0; });
            var context = new SimpContext(SimpConfig.Default with { FailIfUnchanged = false }, [condition], SimpContext.CongrTheoremsOf(Attributes));
            var others = WithContext(goal, () => LCtx.Decls.Where(d => !d.IsImplementationDetail && d.FVarId != fvars[0] && IsProp(d.Type)).Select(d => d.FVarId).ToList());
            if (SimpGoal(goal, context, simplifyTarget: true, others) is { } rest)
            {
                SplitIfs(rest.Goal, splits - 1);
            }
        }
    }

    private static readonly Name DiteName = Name.Parse("dite");

    /// <summary>The condition and <c>Decidable</c> instance of an <c>if</c> whose branches mention <c>*</c>; null when none.</summary>
    private (Expr Condition, Expr Instance)? IfOverProduct(MVarId g)
    {
        foreach (var term in Terms(g))
        {
            var found = ExprOps.Find(term, (e, _) => OmegaExprs.AppOf(e, OmegaNames.Ite, 5) is [_, var c, _, var t, var f]
                && !c.HasLooseBVars && !c.HasExprMVar && c is not ConstExpr
                && (MentionsProduct(t) || MentionsProduct(f)));
            if (found is not null)
            {
                var args = found.GetAppArgs();
                return (args[1], args[2]);
            }
        }
        return null;

        static bool MentionsProduct(Expr e) => ExprOps.Find(e, (x, _) => x is ConstExpr { Name: var n } && n == OmegaNames.HMul) is not null;
    }

    /// <summary>One case of <see cref="SplitIfs"/>: the product bounds, the exact values, the prep step, the literals, <c>omega</c>.</summary>
    private void StrengthenedCase(MVarId start)
    {
        var g = ProductBoundFacts(start);
        var context = OmegaPrepSet.Context(this);
        if (ExactValues(g) is { } exact)
        {
            context = context with { Theorems = context.Theorems.Insert(0, exact) };
        }
        if (SimpAll(g, context) is not { } prepped)
        {
            return;
        }
        if (FalseOrByContra(prepped.Goal) is not { } contra)
        {
            return;
        }
        var last = DecimalLiteralFacts(contra);
        if (WithReducibleAndInstances(() => AssumptionCore(last)))
        {
            return;
        }
        Omega(last);
    }

    /// <summary>
    /// For each <c>units (lit s m e _ _)</c> with literal arguments, at most <see cref="StrengthenLimit"/> of them, the
    /// hypothesis <c>units (lit …) = n</c> by <c>rfl</c>.
    /// </summary>
    private MVarId DecimalLiteralFacts(MVarId g)
    {
        var facts = new List<(Name, Expr, Expr)>();
        var seen = new HashSet<Expr>();
        foreach (var term in Terms(g))
        {
            ExprOps.ForEach(term, (e, _) =>
            {
                if (facts.Count < StrengthenLimit
                    && OmegaExprs.AppOf(e, DecimalUnits, 1) is [var lit] && OmegaExprs.AppOf(lit, DecimalLit, 5) is [var sign, var m, var s, _, _]
                    && sign is ConstExpr { Name: var signName } && (signName == OmegaNames.BoolTrue || signName == OmegaNames.BoolFalse)
                    && NatLiteral(m) is { } mantissa && NatLiteral(s) is { } scale && scale <= 28 && !e.HasLooseBVars && seen.Add(e))
                {
                    var value = mantissa * BigInteger.Pow(10, 28 - (int)scale) * (signName == OmegaNames.BoolTrue ? -1 : 1);
                    facts.Add((Name.From("hlit"), OmegaExprs.MkEq(OmegaExprs.IntType, e, OmegaExprs.IntLit(value)),
                        Expr.App(Expr.Const(OmegaNames.EqRefl, Level.One), OmegaExprs.IntType, e)));
                    return false;
                }
                return true;
            });
        }
        return facts.Count == 0 ? g : AssertHypotheses(g, facts).Goal;

        static BigInteger? NatLiteral(Expr e) => e is NatLitExpr n ? n.Value : OmegaExprs.Nat(e);
    }

    /// <summary>
    /// For each <c>int</c>/<c>long</c> <c>a + b</c>, <c>a - b</c>, <c>a * b</c> or <c>-a</c> in the goal, at most
    /// <see cref="StrengthenLimit"/> of them, whose exact result a plain <c>Tactic.Omega()</c> proves in range, the
    /// equation <c>(a op b).toInt = a.toInt op b.toInt</c>, as simp lemmas for the omega-prep step, tried before its
    /// wrap-around lemmas. Null when there is none.
    /// </summary>
    private SimpTheorems? ExactValues(MVarId g)
    {
        var candidates = new List<(Name Lemma, Expr[] Args)>();
        var seen = new HashSet<Expr>();
        foreach (var term in Terms(g))
        {
            ExprOps.ForEach(term, (e, _) =>
            {
                if (candidates.Count < StrengthenLimit && !e.HasLooseBVars && !e.HasExprMVar && Operation(e) is { } found && seen.Add(e))
                {
                    candidates.Add(found);
                }
                return true;
            });
        }
        SimpTheorems? theorems = null;
        foreach (var (lemma, args) in candidates)
        {
            if (Env.Find(lemma) is null)
            {
                continue;
            }
            var partial = Expr.App(Expr.Const(lemma), args);
            if (WithContext(g, () => WhnfR(InferType(partial))) is not ForallExpr { BinderType: var range })
            {
                continue;
            }
            if (ProveByOmega(g, range) is { } proof)
            {
                (theorems ??= new SimpTheorems()).AddRange(MkSimpTheoremsFromProof(Expr.App(partial, proof), priority: DefaultSimpPriority + 10));
            }
        }
        return theorems;

        static (Name, Expr[])? Operation(Expr e)
        {
            if (e.GetAppFn() is not ConstExpr { Name: var head })
            {
                return null;
            }
            var args = e.GetAppArgs();
            string? op = args.Length == 6 && head == OmegaNames.HAdd ? "add"
                : args.Length == 6 && head == OmegaNames.HSub ? "sub"
                : args.Length == 6 && head == OmegaNames.HMul ? "mul"
                : args.Length == 3 && head == OmegaNames.NegNeg ? "neg"
                : null;
            if (op is null || args[0] is not ConstExpr { Name: var type } || (type != Int32Name && type != Int64Name))
            {
                return null;
            }
            // A literal's negation (`-5`), or an operation on literals, is a literal to the prep step's lemmas.
            Expr[] operands = op == "neg" ? [args[2]] : [args[4], args[5]];
            if (operands.All(x => OmegaExprs.Nat(x) is not null || OmegaExprs.AppOf(x, OmegaNames.NegNeg, 3) is [_, _, var n] && OmegaExprs.Nat(n) is not null))
            {
                return null;
            }
            return (Name.Parse($"Warrant.{type}.toInt_{op}_of_range"), operands);
        }
    }

    /// <summary>
    /// For each product <c>x * y</c> of two non-literal integer terms, at most <see cref="StrengthenLimit"/> of them, the
    /// four lemmas of <see cref="ProductBounds"/> at one literal bound on each side of <c>x</c> and <c>y</c>, each added as
    /// an implication from its bounds, <c>a ≤ x → b ≤ y → a * y + b * x - a * b ≤ x * y</c>, which <c>omega</c> reads as a
    /// disjunction and discharges. The bound on a side is the tightest fact: what a hypothesis states, through <c>∧</c>,
    /// and through <c>¬</c> (<c>¬(p ∨ q)</c> is <c>¬p</c> and <c>¬q</c>, <c>¬¬p</c> is <c>p</c>, <c>¬(x &lt; c)</c> is
    /// <c>c ≤ x</c>), as the negated goal of <c>Spec.Ensures(r =&gt; !(a &gt;= 0) || r &gt;= 0)</c> states <c>0 ≤ a</c>.
    /// With no fact on a side, the tightest comparison found anywhere else, or the complement of one, is used: it is only
    /// a premise. The products and the bounds are read from the goal as the omega-prep
    /// step leaves it (where <c>(a * b).toInt</c> is <c>a.toInt * b.toInt</c> under its <c>bmod</c>, and <c>0 ≤ a</c> is
    /// <c>0 ≤ a.toInt</c>), in a trial run that is then undone; the facts are added to <paramref name="g"/> itself, before
    /// the prep step, so later proofs in the goal have them. A product of three factors, <c>(x * y) * z</c>, gets no bound
    /// for its outer product, whose factor <c>x * y</c> has no literal bound.
    /// </summary>
    private MVarId ProductBoundFacts(MVarId g)
    {
        var known = WithContext(g, () => LCtx.Decls.Select(d => d.FVarId).ToHashSet());
        var products = new List<(Expr X, Expr Y)>();
        var lower = new Dictionary<Expr, Candidates>();
        var upper = new Dictionary<Expr, Candidates>();
        // No product, no trial prep step: `(a * b).toInt` and `a.toInt * b.toInt` both have a `*` before it.
        if (Terms(g).All(t => ExprOps.Find(t, (e, _) => e is ConstExpr { Name: var n } && n == OmegaNames.HMul) is null))
        {
            return g;
        }
        var saved = SaveState();
        try
        {
            if (SimpAll(g, OmegaPrepSet.Context(this)) is { } trial)
            {
                Scan(trial.Goal);
            }
        }
        catch (MetaException ex) when (Combinators.IsRecoverable(ex))
        {
        }
        finally
        {
            Restore(saved);
        }
        if (products.Count == 0)
        {
            return g;
        }
        var facts = new List<(Name, Expr, Expr)>();
        foreach (var (x, y) in products)
        {
            var lx = Bound(lower, x, lowerSide: true);
            var ux = Bound(upper, x, lowerSide: false);
            var ly = Bound(lower, y, lowerSide: true);
            var uy = Bound(upper, y, lowerSide: false);
            // mul_ge_of_ge_of_ge, mul_ge_of_le_of_le, mul_le_of_ge_of_le, mul_le_of_le_of_ge: the bounds on x, then on y.
            (BigInteger? Bx, BigInteger? By)[] corners = [(lx, ly), (ux, uy), (lx, uy), (ux, ly)];
            for (int lemma = 0; lemma < corners.Length; lemma++)
            {
                if (corners[lemma] is not ({ } a, { } b) || Env.Find(ProductBounds[lemma]) is null)
                {
                    continue;
                }
                var fact = Expr.App(Expr.Const(ProductBounds[lemma]), x, y, OmegaExprs.IntLit(a), OmegaExprs.IntLit(b));
                facts.Add((Name.From("hmul"), WithContext(g, () => InferType(fact)), fact));
            }
        }
        return facts.Count == 0 ? g : AssertHypotheses(g, facts).Goal;

        void Scan(MVarId prepped)
        {
            var hyps = WithContext(prepped, () => LCtx.Decls.Where(d => !d.IsImplementationDetail && IsProp(d.Type)).Select(d => this.InstantiateMVars(d.Type)).ToList());
            var seen = new HashSet<Expr>();
            var facts = new HashSet<Expr>();
            foreach (var hyp in hyps)
            {
                // What a hypothesis states through `∧` and `¬` is a fact; a comparison anywhere else (an `if`'s condition, a
                // side of `∨`) is only a candidate, and so is the complement of each comparison.
                Facts(hyp, negated: false, facts);
                ExprOps.ForEach(hyp, (e, _) =>
                {
                    if (e.HasLooseBVars)
                    {
                        return false;
                    }
                    if (products.Count < StrengthenLimit && OmegaExprs.AppOf(e, OmegaNames.HMul, 6) is [var t, _, _, _, var x, var y] && IsInt(t)
                        && Ground(x) is null && Ground(y) is null && OnlyKnown(e) && seen.Add(e))
                    {
                        products.Add((x, y));
                    }
                    if (!facts.Contains(e))
                    {
                        Candidate(e, fact: false);
                    }
                    return true;
                });
            }
        }

        // `negated`: e is stated under an odd number of `¬`, so `p ∨ q` states both negations and a comparison its complement.
        void Facts(Expr e, bool negated, HashSet<Expr> facts)
        {
            if (OmegaExprs.AppOf(e, negated ? OmegaNames.Or : OmegaNames.And, 2) is [var p, var q])
            {
                Facts(p, negated, facts);
                Facts(q, negated, facts);
                return;
            }
            if (OmegaExprs.AppOf(e, OmegaNames.Not, 1) is [var inner])
            {
                Facts(inner, !negated, facts);
                return;
            }
            // ¬(p → q) states p and ¬q (simp writes `¬(p ∧ q)` as `p → ¬q`).
            if (negated && e is ForallExpr { BinderType: var premise, Body: var conclusion } && !conclusion.HasLooseBVars)
            {
                Facts(premise, negated: false, facts);
                Facts(conclusion, negated: true, facts);
                return;
            }
            if (facts.Add(e))
            {
                Candidate(e, fact: true, negated);
            }
        }

        void Candidate(Expr e, bool fact, bool negated = false)
        {
            if (Comparison(e) is not var (strict, a, b))
            {
                return;
            }
            // a ≤ b, or a < b, that is a + 1 ≤ b; its complement is b < a, or b ≤ a. A fact states one of the two (the
            // complement when negated); any other comparison is a candidate both ways (a branch taken or not).
            if (Ground(a) is { } c)
            {
                if (!fact || !negated)
                {
                    Add(lower, b, strict ? c + 1 : c, fact);
                }
                if (!fact || negated)
                {
                    Add(upper, b, strict ? c : c - 1, fact);
                }
            }
            else if (Ground(b) is { } d)
            {
                if (!fact || !negated)
                {
                    Add(upper, a, strict ? d - 1 : d, fact);
                }
                if (!fact || negated)
                {
                    Add(lower, a, strict ? d : d + 1, fact);
                }
            }
        }

        // Whether every free variable of e is one of g's: a term the trial prep step made up cannot be used in g.
        bool OnlyKnown(Expr e) => ExprOps.Find(e, (y, _) => y is FVarExpr f && !known.Contains(f.Id)) is null;

        // The bound used on one side of a factor: the tightest fact, else the tightest candidate (only a premise).
        static BigInteger? Bound(Dictionary<Expr, Candidates> bounds, Expr x, bool lowerSide)
        {
            if (!bounds.TryGetValue(x, out var c))
            {
                return null;
            }
            // Tightest first: the largest lower bound, the smallest upper bound.
            var set = c.Facts.Count > 0 ? c.Facts : c.Others;
            return set.Count == 0 ? null : lowerSide ? set.Max : set.Min;
        }

        static void Add(Dictionary<Expr, Candidates> bounds, Expr term, BigInteger value, bool fact)
        {
            if (!bounds.TryGetValue(term, out var c))
            {
                bounds[term] = c = new Candidates([], []);
            }
            (fact ? c.Facts : c.Others).Add(value);
        }

        static (bool Strict, Expr A, Expr B)? Comparison(Expr e) =>
            OmegaExprs.AppOf(e, OmegaNames.LE, 4) is [var t, _, var a, var b] && IsInt(t) ? (false, a, b)
            : OmegaExprs.AppOf(e, OmegaNames.LT, 4) is [var u, _, var c, var d] && IsInt(u) ? (true, c, d)
            : null;

        // groundInt?, and a negated one: the prep step's literal lemmas state a negative literal as `-↑n`.
        static BigInteger? Ground(Expr e) =>
            OmegaM.GroundInt(e) ?? (OmegaExprs.AppOf(e, OmegaNames.NegNeg, 3) is [_, _, var x] && Ground(x) is { } v ? -v : null);

        static bool IsInt(Expr t) => t is ConstExpr { Name: var n } && n == OmegaNames.Int;
    }

    /// <summary>The literal bounds read for one side of a factor: from facts, and from other comparisons.</summary>
    private sealed record Candidates(SortedSet<BigInteger> Facts, SortedSet<BigInteger> Others);

    private static Expr IntLe(Expr a, Expr b) => Expr.App(Expr.Const(OmegaNames.LE, Level.Zero), OmegaExprs.IntType, Expr.Const(IntInstLE), a, b);

    /// <summary>A proof of <paramref name="prop"/> in <paramref name="g"/>'s context by a plain <c>Tactic.Omega()</c>, or null.</summary>
    private Expr? ProveByOmega(MVarId g, Expr prop)
    {
        var saved = SaveState();
        try
        {
            var goal = WithContext(g, () => MkFreshExprSyntheticOpaqueMVar(prop));
            OmegaPlain(goal.Id);
            var proof = this.InstantiateMVars(goal);
            if (proof.HasExprMVar)
            {
                Restore(saved);
                return null;
            }
            return proof;
        }
        catch (MetaException ex) when (Combinators.IsRecoverable(ex))
        {
            Restore(saved);
            return null;
        }
    }

    /// <summary>The goal's target and its hypotheses' types.</summary>
    private IEnumerable<Expr> Terms(MVarId g) => WithContext(g, () =>
        LCtx.Decls.Where(d => !d.IsImplementationDetail).Select(d => this.InstantiateMVars(d.Type))
            .Append(this.InstantiateMVars(GetMVarType(g))).ToList());
}
