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
    /// <c>Tactic.Omega()</c> with the strengthening facts: the product bounds before the omega-prep step, the in-range
    /// exact values in it, the decimal literal values after it (the prep step's <c>decide</c> would turn a literal's
    /// equation into <c>True</c>), then <c>omega</c>.
    /// </summary>
    /// <param name="mvarId">The goal.</param>
    private void OmegaStrengthened(MVarId mvarId)
    {
        // The goal's premises become hypotheses first, so a bound or range proof can use them.
        if (FalseOrByContra(mvarId) is not { } start)
        {
            return;
        }
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
    /// four lemmas of <see cref="ProductBounds"/> at one literal bound on each side of <c>x</c> and <c>y</c> (see
    /// <c>Bound</c>). A bound stated as a fact (a hypothesis or one of its top-level conjuncts) needs no proof: the lemma
    /// is added as an implication from it, <c>a ≤ x → b ≤ y → a * y + b * x - a * b ≤ x * y</c>, which <c>omega</c> reads
    /// as a disjunction and discharges. A tighter comparison found elsewhere, or the complement of one (an <c>if</c>'s
    /// condition, a side of <c>||</c>: the path may make it true), is used instead when a plain <c>omega</c> proves it from
    /// the linear hypotheses, and its proof is applied; when a side has no fact, its tightest candidate is used as an
    /// implication too (an <c>if</c> in the goal that <c>omega</c> splits). The products and the bounds are read from the goal as the omega-prep
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
            var lx = Bound(x, lowerSide: true);
            var ux = Bound(x, lowerSide: false);
            var ly = Bound(y, lowerSide: true);
            var uy = Bound(y, lowerSide: false);
            // mul_ge_of_ge_of_ge, mul_ge_of_le_of_le, mul_le_of_ge_of_le, mul_le_of_le_of_ge: the bounds on x, then on y.
            ((BigInteger, Expr?)? Bx, (BigInteger, Expr?)? By)[] corners = [(lx, ly), (ux, uy), (lx, uy), (ux, ly)];
            for (int lemma = 0; lemma < corners.Length; lemma++)
            {
                if (corners[lemma] is not ((var a, var hx), (var b, var hy)) || Env.Find(ProductBounds[lemma]) is null)
                {
                    continue;
                }
                Expr fact = Expr.App(Expr.Const(ProductBounds[lemma]), x, y, OmegaExprs.IntLit(a), OmegaExprs.IntLit(b));
                if (hx is not null)
                {
                    fact = hy is not null ? Expr.App(fact, hx, hy) : Expr.App(fact, hx);
                }
                else if (hy is not null)
                {
                    // fun h : (bound on x) => lemma x y a b h hy
                    var premise = WithContext(g, () => WhnfR(InferType(fact))) is ForallExpr f ? f.BinderType : null;
                    if (premise is null)
                    {
                        continue;
                    }
                    fact = Expr.Lam(Name.From("h"), premise, Expr.App(fact, Expr.BVar(0), hy));
                }
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
                // A hypothesis and its top-level conjuncts are facts; a comparison anywhere else (an `if`'s condition, a side
                // of `∨`, under `¬`) is only a candidate, and so is the complement of each comparison.
                Facts(hyp, facts);
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

        void Facts(Expr e, HashSet<Expr> facts)
        {
            if (OmegaExprs.AppOf(e, OmegaNames.And, 2) is [var p, var q])
            {
                Facts(p, facts);
                Facts(q, facts);
                return;
            }
            if (facts.Add(e))
            {
                Candidate(e, fact: true);
            }
        }

        void Candidate(Expr e, bool fact)
        {
            if (Comparison(e) is not var (strict, a, b))
            {
                return;
            }
            // a ≤ b, or a < b, that is a + 1 ≤ b. Unless it is a fact, its complement b < a, or b ≤ a, is a candidate on
            // the other side (a branch not taken: `¬(a < 0)`).
            if (Ground(a) is { } c)
            {
                Add(lower, b, strict ? c + 1 : c, fact);
                if (!fact)
                {
                    Add(upper, b, strict ? c : c - 1, fact: false);
                }
            }
            else if (Ground(b) is { } d)
            {
                Add(upper, a, strict ? d - 1 : d, fact);
                if (!fact)
                {
                    Add(lower, a, strict ? d : d + 1, fact: false);
                }
            }
        }

        // Whether every free variable of e is one of g's: a term the trial prep step made up cannot be used in g.
        bool OnlyKnown(Expr e) => ExprOps.Find(e, (y, _) => y is FVarExpr f && !known.Contains(f.Id)) is null;

        // The bounds a corner is stated at: the tightest fact, and the tightest candidate tighter than it (or the two
        // tightest candidates when no fact bounds this side). omega drops the corners whose premises it cannot show.
        // The bound used on one side of a factor: the tightest tighter-than-fact candidate a plain omega proves from the
        // linear hypotheses (at most two are tried), with its proof; else the tightest fact, with none; else the tightest
        // candidate, with none, for a condition the goal itself splits (`if (a < 0) … else a * b`: `0 ≤ a` in one branch).
        (BigInteger, Expr?)? Bound(Expr x, bool lowerSide)
        {
            if (!(lowerSide ? lower : upper).TryGetValue(x, out var c))
            {
                return null;
            }
            // Tightest first: the largest lower bound, the smallest upper bound.
            IEnumerable<BigInteger> Tightest(SortedSet<BigInteger> set) => lowerSide ? set.Reverse() : set;
            BigInteger? fact = c.Facts.Count > 0 ? Tightest(c.Facts).First() : null;
            foreach (var v in Tightest(c.Others).Where(v => fact is not { } f || (lowerSide ? v > f : v < f)).Take(2))
            {
                var literal = OmegaExprs.IntLit(v);
                if (ProveByOmega(g, lowerSide ? IntLe(literal, x) : IntLe(x, literal), linearOnly: true) is { } proof)
                {
                    return (v, proof);
                }
            }
            return fact is { } b ? (b, null) : c.Others.Count > 0 ? (Tightest(c.Others).First(), null) : null;
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

    /// <summary>The heads <see cref="ProveByOmega"/>'s <c>linearOnly</c> drops hypotheses for.</summary>
    private static readonly HashSet<Name> NonLinear = [OmegaNames.HMul, OmegaNames.HDiv, OmegaNames.HMod, OmegaNames.Ite, Name.Parse("dite")];

    private static Expr IntLe(Expr a, Expr b) => Expr.App(Expr.Const(OmegaNames.LE, Level.Zero), OmegaExprs.IntType, Expr.Const(IntInstLE), a, b);

    /// <summary>A proof of <paramref name="prop"/> in <paramref name="g"/>'s context by a plain <c>Tactic.Omega()</c>, or null.</summary>
    /// <param name="g">The goal whose context the proof is in.</param>
    /// <param name="prop">The proposition.</param>
    /// <param name="linearOnly">
    /// Whether to drop the hypotheses that mention <c>*</c>, <c>/</c>, <c>%</c> or an <c>if</c> first: a factor's literal
    /// bound follows from the linear ones, and the others only make the proof cost more (case splits on a wrap-around).
    /// </param>
    private Expr? ProveByOmega(MVarId g, Expr prop, bool linearOnly = false)
    {
        var saved = SaveState();
        try
        {
            var goal = WithContext(g, () => MkFreshExprSyntheticOpaqueMVar(prop));
            var target = goal.Id;
            if (linearOnly)
            {
                var heavy = WithContext(g, () => LCtx.Decls.Where(d => !d.IsImplementationDetail && IsProp(d.Type)
                    && ExprOps.Find(this.InstantiateMVars(d.Type), (e, _) => e is ConstExpr { Name: var n } && NonLinear.Contains(n)) is not null)
                    .Select(d => d.FVarId).ToList());
                foreach (var fvar in heavy)
                {
                    target = TryClear(target, fvar);
                }
            }
            OmegaPlain(target);
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
