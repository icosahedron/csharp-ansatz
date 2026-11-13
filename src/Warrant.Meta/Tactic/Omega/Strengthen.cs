using System.Numerics;
using Warrant.Cic;
using Warrant.Kernel;
using Warrant.Meta.Omega;

namespace Warrant.Meta;

/// <summary>
/// What <c>Tactic.Omega()</c> tries when <c>omega</c> alone fails (#217, #237, #257): facts that are true in every case
/// and that <c>omega</c> cannot find itself, each one proved, so the step can only make a true goal provable. It runs only
/// after a failure, so a goal <c>omega</c> proves alone gets the same proof as before.
/// <list type="bullet">
/// <item>A <c>decimal</c> literal's <c>units</c> is a closed integer, stated as <c>units (lit …) = n</c> and proved by
/// <c>rfl</c>: the kernel computes it (#217).</item>
/// <item>An <c>int</c> or <c>long</c> <c>+</c>, <c>-</c>, <c>*</c> or unary <c>-</c> whose exact result <c>omega</c> proves
/// in range has that exact value, by <c>Warrant.Int32.toInt_mul_of_range</c> and its siblings, instead of the
/// wrap-around's <c>Int.bmod</c>, whose case split <c>omega</c> cannot always close (#237).</item>
/// <item>A product <c>x * y</c> of two integer terms, an atom to <c>omega</c>, gets the linear bounds that follow from the
/// literal bounds on its factors that <c>omega</c> proves (<c>Warrant.Int.mul_ge_of_ge_of_ge</c> and its siblings,
/// McCormick's inequalities, #257).</item>
/// </list>
/// </summary>
public sealed partial class MetaM
{
    /// <summary>How many terms of each kind the step looks at, so a large goal does not run <c>omega</c> many times.</summary>
    private const int StrengthenLimit = 8;

    private static readonly Name DecimalUnits = Name.Parse("Warrant.Decimal.units");
    private static readonly Name DecimalLit = Name.Parse("Warrant.Decimal.lit");
    private static readonly Name BoolTrueName = Name.Parse("Bool.true");
    private static readonly Name BoolFalseName = Name.Parse("Bool.false");
    private static readonly Name Int32Name = Name.Parse("Int32");
    private static readonly Name Int64Name = Name.Parse("Int64");
    private static readonly Name IntInstLE = Name.Parse("Int.instLEInt");
    private static readonly Name[] ProductBounds =
    [
        Name.Parse("Warrant.Int.mul_ge_of_ge_of_ge"), Name.Parse("Warrant.Int.mul_ge_of_le_of_le"),
        Name.Parse("Warrant.Int.mul_le_of_ge_of_le"), Name.Parse("Warrant.Int.mul_le_of_le_of_ge"),
    ];

    /// <summary>
    /// <c>Tactic.Omega()</c> with the strengthening facts: the in-range exact values in the omega-prep step, the decimal
    /// literal values and product bounds after it (the prep step's <c>decide</c> would turn a literal's equation into
    /// <c>True</c>), then <c>omega</c>.
    /// </summary>
    /// <param name="mvarId">The goal.</param>
    /// <param name="depth">0 at the top; the nested <c>omega</c> calls that prove a range or a bound are deeper.</param>
    private void OmegaStrengthened(MVarId mvarId, int depth)
    {
        // The goal's premises become hypotheses first, so a range or bound proof can use them.
        if (FalseOrByContra(mvarId) is not { } start)
        {
            return;
        }
        var exact = depth == 0 ? ExactValues(start, depth) : null;
        var context = OmegaPrepSet.Context(this);
        if (exact is not null)
        {
            context = context with { Theorems = context.Theorems.Insert(0, exact) };
        }
        if (SimpAll(start, context) is not { } prepped)
        {
            return;
        }
        if (FalseOrByContra(prepped.Goal) is not { } contra)
        {
            return;
        }
        var g = ProductBoundFacts(DecimalLiteralFacts(contra), depth);
        if (WithReducibleAndInstances(() => AssumptionCore(g)))
        {
            return;
        }
        Omega(g);
    }

    /// <summary>For each <c>units (lit s m e _ _)</c> with literal arguments, the hypothesis <c>units (lit …) = n</c> by <c>rfl</c>.</summary>
    private MVarId DecimalLiteralFacts(MVarId g)
    {
        var facts = new List<(Name, Expr, Expr)>();
        var seen = new HashSet<Expr>();
        foreach (var term in Terms(g))
        {
            ExprOps.ForEach(term, (e, _) =>
            {
                if (OmegaExprs.AppOf(e, DecimalUnits, 1) is [var lit] && OmegaExprs.AppOf(lit, DecimalLit, 5) is [var sign, var m, var s, _, _]
                    && sign is ConstExpr { Name: var signName } && (signName == BoolTrueName || signName == BoolFalseName)
                    && NatLiteral(m) is { } mantissa && NatLiteral(s) is { } scale && scale <= 28 && !e.HasLooseBVars && seen.Add(e))
                {
                    var value = mantissa * BigInteger.Pow(10, 28 - (int)scale) * (signName == BoolTrueName ? -1 : 1);
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
    /// For each <c>int</c>/<c>long</c> <c>a + b</c>, <c>a - b</c>, <c>a * b</c> or <c>-a</c> in the goal whose exact result
    /// a nested <c>omega</c> proves in range, the equation <c>(a op b).toInt = a.toInt op b.toInt</c>, as simp lemmas for
    /// the omega-prep step, tried before its wrap-around lemmas.
    /// </summary>
    private SimpTheorems? ExactValues(MVarId g, int depth)
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
            if (ProveByOmega(g, range, depth + 1) is { } proof)
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
            var lemma = Name.Parse($"Warrant.{type}.toInt_{op}_of_range");
            return op == "neg" ? (lemma, [args[2]]) : (lemma, [args[4], args[5]]);
        }
    }

    /// <summary>
    /// For each product <c>x * y</c> of two non-literal integer terms in a hypothesis, the bounds of <see cref="ProductBounds"/>
    /// for the literal bounds on <c>x</c> and <c>y</c> that the hypotheses state and a nested <c>omega</c> proves.
    /// </summary>
    private MVarId ProductBoundFacts(MVarId g, int depth)
    {
        if (depth > 1)
        {
            return g;
        }
        var hyps = WithContext(g, () => LCtx.Decls.Where(d => !d.IsImplementationDetail && IsProp(d.Type)).Select(d => this.InstantiateMVars(d.Type)).ToList());
        var products = new List<(Expr X, Expr Y)>();
        var seen = new HashSet<Expr>();
        var lower = new Dictionary<Expr, List<BigInteger>>();
        var upper = new Dictionary<Expr, List<BigInteger>>();
        foreach (var hyp in hyps)
        {
            ExprOps.ForEach(hyp, (e, _) =>
            {
                if (e.HasLooseBVars)
                {
                    return false;
                }
                if (OmegaExprs.AppOf(e, OmegaNames.HMul, 6) is [var t, _, _, _, var x, var y] && t is ConstExpr { Name: var tn } && tn == OmegaNames.Int
                    && Ground(x) is null && Ground(y) is null && products.Count < StrengthenLimit && seen.Add(e))
                {
                    products.Add((x, y));
                }
                if (Comparison(e) is var (strict, a, b))
                {
                    // a ≤ b, or a < b, that is a + 1 ≤ b.
                    if (Ground(a) is { } c)
                    {
                        Add(lower, b, strict ? c + 1 : c);
                    }
                    else if (Ground(b) is { } d)
                    {
                        Add(upper, a, strict ? d - 1 : d);
                    }
                }
                return true;
            });
        }
        if (products.Count == 0)
        {
            return g;
        }
        var facts = new List<(Name, Expr, Expr)>();
        var proved = new Dictionary<(Expr, bool), (BigInteger, Expr)?>();
        foreach (var (x, y) in products)
        {
            var lx = Bound(x, lowerSide: true);
            var ux = Bound(x, lowerSide: false);
            var ly = Bound(y, lowerSide: true);
            var uy = Bound(y, lowerSide: false);
            // mul_ge_of_ge_of_ge, mul_ge_of_le_of_le, mul_le_of_ge_of_le, mul_le_of_le_of_ge: the bounds on x, then on y.
            (int Lemma, (BigInteger, Expr)? Bx, (BigInteger, Expr)? By)[] corners = [(0, lx, ly), (1, ux, uy), (2, lx, uy), (3, ux, ly)];
            foreach (var (lemma, bx, by) in corners)
            {
                if (bx is var (a, hx) && by is var (b, hy) && Env.Find(ProductBounds[lemma]) is not null)
                {
                    var proof = Expr.App(Expr.Const(ProductBounds[lemma]), x, y, OmegaExprs.IntLit(a), OmegaExprs.IntLit(b), hx, hy);
                    facts.Add((Name.From("hmul"), WithContext(g, () => InferType(proof)), proof));
                }
            }
        }
        return facts.Count == 0 ? g : AssertHypotheses(g, facts).Goal;

        (BigInteger, Expr)? Bound(Expr x, bool lowerSide)
        {
            if (proved.TryGetValue((x, lowerSide), out var known))
            {
                return known;
            }
            (BigInteger, Expr)? result = null;
            var candidates = (lowerSide ? lower : upper).GetValueOrDefault(x) ?? [];
            // The tightest bound first; a looser one if omega cannot prove it.
            foreach (var c in lowerSide ? candidates.Distinct().OrderDescending() : candidates.Distinct().Order())
            {
                var literal = OmegaExprs.IntLit(c);
                var prop = lowerSide ? IntLe(literal, x) : IntLe(x, literal);
                if (ProveByOmega(g, prop, depth + 2) is { } proof)
                {
                    result = (c, proof);
                    break;
                }
            }
            proved[(x, lowerSide)] = result;
            return result;
        }

        static void Add(Dictionary<Expr, List<BigInteger>> bounds, Expr term, BigInteger value)
        {
            if (!bounds.TryGetValue(term, out var list))
            {
                bounds[term] = list = [];
            }
            list.Add(value);
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

    private static Expr IntLe(Expr a, Expr b) => Expr.App(Expr.Const(OmegaNames.LE, Level.Zero), OmegaExprs.IntType, Expr.Const(IntInstLE), a, b);

    /// <summary>A proof of <paramref name="prop"/> in <paramref name="g"/>'s context by <c>Tactic.Omega()</c>, or null.</summary>
    private Expr? ProveByOmega(MVarId g, Expr prop, int depth)
    {
        var saved = SaveState();
        try
        {
            var goal = WithContext(g, () => MkFreshExprSyntheticOpaqueMVar(prop));
            OmegaTacticAt(goal.Id, depth);
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
