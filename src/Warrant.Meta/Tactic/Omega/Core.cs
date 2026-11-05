using System.Collections.Immutable;
using System.Numerics;
using Warrant.Cic;
using static Warrant.Meta.Omega.OmegaExprs;

namespace Warrant.Meta.Omega;

/// <summary>
/// How a constraint on some coefficients was derived (Lean's <c>Justification</c>, Lean/Elab/Tactic/Omega/Core.lean
/// 42-59). The proof of a contradiction restates the tree with the <c>Init/Omega</c> lemmas.
/// </summary>
internal abstract record Justification
{
    /// <summary><c>Problem.assumptions[I]</c> proves <c>S.sat' X atoms</c>.</summary>
    public sealed record Assumption(Constraint S, Coeffs X, int I) : Justification;

    /// <summary><c>tidy</c> of <c>J</c>, which justifies <c>S</c> on <c>X</c>.</summary>
    public sealed record Tidy(Constraint S, Coeffs X, Justification J) : Justification;

    /// <summary><c>combine</c> of <c>J</c> (for <c>S</c>) and <c>K</c> (for <c>T</c>), both on <c>X</c>.</summary>
    public sealed record Combine(Constraint S, Constraint T, Coeffs X, Justification J, Justification K) : Justification;

    /// <summary><c>A * x + B * y</c> of <c>J</c> (for <c>S</c> on <c>X</c>) and <c>K</c> (for <c>T</c> on <c>Y</c>).</summary>
    public sealed record Combo(Constraint S, Constraint T, BigInteger A, Coeffs X, BigInteger B, Coeffs Y, Justification J, Justification K) : Justification;

    /// <summary>The balanced-mod step of a hard equality: <c>J</c> justifies <c>exact R</c> on <c>X</c>.</summary>
    public sealed record Bmod(BigInteger M, BigInteger R, int I, Coeffs X, Justification J) : Justification;

    /// <summary>
    /// <c>Justification.proof</c> (Core.lean 117): a proof that the justified constraint holds at <paramref name="v"/>,
    /// the atoms.
    /// </summary>
    public Expr Proof(MetaM m, Expr v, IReadOnlyList<Proof> assumptions) => this switch
    {
        Assumption a => assumptions[a.I](),
        Tidy t => Expr.App(Expr.Const(OmegaNames.TidySat), ToExpr(t.S), ToExpr(t.X), v, t.J.Proof(m, v, assumptions)),
        Combine c => Expr.App(Expr.Const(OmegaNames.ConstraintCombineSat), ToExpr(c.S), ToExpr(c.T), ToExpr(c.X), v,
            c.J.Proof(m, v, assumptions), c.K.Proof(m, v, assumptions)),
        Combo c => Expr.App(Expr.Const(OmegaNames.ComboSat), ToExpr(c.S), ToExpr(c.T), IntLit(c.A), ToExpr(c.X), IntLit(c.B), ToExpr(c.Y), v,
            c.J.Proof(m, v, assumptions), c.K.Proof(m, v, assumptions)),
        Bmod b => BmodProof(m, b, v, b.J.Proof(m, v, assumptions)),
        _ => throw new InvalidOperationException("unknown justification"),
    };

    /// <summary><c>bmodProof</c> (Core.lean 102).</summary>
    private static Expr BmodProof(MetaM m, Bmod b, Expr v, Expr w)
    {
        var mExpr = NatLit(b.M);
        var i = NatLit(b.I);
        var x = ToExpr(b.X);
        var h = OmegaAppBuilder.MkDecideProof(m, NatLe(Expr.App(Expr.Const(OmegaNames.CoeffsLength), x), i));
        var lhs = Expr.App(Expr.Const(OmegaNames.CoeffsGet), v, i);
        var rhs = Expr.App(Expr.Const(OmegaNames.BmodDivTerm), mExpr, x, v);
        var p = OmegaAppBuilder.MkEqReflWithExpectedType(m, lhs, rhs);
        return Expr.App(Expr.Const(OmegaNames.BmodSat), mExpr, IntLit(b.R), i, x, v, h, p, w);
    }
}

/// <summary>A constraint on coefficients with its justification (Lean's <c>Fact</c>, Core.lean 129).</summary>
/// <param name="Coeffs">The coefficients.</param>
/// <param name="Constraint">The constraint.</param>
/// <param name="Justification">How it was derived.</param>
internal sealed record Fact(Coeffs Coeffs, Constraint Constraint, Justification Justification)
{
    /// <summary><c>Fact.tidy</c>: the tidied fact, or this one if <c>tidy?</c> does nothing.</summary>
    public Fact Tidy() =>
        Omega.Tidy.TidyQ(Constraint, Coeffs) is var (s, x) ? new(x, s, new Justification.Tidy(Constraint, Coeffs, Justification)) : this;

    /// <summary><c>Fact.combo a f b g</c>.</summary>
    public static Fact Combo(BigInteger a, Fact f, BigInteger b, Fact g) => new(
        Coeffs.Combo(a, f.Coeffs, b, g.Coeffs),
        Constraint.Combo(a, f.Constraint, b, g.Constraint),
        new Justification.Combo(f.Constraint, g.Constraint, a, f.Coeffs, b, g.Coeffs, f.Justification, g.Justification));
}

/// <summary>
/// An <c>omega</c> problem (Lean's <c>Problem</c>, Core.lean 167): the proofs of the assumptions and the current
/// constraints, keyed by their coefficients. It is a persistent value, as in Lean, because a case split reuses it in both
/// branches. The constraints keep their insertion order, so the algorithm is deterministic.
/// </summary>
internal sealed record Problem
{
    /// <summary>The proofs of the ground assumptions.</summary>
    public ImmutableList<Proof> Assumptions { get; init; } = [];

    /// <summary>The number of variables.</summary>
    public int NumVars { get; init; }

    /// <summary>The constraints, by their coefficients.</summary>
    public ImmutableDictionary<Coeffs, Fact> Constraints { get; init; } = ImmutableDictionary<Coeffs, Fact>.Empty;

    /// <summary>The order the constraints were first inserted in.</summary>
    public ImmutableList<Coeffs> Order { get; init; } = [];

    /// <summary>The coefficients with an exact constraint (an equality), in insertion order.</summary>
    public ImmutableList<Coeffs> Equalities { get; init; } = [];

    /// <summary>The equalities used to eliminate a variable, most recent first, with the variable and its coefficient's sign.</summary>
    public ImmutableList<(Fact Fact, int Var, BigInteger Sign)> Eliminations { get; init; } = [];

    /// <summary>Whether the problem may be satisfiable.</summary>
    public bool Possible { get; init; } = true;

    /// <summary>A proof of <c>False</c> once the problem is impossible.</summary>
    public Proof? ProveFalse { get; init; }

    /// <summary>Whether there are no constraints.</summary>
    public bool IsEmpty => Constraints.IsEmpty;

    /// <summary>The facts, in insertion order.</summary>
    public IEnumerable<Fact> Facts => Order.Select(c => Constraints[c]);

    /// <summary>A problem with these assumptions and eliminations and no constraints.</summary>
    private Problem Fresh() => new() { Assumptions = Assumptions, Eliminations = Eliminations };

    /// <summary>
    /// <c>proveFalse</c> (Core.lean 218): from a justification of an impossible constraint, <c>False</c>.
    /// </summary>
    private static Proof ProveFalseOf(OmegaM o, Constraint s, Coeffs x, Justification j, ImmutableList<Proof> assumptions) => () =>
    {
        var m = o.Meta;
        var v = o.AtomsCoeffs();
        var prf = j.Proof(m, v, assumptions);
        var sExpr = ToExpr(s);
        var bool_ = Expr.Const(OmegaNames.Bool);
        var impossible = OmegaAppBuilder.MkDecideProof(m, MkEq(bool_, Expr.App(Expr.Const(OmegaNames.ConstraintIsImpossible), sExpr), BoolTrue));
        return Expr.App(Expr.Const(OmegaNames.ConstraintNotSatOfIsImpossible), sExpr, impossible, ToExpr(x), v, prf);
    };

    /// <summary><c>insertConstraint</c> (Core.lean 231): without combining with an existing constraint.</summary>
    public Problem InsertConstraint(OmegaM o, Fact f)
    {
        if (f.Constraint.IsImpossible)
        {
            return this with
            {
                Possible = false,
                ProveFalse = ProveFalseOf(o, f.Constraint, f.Coeffs, f.Justification, Assumptions),
            };
        }
        return this with
        {
            NumVars = Math.Max(NumVars, f.Coeffs.Length),
            Constraints = Constraints.SetItem(f.Coeffs, f),
            Order = Constraints.ContainsKey(f.Coeffs) ? Order : Order.Add(f.Coeffs),
            Equalities = f.Constraint.IsExact && !Equalities.Contains(f.Coeffs) ? Equalities.Add(f.Coeffs) : Equalities,
        };
    }

    /// <summary><c>addConstraint</c> (Core.lean 254): combining with the constraint already on the same coefficients.</summary>
    public Problem AddConstraint(OmegaM o, Fact f)
    {
        if (!Possible)
        {
            return this;
        }
        if (!Constraints.TryGetValue(f.Coeffs, out var existing))
        {
            return f.Constraint == Constraint.Trivial ? this : InsertConstraint(o, f);
        }
        var r = f.Constraint.Combine(existing.Constraint);
        if (r == existing.Constraint)
        {
            return this;
        }
        if (r == f.Constraint)
        {
            return InsertConstraint(o, f);
        }
        return InsertConstraint(o, new Fact(f.Coeffs, r,
            new Justification.Combine(f.Constraint, existing.Constraint, f.Coeffs, f.Justification, existing.Justification)));
    }

    /// <summary>
    /// <c>selectEquality</c> (Core.lean 289): the first equality with a <c>±1</c> coefficient, else the one with the least
    /// <c>(minNatAbs, maxNatAbs)</c>.
    /// </summary>
    public (Coeffs Coeffs, BigInteger Min)? SelectEquality()
    {
        (Coeffs, BigInteger)? best = null;
        foreach (var c in Equalities)
        {
            if (best is not var (r, m))
            {
                best = (c, MinNatAbs.Min(c));
                continue;
            }
            if (m >= 2)
            {
                var m1 = MinNatAbs.Min(c);
                if (m1 < m || (m1 == m && MinNatAbs.Max(c) < MinNatAbs.Max(r)))
                {
                    best = (c, m1);
                }
            }
        }
        return best;
    }

    /// <summary><c>replayEliminations</c> (Core.lean 305): applies the equalities already solved to a new fact.</summary>
    public Fact ReplayEliminations(Fact f)
    {
        var g = f;
        for (int k = Eliminations.Count - 1; k >= 0; k--)
        {
            var (e, i, s) = Eliminations[k];
            var y = g.Coeffs.Get(i);
            if (!y.IsZero)
            {
                g = Fact.Combo(-1 * s * y, e, 1, g);
            }
        }
        return g;
    }

    /// <summary><c>solveEasyEquality</c> (Core.lean 316): eliminates a variable with a <c>±1</c> coefficient.</summary>
    public Problem SolveEasyEquality(OmegaM o, Coeffs c)
    {
        int i = c.FindUnit() ?? 0;
        var sign = LeanInt.Sign(c.Get(i));
        if (!Constraints.TryGetValue(c, out var f))
        {
            return this;
        }
        var p = Fresh() with { Eliminations = Eliminations.Insert(0, (f, i, sign)) };
        foreach (var g in Facts)
        {
            var ci = g.Coeffs.Get(i);
            p = ci.IsZero ? p.AddConstraint(o, g) : p.AddConstraint(o, Fact.Combo(-1 * sign * ci, f, 1, g).Tidy());
        }
        return p;
    }

    /// <summary>
    /// <c>dealWithHardEquality</c> (Core.lean 340): introduces a new variable through balanced mod, so that a new easy
    /// equality appears.
    /// </summary>
    public Problem DealWithHardEquality(OmegaM o, Coeffs c)
    {
        if (!Constraints.TryGetValue(c, out var fact) || fact.Constraint is not { Lower: { } r, Upper: { } r1 })
        {
            return this;
        }
        var m = MinNatAbs.Min(c) + 1;
        var x = Expr.App(Expr.Const(OmegaNames.BmodDivTerm), NatLit(m), ToExpr(c), o.AtomsCoeffs());
        var (i, facts) = o.Lookup(x);
        if (r1 != r)
        {
            throw new MetaException("Invalid constraint, expected an equation.");
        }
        if (facts is null)
        {
            throw new MetaException("When solving hard equality, new atom had been seen before!");
        }
        if (!facts.IsEmpty)
        {
            throw new MetaException("When solving hard equality, there were unexpected new facts!");
        }
        return AddConstraint(o, new Fact(Tidy.BmodCoeffs(m, i, c), Constraint.Exact(LeanInt.BMod(r, m)),
            new Justification.Bmod(m, r, i, c, fact.Justification)));
    }

    /// <summary><c>solveEqualities</c> (Core.lean 369): eliminates every equality.</summary>
    public Problem SolveEqualities(OmegaM o)
    {
        var p = this;
        while (p.Possible && p.SelectEquality() is var (c, m))
        {
            o.Meta.Budget.Tick();
            p = m.IsOne ? p.SolveEasyEquality(o, c) : p.DealWithHardEquality(o, c);
        }
        return p;
    }

    /// <summary>
    /// <c>addInequality</c> (Core.lean 396): adds <c>const + coeffs · atoms ≥ 0</c>, given its proof.
    /// </summary>
    public Problem AddInequality(OmegaM o, BigInteger @const, Coeffs coeffs, Proof prf)
    {
        int i = Assumptions.Count;
        var p1 = this with
        {
            Assumptions = Assumptions.Add(() => Expr.App(Expr.Const(OmegaNames.ConstraintAddInequalitySat), IntLit(@const), ToExpr(coeffs), o.AtomsCoeffs(), prf())),
        };
        var s = new Constraint(-@const, null);
        var f = ReplayEliminations(new Fact(coeffs, s, new Justification.Assumption(s, coeffs, i))).Tidy();
        return p1.AddConstraint(o, f);
    }

    /// <summary><c>addEquality</c> (Core.lean 414): adds <c>const + coeffs · atoms = 0</c>, given its proof.</summary>
    public Problem AddEquality(OmegaM o, BigInteger @const, Coeffs coeffs, Proof prf)
    {
        int i = Assumptions.Count;
        var p1 = this with
        {
            Assumptions = Assumptions.Add(() => Expr.App(Expr.Const(OmegaNames.ConstraintAddEqualitySat), IntLit(@const), ToExpr(coeffs), o.AtomsCoeffs(), prf())),
        };
        var s = Constraint.Exact(-@const);
        var f = ReplayEliminations(new Fact(coeffs, s, new Justification.Assumption(s, coeffs, i))).Tidy();
        return p1.AddConstraint(o, f);
    }

    /// <summary>The data for eliminating one variable by Fourier–Motzkin (Lean's <c>FourierMotzkinData</c>, Core.lean 435).</summary>
    private sealed record FourierMotzkinData(int Var)
    {
        public ImmutableList<Fact> Irrelevant { get; init; } = [];

        public ImmutableList<(Fact Fact, BigInteger Coeff)> LowerBounds { get; init; } = [];

        public ImmutableList<(Fact Fact, BigInteger Coeff)> UpperBounds { get; init; } = [];

        public bool LowerExact { get; init; } = true;

        public bool UpperExact { get; init; } = true;

        public bool IsEmpty => LowerBounds.IsEmpty && UpperBounds.IsEmpty;

        public long Size => (long)LowerBounds.Count * UpperBounds.Count;

        public bool Exact => LowerExact || UpperExact;
    }

    /// <summary><c>fourierMotzkinData</c> (Core.lean 481).</summary>
    private FourierMotzkinData[] FourierMotzkinDataOf()
    {
        var data = Enumerable.Range(0, NumVars).Select(i => new FourierMotzkinData(i)).ToArray();
        foreach (var f in Facts)
        {
            for (int i = 0; i < NumVars; i++)
            {
                var x = f.Coeffs.Get(i);
                var d = data[i];
                if (x.IsZero)
                {
                    data[i] = d with { Irrelevant = d.Irrelevant.Insert(0, f) };
                    continue;
                }
                var s1 = f.Constraint.Scale(x);
                bool unit = BigInteger.Abs(x).IsOne;
                if (s1.Lower is not null)
                {
                    d = d with { LowerBounds = d.LowerBounds.Insert(0, (f, x)), LowerExact = d.LowerExact && unit };
                }
                if (s1.Upper is not null)
                {
                    d = d with { UpperBounds = d.UpperBounds.Insert(0, (f, x)), UpperExact = d.UpperExact && unit };
                }
                data[i] = d;
            }
        }
        return data;
    }

    /// <summary>
    /// <c>fourierMotzkinSelect</c> (Core.lean 511): prefers an elimination that adds no constraint, then an exact one,
    /// then the fewest new constraints.
    /// </summary>
    private static FourierMotzkinData FourierMotzkinSelect(FourierMotzkinData[] all)
    {
        var data = all.Where(d => !d.IsEmpty).ToArray();
        int bestIdx = 0;
        var bestSize = data[0].Size;
        var bestExact = data[0].Exact;
        if (bestSize == 0)
        {
            return data[0];
        }
        for (int i = 1; i < data.Length; i++)
        {
            var exact = data[i].Exact;
            var size = data[i].Size;
            if (size == 0 || (!bestExact && exact) || (bestExact == exact && size < bestSize))
            {
                if (size == 0)
                {
                    return data[i];
                }
                bestIdx = i;
                bestExact = exact;
                bestSize = size;
            }
        }
        return data[bestIdx];
    }

    /// <summary><c>fourierMotzkin</c> (Core.lean 538): eliminates one variable.</summary>
    private Problem FourierMotzkin(OmegaM o)
    {
        var d = FourierMotzkinSelect(FourierMotzkinDataOf());
        var r = Fresh();
        foreach (var f in d.Irrelevant)
        {
            r = r.InsertConstraint(o, f);
        }
        foreach (var (f, b) in d.LowerBounds)
        {
            foreach (var (g, a) in d.UpperBounds)
            {
                o.Meta.Budget.Tick();
                r = r.AddConstraint(o, Fact.Combo(a, f, -b, g).Tidy());
            }
        }
        return r;
    }

    /// <summary>
    /// <c>elimination</c> and <c>runOmega</c> (Core.lean 555-572), without dark and grey shadows: Fourier–Motzkin, then
    /// the equalities that produced, until the problem is empty or impossible.
    /// </summary>
    public Problem Elimination(OmegaM o)
    {
        var p = this;
        while (p.Possible && !p.IsEmpty)
        {
            o.Meta.Budget.Tick();
            p = p.FourierMotzkin(o);
            if (p.Possible)
            {
                p = p.SolveEqualities(o);
            }
        }
        return p;
    }
}
