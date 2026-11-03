using Warrant.Cic;
using Warrant.Kernel;

namespace Warrant.Meta;

// Universe unification (a port of Lean 4.35.0's Lean/Meta/LevelDefEq.lean and Lean/Meta/DecLevel.lean),
// with postponed constraints and checkpointDefEq from Lean/Meta/Basic.lean 2385-2506.
public sealed partial class MetaM
{
    // Lean's Context.univApprox: set while retrying postponed constraints with approximations.
    private bool _univApproxActive;

    // ---------------------------------------------------------------- decLevel

    private Level? DecAux(Level u, bool canAssignMVars)
    {
        switch (u.Kind)
        {
            case LevelKind.Zero:
            case LevelKind.Param:
                return null;
            case LevelKind.MVar:
                var mvarId = u.MVarId!.Value;
                if (MCtx.GetLevelAssignment(mvarId) is { } a)
                {
                    return DecAux(a, canAssignMVars);
                }
                if (IsReadOnly(mvarId) || !canAssignMVars)
                {
                    return null;
                }
                var n = MkFreshLevelMVar();
                AssignLevelMVar(mvarId, Level.Succ(n));
                return n;
            case LevelKind.Succ:
                return u.Lhs;
            default:
                // max (u+1) (v+1) = (max u v)+1; the recursive calls must not assign.
                if (DecAux(u.Lhs!, false) is not { } l || DecAux(u.Rhs!, false) is not { } r)
                {
                    return null;
                }
                return LevelOps.MkMax(l, r);
        }
    }

    /// <summary><c>v</c> with <c>u = v+1</c>, assigning a universe metavariable if needed (Lean's <c>decLevel?</c>).</summary>
    public Level? DecLevelOrNull(Level u)
    {
        var mctx = MCtx;
        if (DecAux(u, true) is { } v)
        {
            return v;
        }
        MCtx = mctx;
        return null;
    }

    /// <summary>Lean's <c>decLevel</c>.</summary>
    /// <exception cref="MetaException"><paramref name="u"/> is not greater than 0.</exception>
    public Level DecLevel(Level u) =>
        DecLevelOrNull(u) ?? throw new MetaException($"invalid universe level, {u} is not greater than 0");

    /// <summary>The <c>u</c> with <paramref name="type"/> <c>: Sort (u+1)</c> (Lean's <c>getDecLevel</c>).</summary>
    public Level GetDecLevel(Expr type) => DecLevel(LevelOps.Normalize(this.InstantiateLevelMVars(GetLevel(type))));

    // ---------------------------------------------------------------- solving

    private static bool StrictOccursMax(Level lvl, Level l)
    {
        return l.Kind == LevelKind.Max && (Visit(l.Lhs!) || Visit(l.Rhs!));

        bool Visit(Level u) => u.Kind == LevelKind.Max ? Visit(u.Lhs!) || Visit(u.Rhs!) : u != lvl && lvl.Occurs(u);
    }

    private static Level MkMaxArgsDiff(LMVarId mvarId, Level l, Level acc) => l.Kind switch
    {
        LevelKind.Max => MkMaxArgsDiff(mvarId, l.Rhs!, MkMaxArgsDiff(mvarId, l.Lhs!, acc)),
        LevelKind.MVar when l.MVarId == mvarId => acc,
        _ => LevelOps.MkMax(acc, l),
    };

    // ?m =?= max ?m v: assign ?m := max ?n v for a fresh ?n.
    private void SolveSelfMax(LMVarId mvarId, Level v)
    {
        var n = MkFreshLevelMVar();
        AssignLevelMVar(mvarId, MkMaxArgsDiff(mvarId, v, n));
    }

    // u =?= max u ?m: assign ?m := u (ignoring the solution ?m := 0).
    private bool TryApproxSelfMax(Level u, Level v)
    {
        if (v.Kind != LevelKind.Max)
        {
            return false;
        }
        if (v.Rhs!.IsMVar())
        {
            return Solve(v.Lhs!, v.Rhs!.MVarId!.Value);
        }
        if (v.Lhs!.IsMVar())
        {
            return Solve(v.Rhs!, v.Lhs!.MVarId!.Value);
        }
        return false;

        bool Solve(Level v1, LMVarId mvarId)
        {
            if (u != v1)
            {
                return false;
            }
            AssignLevelMVar(mvarId, u);
            return true;
        }
    }

    // max u₁ u₂ =?= max u₁ ?w: assign ?w := u₂.
    private bool TryApproxMaxMax(Level u, Level v)
    {
        if (u.Kind != LevelKind.Max || v.Kind != LevelKind.Max)
        {
            return false;
        }
        if (v.Rhs!.IsMVar())
        {
            return Solve(v.Lhs!, v.Rhs!.MVarId!.Value);
        }
        if (v.Lhs!.IsMVar())
        {
            return Solve(v.Rhs!, v.Lhs!.MVarId!.Value);
        }
        return false;

        bool Solve(Level v1, LMVarId mvarId)
        {
            if (u.Lhs == v1)
            {
                AssignLevelMVar(mvarId, u.Rhs!);
                return true;
            }
            if (u.Rhs == v1)
            {
                AssignLevelMVar(mvarId, u.Lhs!);
                return true;
            }
            return false;
        }
    }

    private void PostponeIsLevelDefEq(Level lhs, Level rhs) => Postponed = Postponed.Add(new PostponedEntry(lhs, rhs));

    private bool IsMVarWithGreaterDepth(Level v, LMVarId mvarId) =>
        v.IsMVar() && MCtx.GetLevelDecl(v.MVarId!.Value).Depth > MCtx.GetLevelDecl(mvarId).Depth;

    private LBool SolveLevel(Level u, Level v)
    {
        if (u.IsMVar())
        {
            var mvarId = u.MVarId!.Value;
            if (IsReadOnly(mvarId))
            {
                return LBool.Undef;
            }
            if (IsMVarWithGreaterDepth(v, mvarId))
            {
                AssignLevelMVar(v.MVarId!.Value, u);
                return LBool.True;
            }
            if (!u.Occurs(v))
            {
                AssignLevelMVar(mvarId, v);
                return LBool.True;
            }
            if (v.IsMax() && !StrictOccursMax(u, v))
            {
                SolveSelfMax(mvarId, v);
                return LBool.True;
            }
            return LBool.Undef;
        }
        if (v.IsMVar())
        {
            return LBool.Undef; // `solve v u` handles it
        }
        if (u.Kind == LevelKind.Zero)
        {
            switch (v.Kind)
            {
                case LevelKind.Max:
                    return IsLevelDefEqAux(Level.Zero, v.Lhs!) && IsLevelDefEqAux(Level.Zero, v.Rhs!) ? LBool.True : LBool.False;
                case LevelKind.IMax:
                    return IsLevelDefEqAux(Level.Zero, v.Rhs!) ? LBool.True : LBool.False;
                case LevelKind.Succ:
                    return LBool.False;
            }
        }
        if (u.Kind == LevelKind.Succ)
        {
            var u1 = u.Lhs!;
            if (v.Kind == LevelKind.Param)
            {
                return LBool.False;
            }
            if (u1.IsMVar() && u1.Occurs(v))
            {
                return LBool.Undef;
            }
            return DecLevelOrNull(v) is { } v1 ? (IsLevelDefEqAux(u1, v1) ? LBool.True : LBool.False) : LBool.Undef;
        }
        if (_univApproxActive && (TryApproxSelfMax(u, v) || TryApproxMaxMax(u, v)))
        {
            return LBool.True;
        }
        return LBool.Undef;
    }

    private bool HasAssignableLevelMVar(Level l) => l.Kind switch
    {
        LevelKind.MVar => !IsReadOnly(l.MVarId!.Value),
        LevelKind.Succ => l.HasMVar && HasAssignableLevelMVar(l.Lhs!),
        LevelKind.Max or LevelKind.IMax => l.HasMVar && (HasAssignableLevelMVar(l.Lhs!) || HasAssignableLevelMVar(l.Rhs!)),
        _ => false,
    };

    /// <summary>
    /// Unifies two universe levels, assigning universe metavariables and postponing what it cannot
    /// decide yet (Lean's <c>isLevelDefEqAuxImpl</c>). Without <see cref="CheckpointDefEq"/>, the
    /// assignments are not rolled back on failure.
    /// </summary>
    public bool IsLevelDefEqAux(Level lhs, Level rhs)
    {
        ArgumentNullException.ThrowIfNull(lhs);
        ArgumentNullException.ThrowIfNull(rhs);
        while (lhs.Kind == LevelKind.Succ && rhs.Kind == LevelKind.Succ)
        {
            lhs = lhs.Lhs!;
            rhs = rhs.Lhs!;
        }
        var (lb, lk) = LevelOps.ToOffset(lhs);
        var (rb, rk) = LevelOps.ToOffset(rhs);
        if (lb == rb)
        {
            return lk == rk;
        }
        var lhs1 = LevelOps.Normalize(this.InstantiateLevelMVars(lhs));
        var rhs1 = LevelOps.Normalize(this.InstantiateLevelMVars(rhs));
        if (lhs != lhs1 || rhs != rhs1)
        {
            return IsLevelDefEqAux(lhs1, rhs1);
        }
        var r = SolveLevel(lhs, rhs);
        if (r != LBool.Undef)
        {
            return r == LBool.True;
        }
        r = SolveLevel(rhs, lhs);
        if (r != LBool.Undef)
        {
            return r == LBool.True;
        }
        if (!HasAssignableLevelMVar(lhs) && !HasAssignableLevelMVar(rhs))
        {
            if (Config.IsDefEqStuckEx && (lhs.IsMVar() || rhs.IsMVar()))
            {
                throw new IsDefEqStuckException();
            }
            return false;
        }
        PostponeIsLevelDefEq(lhs, rhs);
        return true;
    }

    /// <summary>Lean's <c>isListLevelDefEqAux</c>.</summary>
    public bool IsListLevelDefEqAux(EquatableArray<Level> us, EquatableArray<Level> vs)
    {
        if (us.Count != vs.Count)
        {
            return false;
        }
        for (int i = 0; i < us.Count; i++)
        {
            if (!IsLevelDefEqAux(us[i], vs[i]))
            {
                return false;
            }
        }
        return true;
    }

    // ---------------------------------------------------------------- postponed constraints

    private bool ProcessPostponedStep()
    {
        var ps = Postponed;
        Postponed = [];
        foreach (var p in ps)
        {
            if (!IsLevelDefEqAux(p.Lhs, p.Rhs))
            {
                return false;
            }
        }
        return true;
    }

    /// <summary>
    /// Retries the postponed universe constraints until none remain or no progress is made (Lean's
    /// <c>processPostponed</c>). With <paramref name="mayPostpone"/> false, approximations are tried
    /// before giving up, and leftover constraints fail.
    /// </summary>
    public bool ProcessPostponed(bool mayPostpone = true)
    {
        if (Postponed.Count == 0)
        {
            return true;
        }
        return Loop();

        bool Loop()
        {
            while (true)
            {
                int numPostponed = Postponed.Count;
                if (numPostponed == 0)
                {
                    return true;
                }
                if (!ProcessPostponedStep())
                {
                    return false;
                }
                int numPostponed1 = Postponed.Count;
                if (numPostponed1 == 0)
                {
                    return true;
                }
                if (numPostponed1 < numPostponed)
                {
                    continue;
                }
                if (!mayPostpone && Config.UnivApprox && !_univApproxActive)
                {
                    _univApproxActive = true;
                    try
                    {
                        return Loop();
                    }
                    finally
                    {
                        _univApproxActive = false;
                    }
                }
                return mayPostpone;
            }
        }
    }

    /// <summary>
    /// Runs <paramref name="x"/> and processes the universe constraints it postponed, keeping its
    /// effects only if both succeed; otherwise the state is restored (Lean's <c>checkpointDefEq</c>).
    /// </summary>
    public bool CheckpointDefEq(Func<bool> x, bool mayPostpone = true)
    {
        ArgumentNullException.ThrowIfNull(x);
        var s = SaveState();
        // The transient cache must not survive between calls: results depend on the metavariable context.
        _defEqTransCache.Clear();
        var postponed = Postponed;
        Postponed = [];
        try
        {
            if (x() && ProcessPostponed(mayPostpone))
            {
                Postponed = postponed.AddRange(Postponed);
                return true;
            }
            Restore(s);
            return false;
        }
        catch
        {
            Restore(s);
            throw;
        }
    }

    /// <summary>Whether two universe levels are definitionally equal, assigning universe metavariables (Lean's <c>isLevelDefEq</c>).</summary>
    public bool IsLevelDefEq(Level u, Level v) => CheckpointDefEq(() => IsLevelDefEqAux(u, v), mayPostpone: true);
}
