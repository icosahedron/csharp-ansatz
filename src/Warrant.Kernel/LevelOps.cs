using Warrant.Cic;

namespace Warrant.Kernel;

/// <summary>
/// The universe-level algebra of the kernel: simplifying constructors, normalization, equivalence,
/// the <c>≥</c> test and parameter instantiation. A port of Lean 4's <c>src/kernel/level.cpp</c>.
/// </summary>
/// <remarks>
/// A universe metavariable is an opaque atom here, as in Lean's <c>Level.normalize</c>: it is never
/// zero, never instantiated, and ordered by its name. The kernel itself never sees one (it rejects
/// declarations that contain one); the Meta layer reuses these operations.
/// </remarks>
public static class LevelOps
{
    /// <summary>Whether <paramref name="l"/> is <c>succⁿ 0</c>.</summary>
    public static bool IsExplicit(Level l)
    {
        while (l.Kind == LevelKind.Succ)
        {
            l = l.Lhs!;
        }
        return l.Kind == LevelKind.Zero;
    }

    /// <summary>Splits <c>succᵏ l</c> into <c>(l, k)</c>, where <c>l</c> is not a successor.</summary>
    public static (Level Base, int Offset) ToOffset(Level l)
    {
        int k = 0;
        while (l.Kind == LevelKind.Succ)
        {
            l = l.Lhs!;
            k++;
        }
        return (l, k);
    }

    /// <summary><c>succᵏ l</c>.</summary>
    public static Level MkSucc(Level l, int k)
    {
        while (k-- > 0)
        {
            l = Level.Succ(l);
        }
        return l;
    }

    /// <summary><c>max l1 l2</c>, simplified where this is trivially sound (Lean's <c>mk_max</c>).</summary>
    public static Level MkMax(Level l1, Level l2)
    {
        if (IsExplicit(l1) && IsExplicit(l2))
        {
            return l1.Depth >= l2.Depth ? l1 : l2;
        }
        if (l1 == l2)
        {
            return l1;
        }
        if (l1.Kind == LevelKind.Zero)
        {
            return l2;
        }
        if (l2.Kind == LevelKind.Zero)
        {
            return l1;
        }
        if (l2.Kind == LevelKind.Max && (l2.Lhs == l1 || l2.Rhs == l1))
        {
            return l2; // max l1 (max l1 l') = max l1 l'
        }
        if (l1.Kind == LevelKind.Max && (l1.Lhs == l2 || l1.Rhs == l2))
        {
            return l1;
        }
        var p1 = ToOffset(l1);
        var p2 = ToOffset(l2);
        if (p1.Base == p2.Base)
        {
            return p1.Offset > p2.Offset ? l1 : l2;
        }
        return Level.Max(l1, l2);
    }

    /// <summary><c>imax l1 l2</c>, simplified where this is trivially sound (Lean's <c>mk_imax</c>).</summary>
    public static Level MkIMax(Level l1, Level l2)
    {
        if (IsNotZero(l2))
        {
            return MkMax(l1, l2);
        }
        if (l2.Kind == LevelKind.Zero)
        {
            return l2; // imax u 0 = 0
        }
        if (l1.Kind == LevelKind.Zero || l1 == Level.One)
        {
            return l2; // imax 0 u = imax 1 u = u
        }
        if (l1 == l2)
        {
            return l1;
        }
        return Level.IMax(l1, l2);
    }

    /// <summary>Whether <paramref name="l"/> is nonzero under every instantiation of its parameters.</summary>
    public static bool IsNotZero(Level l) => l.Kind switch
    {
        LevelKind.Succ => true,
        LevelKind.Max => IsNotZero(l.Lhs!) || IsNotZero(l.Rhs!),
        LevelKind.IMax => IsNotZero(l.Rhs!),
        LevelKind.MVar => false,
        _ => false,
    };

    /// <summary>Whether <paramref name="l"/> normalizes to zero (for example <c>imax 1 0</c>).</summary>
    public static bool NormalizesToZero(Level l) => l.Kind switch
    {
        LevelKind.Zero => true,
        LevelKind.Max => NormalizesToZero(l.Lhs!) && NormalizesToZero(l.Rhs!),
        LevelKind.IMax => NormalizesToZero(l.Rhs!),
        LevelKind.MVar => false,
        _ => false,
    };

    /// <summary>Lean's level normal form, used to decide equivalence.</summary>
    public static Level Normalize(Level l)
    {
        var (r, k) = ToOffset(l);
        switch (r.Kind)
        {
            case LevelKind.Zero:
            case LevelKind.Param:
            case LevelKind.MVar:
                return l;
            case LevelKind.IMax:
                return MkSucc(MkIMax(Normalize(r.Lhs!), Normalize(r.Rhs!)), k);
            case LevelKind.Max:
            {
                var todo = new List<Level>();
                var args = new List<Level>();
                PushMaxArgs(r, todo);
                foreach (var a in todo)
                {
                    PushMaxArgs(Normalize(a), args);
                }
                args.Sort(NormComparer.Instance);
                var rargs = new List<Level>();
                int i = 0;
                if (IsExplicit(args[i]))
                {
                    // Find the largest explicit universe.
                    while (i + 1 < args.Count && IsExplicit(args[i + 1]))
                    {
                        i++;
                    }
                    int kExplicit = ToOffset(args[i]).Offset;
                    // An explicit universe k is subsumed by succᵏ' l with k' >= k.
                    int j = i + 1;
                    for (; j < args.Count; j++)
                    {
                        if (ToOffset(args[j]).Offset >= kExplicit)
                        {
                            break;
                        }
                    }
                    if (j < args.Count)
                    {
                        i++;
                    }
                }
                rargs.Add(args[i]);
                var prev = ToOffset(args[i]);
                i++;
                for (; i < args.Count; i++)
                {
                    var curr = ToOffset(args[i]);
                    if (prev.Base == curr.Base)
                    {
                        if (prev.Offset < curr.Offset)
                        {
                            prev = curr;
                            rargs[^1] = args[i];
                        }
                    }
                    else
                    {
                        prev = curr;
                        rargs.Add(args[i]);
                    }
                }
                for (int m = 0; m < rargs.Count; m++)
                {
                    rargs[m] = MkSucc(rargs[m], k);
                }
                return MkMax(rargs);
            }
            default:
                throw new InvalidOperationException("unreachable: offset base is a successor");
        }
    }

    /// <summary>Whether two levels are equal for every instantiation of their parameters (sound, incomplete).</summary>
    public static bool IsEquivalent(Level lhs, Level rhs) => lhs == rhs || Normalize(lhs) == Normalize(rhs);

    /// <summary>Whether <c>l1 ≥ l2</c> for every instantiation of their parameters (sound, incomplete).</summary>
    public static bool IsGeq(Level l1, Level l2) => IsGeqCore(Normalize(l1), Normalize(l2));

    private static bool IsGeqCore(Level l1, Level l2)
    {
        if (l1 == l2 || l2.Kind == LevelKind.Zero)
        {
            return true;
        }
        if (l2.Kind == LevelKind.Max)
        {
            return IsGeq(l1, l2.Lhs!) && IsGeq(l1, l2.Rhs!);
        }
        if (l1.Kind == LevelKind.Max && (IsGeq(l1.Lhs!, l2) || IsGeq(l1.Rhs!, l2)))
        {
            return true;
        }
        if (l2.Kind == LevelKind.IMax)
        {
            return IsGeq(l1, l2.Lhs!) && IsGeq(l1, l2.Rhs!);
        }
        if (l1.Kind == LevelKind.IMax)
        {
            return IsGeq(l1.Rhs!, l2);
        }
        var p1 = ToOffset(l1);
        var p2 = ToOffset(l2);
        if (p1.Base == p2.Base || p2.Base.Kind == LevelKind.Zero)
        {
            return p1.Offset >= p2.Offset;
        }
        if (p1.Offset == p2.Offset && p1.Offset > 0)
        {
            return IsGeq(p1.Base, p2.Base);
        }
        return false;
    }

    /// <summary>Substitutes <paramref name="levels"/> for the parameters <paramref name="names"/>.</summary>
    public static Level Instantiate(Level l, EquatableArray<Name> names, EquatableArray<Level> levels)
    {
        if (!l.HasParam)
        {
            return l;
        }
        switch (l.Kind)
        {
            case LevelKind.Param:
                int n = Math.Min(names.Count, levels.Count);
                for (int i = 0; i < n; i++)
                {
                    if (names[i] == l.ParamName)
                    {
                        return levels[i];
                    }
                }
                return l;
            case LevelKind.Succ:
            {
                var a = Instantiate(l.Lhs!, names, levels);
                return ReferenceEquals(a, l.Lhs) ? l : Level.Succ(a);
            }
            case LevelKind.Max:
            case LevelKind.IMax:
            {
                var a = Instantiate(l.Lhs!, names, levels);
                var b = Instantiate(l.Rhs!, names, levels);
                if (ReferenceEquals(a, l.Lhs) && ReferenceEquals(b, l.Rhs))
                {
                    return l;
                }
                return l.Kind == LevelKind.Max ? MkMax(a, b) : MkIMax(a, b);
            }
            case LevelKind.MVar:
                return l;
            default:
                return l;
        }
    }

    /// <summary>A parameter of <paramref name="l"/> not among <paramref name="names"/>, if any.</summary>
    public static Name? GetUndefinedParam(Level l, EquatableArray<Name> names)
    {
        if (!l.HasParam)
        {
            return null;
        }
        switch (l.Kind)
        {
            case LevelKind.Param:
                foreach (var n in names)
                {
                    if (n == l.ParamName)
                    {
                        return null;
                    }
                }
                return l.ParamName;
            case LevelKind.Succ:
                return GetUndefinedParam(l.Lhs!, names);
            case LevelKind.MVar:
                return null;
            default:
                return GetUndefinedParam(l.Lhs!, names) ?? GetUndefinedParam(l.Rhs!, names);
        }
    }

    /// <summary>The levels <c>u₁ … uₙ</c> for parameter names <c>u₁ … uₙ</c>.</summary>
    public static EquatableArray<Level> ParamsToLevels(EquatableArray<Name> names) =>
        names.Select(Level.Param).ToEquatableArray();

    private static void PushMaxArgs(Level l, List<Level> result)
    {
        if (l.Kind == LevelKind.Max)
        {
            PushMaxArgs(l.Lhs!, result);
            PushMaxArgs(l.Rhs!, result);
        }
        else
        {
            result.Add(l);
        }
    }

    private static Level MkMax(List<Level> args)
    {
        int n = args.Count;
        if (n == 1)
        {
            return args[0];
        }
        var r = MkMax(args[n - 2], args[n - 1]);
        for (int i = n - 2; i > 0;)
        {
            --i;
            r = MkMax(args[i], r);
        }
        return r;
    }

    /// <summary>
    /// The total order used by normalization: <c>succ l</c> is the immediate successor of <c>l</c>,
    /// and zero is the least element.
    /// </summary>
    private sealed class NormComparer : IComparer<Level>
    {
        public static readonly NormComparer Instance = new();

        public int Compare(Level? a, Level? b)
        {
            if (ReferenceEquals(a, b))
            {
                return 0;
            }
            return IsNormLt(a!, b!) ? -1 : IsNormLt(b!, a!) ? 1 : 0;
        }

        private static bool IsNormLt(Level a, Level b)
        {
            if (ReferenceEquals(a, b))
            {
                return false;
            }
            var (l1, k1) = ToOffset(a);
            var (l2, k2) = ToOffset(b);
            if (l1 != l2)
            {
                if (l1.Kind != l2.Kind)
                {
                    return l1.Kind < l2.Kind;
                }
                switch (l1.Kind)
                {
                    case LevelKind.Param:
                        return l1.ParamName!.CompareTo(l2.ParamName) < 0;
                    case LevelKind.MVar:
                        return l1.MVarId!.Value.Name.CompareTo(l2.MVarId!.Value.Name) < 0;
                    case LevelKind.Max:
                    case LevelKind.IMax:
                        return l1.Lhs != l2.Lhs ? IsNormLt(l1.Lhs!, l2.Lhs!) : IsNormLt(l1.Rhs!, l2.Rhs!);
                    default:
                        throw new InvalidOperationException("unreachable level kind in normalization order");
                }
            }
            return k1 < k2;
        }
    }
}
