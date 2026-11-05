using System.Collections.Immutable;
using System.Globalization;
using System.Numerics;
using System.Text;
using Warrant.Cic;
using Warrant.Kernel;

namespace Warrant.Meta;

// A port of Lean 4.35.0's discrimination trees (Lean/Meta/DiscrTree/{Types,Basic,Main}.lean): the
// index from term shapes to simp lemmas and instances (plan U16, KTD9; docs/m5a/05 "Discrimination
// trees"). Keys are computed at `reducible` transparency; instance-implicit arguments, proofs and
// non-type implicit arguments are wildcards; `OfNat.ofNat _ n _` keys as the literal `n`; a term
// annotated `no_index` keys as `*`.
//
// Lean orders a node's children with `Key.lt`, which compares names with `Name.quickLt` (by hash);
// this port orders them with `Name.CompareTo`. Only the order in which candidates are returned can
// differ, and both callers (simp's rewrite and instance resolution) sort candidates by priority
// with a stable sort, as Lean does.

/// <summary>The kinds of <see cref="DiscrTreeKey"/>, in the order of Lean's constructors (<c>star</c> is the least).</summary>
public enum DiscrTreeKeyKind
{
    /// <summary>A wildcard: a metavariable, or an argument the tree ignores.</summary>
    Star,

    /// <summary>Any other term: a sort, a lambda, a read-only metavariable.</summary>
    Other,

    /// <summary>A literal.</summary>
    Lit,

    /// <summary>A free variable with its number of arguments.</summary>
    FVar,

    /// <summary>A constant with its number of arguments (universe levels are ignored).</summary>
    Const,

    /// <summary>A <c>∀</c> (or <c>→</c>), whose domain follows.</summary>
    Arrow,

    /// <summary>A projection, with its structure, field index and number of arguments.</summary>
    Proj,
}

/// <summary>A discrimination-tree key (Lean's <c>DiscrTree.Key</c>).</summary>
/// <param name="Kind">The kind.</param>
/// <param name="Name">The constant, or the projection's structure.</param>
/// <param name="FVarId">The free variable.</param>
/// <param name="Literal">The literal (a <see cref="NatLitExpr"/> or <see cref="StrLitExpr"/>).</param>
/// <param name="Index">The projection's field index.</param>
/// <param name="NumArgs">The number of arguments of a constant, free variable or projection.</param>
public sealed record DiscrTreeKey(DiscrTreeKeyKind Kind, Name? Name = null, FVarId? FVarId = null, Expr? Literal = null, int Index = 0, int NumArgs = 0)
{
    /// <summary>Orders keys with <see cref="CompareTo"/>.</summary>
    public static IComparer<DiscrTreeKey> Comparer { get; } = Comparer<DiscrTreeKey>.Create((a, b) => a.CompareTo(b));

    /// <summary>The wildcard key.</summary>
    public static DiscrTreeKey Star { get; } = new(DiscrTreeKeyKind.Star);

    /// <summary>The key of any other term.</summary>
    public static DiscrTreeKey Other { get; } = new(DiscrTreeKeyKind.Other);

    /// <summary>The key of a <c>∀</c>.</summary>
    public static DiscrTreeKey Arrow { get; } = new(DiscrTreeKeyKind.Arrow);

    /// <summary>A constant key.</summary>
    public static DiscrTreeKey Const(Name name, int numArgs) => new(DiscrTreeKeyKind.Const, Name: name, NumArgs: numArgs);

    /// <summary>A free-variable key.</summary>
    public static DiscrTreeKey FVar(FVarId fvarId, int numArgs) => new(DiscrTreeKeyKind.FVar, FVarId: fvarId, NumArgs: numArgs);

    /// <summary>A literal key.</summary>
    public static DiscrTreeKey Lit(Expr literal) => new(DiscrTreeKeyKind.Lit, Literal: literal);

    /// <summary>A natural-number literal key.</summary>
    public static DiscrTreeKey NatLit(BigInteger n) => Lit(Expr.NatLit(n));

    /// <summary>A projection key.</summary>
    public static DiscrTreeKey Proj(Name structName, int index, int numArgs) => new(DiscrTreeKeyKind.Proj, Name: structName, Index: index, NumArgs: numArgs);

    /// <summary>How many subterms follow this key in a path (Lean's <c>Key.arity</c>).</summary>
    public int Arity => Kind switch
    {
        DiscrTreeKeyKind.Const or DiscrTreeKeyKind.FVar => NumArgs,
        DiscrTreeKeyKind.Arrow => 1,
        DiscrTreeKeyKind.Proj => 1 + NumArgs,
        _ => 0,
    };

    /// <summary>The key as Lean's <c>DiscrTree.Key.format</c> prints it (without arity).</summary>
    public string Format() => Kind switch
    {
        DiscrTreeKeyKind.Star => "*",
        DiscrTreeKeyKind.Other => "◾",
        DiscrTreeKeyKind.Lit => Literal switch
        {
            NatLitExpr n => n.Value.ToString(CultureInfo.InvariantCulture),
            StrLitExpr s => Quote(s.Value),
            _ => "?",
        },
        DiscrTreeKeyKind.Const => Name!.ToString(),
        DiscrTreeKeyKind.Proj => $"{Name}.{Index}",
        DiscrTreeKeyKind.FVar => FVarId!.Value.Name.ToString(),
        _ => "∀",
    };

    /// <inheritdoc/>
    public override string ToString() => Kind is DiscrTreeKeyKind.Const or DiscrTreeKeyKind.FVar or DiscrTreeKeyKind.Proj
        ? $"{Format()}/{NumArgs}"
        : Format();

    /// <summary>A total order with <see cref="Star"/> least (Lean's <c>Key.lt</c>, comparing names by <see cref="Name.CompareTo"/>).</summary>
    public int CompareTo(DiscrTreeKey? other)
    {
        if (other is null)
        {
            return 1;
        }
        if (Kind != other.Kind)
        {
            return Kind.CompareTo(other.Kind);
        }
        switch (Kind)
        {
            case DiscrTreeKeyKind.Lit:
                return (Literal, other.Literal) switch
                {
                    (NatLitExpr a, NatLitExpr b) => a.Value.CompareTo(b.Value),
                    (StrLitExpr a, StrLitExpr b) => string.CompareOrdinal(a.Value, b.Value),
                    (NatLitExpr, _) => -1,
                    _ => 1,
                };
            case DiscrTreeKeyKind.Const:
            {
                int c = Name!.CompareTo(other.Name);
                return c != 0 ? c : NumArgs.CompareTo(other.NumArgs);
            }
            case DiscrTreeKeyKind.FVar:
            {
                int c = FVarId!.Value.Name.CompareTo(other.FVarId!.Value.Name);
                return c != 0 ? c : NumArgs.CompareTo(other.NumArgs);
            }
            case DiscrTreeKeyKind.Proj:
            {
                int c = Name!.CompareTo(other.Name);
                if (c != 0)
                {
                    return c;
                }
                c = Index.CompareTo(other.Index);
                return c != 0 ? c : NumArgs.CompareTo(other.NumArgs);
            }
            default:
                return 0;
        }
    }

    // Lean's String.quote.
    private static string Quote(string s)
    {
        var sb = new StringBuilder("\"");
        foreach (var ch in s)
        {
            switch (ch)
            {
                case '\n': sb.Append("\\n"); break;
                case '\t': sb.Append("\\t"); break;
                case '\\': sb.Append("\\\\"); break;
                case '"': sb.Append("\\\""); break;
                default:
                    if (ch < ' ' || ch == '\u007f')
                    {
                        sb.Append("\\x").Append(((int)ch).ToString("x2", CultureInfo.InvariantCulture));
                    }
                    else
                    {
                        sb.Append(ch);
                    }
                    break;
            }
        }
        return sb.Append('"').ToString();
    }
}

/// <summary>
/// A discrimination tree (Lean's <c>DiscrTree</c>): an index from term shapes to values, which
/// returns, for a term, the values whose key path may match it (<see cref="GetMatch"/>) or unify with
/// it (<see cref="GetUnify"/>). Retrieval is imperfect: candidates must still be checked with
/// <c>isDefEq</c>.
/// </summary>
/// <typeparam name="T">The values.</typeparam>
public sealed class DiscrTree<T>
{
    private readonly Dictionary<DiscrTreeKey, Trie> _root = [];

    /// <summary>The number of values (Lean's <c>DiscrTree.size</c>).</summary>
    public int Count { get; private set; }

    /// <summary>
    /// Adds <paramref name="value"/> under <paramref name="keys"/>, replacing an equal value already
    /// there (Lean's <c>insertKeyValue</c>).
    /// </summary>
    /// <exception cref="ArgumentException">The key sequence is empty.</exception>
    public void Insert(IReadOnlyList<DiscrTreeKey> keys, T value)
    {
        ArgumentNullException.ThrowIfNull(keys);
        if (keys.Count == 0)
        {
            throw new ArgumentException("invalid key sequence", nameof(keys));
        }
        if (!_root.TryGetValue(keys[0], out var node))
        {
            _root[keys[0]] = node = new Trie();
        }
        for (int i = 1; i < keys.Count; i++)
        {
            node = node.Child(keys[i], create: true)!;
        }
        int j = node.Values.FindIndex(v => EqualityComparer<T>.Default.Equals(v, value));
        if (j >= 0)
        {
            node.Values[j] = value;
        }
        else
        {
            node.Values.Add(value);
            Count++;
        }
    }

    /// <summary>Adds <paramref name="value"/> under the path of <paramref name="e"/> (Lean's <c>insert</c>).</summary>
    public void Insert(MetaM m, Expr e, T value, bool noIndexAtArgs = false) =>
        Insert(DiscrTree.MkPath(m, e, noIndexAtArgs), value);

    /// <summary>The values whose path matches <paramref name="e"/>, without assigning its metavariables (Lean's <c>getMatch</c>).</summary>
    public IReadOnlyList<T> GetMatch(MetaM m, Expr e)
    {
        ArgumentNullException.ThrowIfNull(m);
        ArgumentNullException.ThrowIfNull(e);
        return GetMatchCore(m, e).Result;
    }

    /// <summary>
    /// Like <see cref="GetMatch"/>, also returning values that match a prefix <c>f a₁ … aₖ</c> of
    /// <paramref name="e"/> = <c>f a₁ … aₙ</c>, with the number <c>n - k</c> of extra arguments
    /// (Lean's <c>getMatchWithExtra</c>).
    /// </summary>
    public IReadOnlyList<(T Value, int NumExtra)> GetMatchWithExtra(MetaM m, Expr e)
    {
        ArgumentNullException.ThrowIfNull(m);
        ArgumentNullException.ThrowIfNull(e);
        var (k, first) = GetMatchCore(m, e);
        var result = first.Select(v => (v, 0)).ToList();
        if (e is not AppExpr || !MayMatchPrefix(k))
        {
            return result;
        }
        int numExtra = 1;
        for (var f = ((AppExpr)e).Fn; ; f = ((AppExpr)f).Fn, numExtra++)
        {
            int n = numExtra;
            result.AddRange(GetMatchCore(m, f).Result.Select(v => (v, n)));
            if (f is not AppExpr)
            {
                return result;
            }
        }
    }

    /// <summary>The values whose path may unify with <paramref name="e"/> (Lean's <c>getUnify</c>).</summary>
    /// <exception cref="IsDefEqStuckException">With <see cref="MetaConfig.IsDefEqStuckEx"/>, <paramref name="e"/> is stuck on a metavariable.</exception>
    public IReadOnlyList<T> GetUnify(MetaM m, Expr e)
    {
        ArgumentNullException.ThrowIfNull(m);
        ArgumentNullException.ThrowIfNull(e);
        return m.WithReducible(() =>
        {
            var (k, args) = DiscrTree.GetKeyArgs(m, e, isMatch: false, root: true);
            var result = new List<T>();
            if (k.Kind == DiscrTreeKeyKind.Star)
            {
                foreach (var (key, c) in _root.OrderBy(kv => kv.Key, DiscrTreeKey.Comparer))
                {
                    Process(key.Arity, [], c);
                }
                return result;
            }
            AddStarResult(result);
            if (_root.TryGetValue(k, out var node))
            {
                Process(0, args, node);
            }
            return result;

            void Process(int skip, ImmutableList<Expr> todo, Trie c)
            {
                if (skip > 0)
                {
                    foreach (var (key, child) in c.Children)
                    {
                        Process(skip - 1 + key.Arity, todo, child);
                    }
                    return;
                }
                if (todo.IsEmpty)
                {
                    result.AddRange(c.Values);
                    return;
                }
                if (c.Children.Count == 0)
                {
                    return;
                }
                var next = todo[^1];
                var rest = todo.RemoveAt(todo.Count - 1);
                var (k1, args1) = DiscrTree.GetKeyArgs(m, next, isMatch: false, root: false);
                if (k1.Kind == DiscrTreeKeyKind.Star)
                {
                    foreach (var (key, child) in c.Children)
                    {
                        Process(key.Arity, rest, child);
                    }
                    return;
                }
                if (c.Children[0].Key.Kind == DiscrTreeKeyKind.Star)
                {
                    Process(0, rest, c.Children[0].Child);
                }
                if (c.Child(k1, create: false) is { } found)
                {
                    Process(0, rest.AddRange(args1), found);
                }
            }
        });
    }

    private bool MayMatchPrefix(DiscrTreeKey k)
    {
        while (k.Kind is DiscrTreeKeyKind.Const or DiscrTreeKeyKind.FVar or DiscrTreeKeyKind.Proj && k.NumArgs > 0)
        {
            k = k with { NumArgs = k.NumArgs - 1 };
            if (_root.ContainsKey(k))
            {
                return true;
            }
        }
        return false;
    }

    private void AddStarResult(List<T> result)
    {
        if (_root.TryGetValue(DiscrTreeKey.Star, out var star))
        {
            result.AddRange(star.Values);
        }
    }

    private (DiscrTreeKey Key, List<T> Result) GetMatchCore(MetaM m, Expr e) => m.WithReducible(() =>
    {
        var result = new List<T>();
        AddStarResult(result);
        var (k, args) = DiscrTree.GetKeyArgs(m, e, isMatch: true, root: true);
        if (k.Kind != DiscrTreeKeyKind.Star && _root.TryGetValue(k, out var node))
        {
            GetMatchLoop(m, args, node, result);
        }
        return (k, result);
    });

    private static void GetMatchLoop(MetaM m, ImmutableList<Expr> todo, Trie c, List<T> result)
    {
        if (todo.IsEmpty)
        {
            result.AddRange(c.Values);
            return;
        }
        if (c.Children.Count == 0)
        {
            return;
        }
        var e = todo[^1];
        var rest = todo.RemoveAt(todo.Count - 1);
        var (k, args) = DiscrTree.GetKeyArgs(m, e, isMatch: true, root: false);
        // A star edge is a wildcard and is always visited.
        if (c.Children[0].Key.Kind == DiscrTreeKeyKind.Star)
        {
            GetMatchLoop(m, rest, c.Children[0].Child, result);
        }
        if (k.Kind != DiscrTreeKeyKind.Star && c.Child(k, create: false) is { } found)
        {
            GetMatchLoop(m, rest.AddRange(args), found, result);
        }
    }

    // Lean's Trie: values here, and children sorted by key.
    private sealed class Trie
    {
        public List<T> Values { get; } = [];

        public List<(DiscrTreeKey Key, Trie Child)> Children { get; } = [];

        public Trie? Child(DiscrTreeKey k, bool create)
        {
            int lo = 0, hi = Children.Count;
            while (lo < hi)
            {
                int mid = (lo + hi) / 2;
                int c = Children[mid].Key.CompareTo(k);
                if (c == 0)
                {
                    return Children[mid].Child;
                }
                if (c < 0)
                {
                    lo = mid + 1;
                }
                else
                {
                    hi = mid;
                }
            }
            if (!create)
            {
                return null;
            }
            var t = new Trie();
            Children.Insert(lo, (k, t));
            return t;
        }
    }
}

/// <summary>Key computation for <see cref="DiscrTree{T}"/> (Lean/Meta/DiscrTree/Main.lean).</summary>
public static class DiscrTree
{
    private const string NoIndexKey = "noindex";

    // Lean's tmpStar: the mark for ignored arguments.
    private static readonly MVarExpr TmpStar = Expr.MVar(new MVarId(Name.From("_discr_tree_tmp")));

    private static readonly Name NatAddName = Name.From("Nat", "add");
    private static readonly Name AddAddName = Name.From("Add", "add");

    // lean4export writes a KVMap value as its Lean DataValue, so a true Bool is "Lean.DataValue.ofBool true".
    private const string TrueValue = "Lean.DataValue.ofBool true";

    /// <summary><c>no_index e</c> (Lean's <c>mkNoindexAnnotation</c>), with the value spelled as lean4export writes it.</summary>
    public static Expr MkNoIndexAnnotation(Expr e) => Expr.MData(new KVMap([new KVMapEntry(NoIndexKey, TrueValue)]), e);

    /// <summary>
    /// Whether <paramref name="e"/> is <c>no_index _</c> (Lean's <c>hasNoindexAnnotation</c>: a single <c>noindex</c> entry whose Bool is true).
    /// Accepts the lean4export spelling and a bare <c>true</c>.
    /// </summary>
    public static bool HasNoIndexAnnotation(Expr e) =>
        e is MDataExpr m && m.Data.Entries.Count == 1 && m.Data.Entries[0] is { Key: NoIndexKey, Value: TrueValue or "true" };

    /// <summary>The key path of <paramref name="e"/>, computed at <c>reducible</c> transparency (Lean's <c>mkPath</c>).</summary>
    /// <param name="m">The Meta computation.</param>
    /// <param name="e">The term.</param>
    /// <param name="noIndexAtArgs">Index every argument as if it were <c>no_index</c> (for local hypotheses).</param>
    public static ImmutableArray<DiscrTreeKey> MkPath(MetaM m, Expr e, bool noIndexAtArgs = false)
    {
        ArgumentNullException.ThrowIfNull(m);
        ArgumentNullException.ThrowIfNull(e);
        return m.WithReducible(() =>
        {
            var todo = new List<Expr> { e };
            var keys = ImmutableArray.CreateBuilder<DiscrTreeKey>();
            bool root = true;
            while (todo.Count > 0)
            {
                var next = todo[^1];
                todo.RemoveAt(todo.Count - 1);
                keys.Add(PushArgs(m, root, todo, next, noIndexAtArgs));
                root = false;
            }
            return keys.ToImmutable();
        });
    }

    /// <summary>
    /// The discrimination tree's <c>whnf</c> (Lean's <c>reduceDT</c>): <c>whnfCore</c> and unfolding
    /// at the current transparency, with strict eta; at the root, stops before an unfolding whose head
    /// would be a bad key.
    /// </summary>
    public static Expr ReduceDT(MetaM m, Expr e, bool root)
    {
        ArgumentNullException.ThrowIfNull(m);
        ArgumentNullException.ThrowIfNull(e);
        return root ? ReduceUntilBadKey(m, e) : Reduce(m, e);
    }

    private static Expr? EtaExpandedStrict(Expr e) => e is LamExpr ? e.EtaExpanded() : null;

    private static Expr Reduce(MetaM m, Expr e)
    {
        while (true)
        {
            e = m.WhnfCore(e);
            if (m.UnfoldDefinition(e) is { } u)
            {
                e = u;
            }
            else if (EtaExpandedStrict(e) is { } x)
            {
                e = x;
            }
            else
            {
                return e;
            }
        }
    }

    private static Expr ReduceUntilBadKey(MetaM m, Expr e)
    {
        while (true)
        {
            e = Step(e);
            if (EtaExpandedStrict(e) is { } x)
            {
                e = x;
                continue;
            }
            return e;
        }

        Expr Step(Expr e)
        {
            while (true)
            {
                e = m.WhnfCore(e);
                if (m.UnfoldDefinition(e) is not { } e1 || IsBadKey(e1.GetAppFn()))
                {
                    return e;
                }
                e = e1;
            }
        }
    }

    private static bool IsBadKey(Expr fn) => fn is not (NatLitExpr or StrLitExpr or ConstExpr or FVarExpr or ProjExpr or ForallExpr);

    private static bool IgnoreArg(MetaM m, Expr a, int i, ImmutableArray<ParamInfo> infos)
    {
        if (i < infos.Length)
        {
            var info = infos[i];
            if (info.IsInstance)
            {
                return true;
            }
            if (info.BinderInfo is BinderInfo.Implicit or BinderInfo.StrictImplicit)
            {
                return !m.IsType(a);
            }
        }
        return m.IsProof(a);
    }

    private static void PushArgsAux(MetaM m, ImmutableArray<ParamInfo> infos, int i, Expr e, List<Expr> todo)
    {
        while (e is AppExpr a)
        {
            todo.Add(IgnoreArg(m, a.Arg, i, infos) ? TmpStar : a.Arg);
            i = Math.Max(i - 1, 0);
            e = a.Fn;
        }
    }

    private static bool IsNumeral(Expr e)
    {
        while (true)
        {
            if (e is NatLitExpr)
            {
                return true;
            }
            if (e.GetAppFn() is not ConstExpr f)
            {
                return false;
            }
            int n = e.GetAppNumArgs();
            if (f.Name == MetaNames.NatSucc && n == 1)
            {
                e = ((AppExpr)e).Arg;
            }
            else if (f.Name == MetaNames.OfNatOfNat && n == 3)
            {
                e = e.GetAppArgs()[1];
            }
            else
            {
                return f.Name == MetaNames.NatZero && n == 0;
            }
        }
    }

    // Lean's toNatLit?.
    private static BigInteger? ToNatLit(Expr e)
    {
        if (!IsNumeral(e))
        {
            return null;
        }
        BigInteger k = 0;
        while (true)
        {
            switch (e.GetAppFn())
            {
                case NatLitExpr lit:
                    return lit.Value + k;
                case ConstExpr f:
                {
                    int n = e.GetAppNumArgs();
                    if (f.Name == MetaNames.NatSucc && n == 1)
                    {
                        k++;
                        e = ((AppExpr)e).Arg;
                    }
                    else if (f.Name == MetaNames.OfNatOfNat && n == 3)
                    {
                        e = e.GetAppArgs()[1];
                    }
                    else if (f.Name == MetaNames.NatZero && n == 0)
                    {
                        return k;
                    }
                    else
                    {
                        return null;
                    }
                    break;
                }
                default:
                    return null;
            }
        }
    }

    private static bool IsNatType(MetaM m, Expr e) => m.Whnf(e).IsConstOf(MetaNames.Nat);

    // Lean's isOffset (via shouldAddAsStar): offset terms key as `*`.
    private static bool ShouldAddAsStar(MetaM m, Name fName, Expr e)
    {
        int n = e.GetAppNumArgs();
        if (fName == NatAddName && n == 2)
        {
            return IsNumeral(((AppExpr)e).Arg);
        }
        if (fName == AddAddName && n == 4)
        {
            return IsNatType(m, e.GetAppArgs()[0]) && IsNumeral(((AppExpr)e).Arg);
        }
        if (fName == MetaNames.HAddHAdd && n == 6)
        {
            return IsNatType(m, e.GetAppArgs()[1]) && IsNumeral(((AppExpr)e).Arg);
        }
        return fName == MetaNames.NatSucc && n == 1;
    }

    private static DiscrTreeKey PushArgs(MetaM m, bool root, List<Expr> todo, Expr e, bool noIndexAtArgs)
    {
        if (HasNoIndexAnnotation(e) || ReferenceEquals(e, TmpStar))
        {
            return DiscrTreeKey.Star;
        }
        e = ReduceDT(m, e, root);
        var fn = e.GetAppFn();
        switch (fn)
        {
            case NatLitExpr or StrLitExpr:
                return DiscrTreeKey.Lit(fn);
            case ConstExpr c:
            {
                if (!root)
                {
                    if (ToNatLit(e) is { } v)
                    {
                        return DiscrTreeKey.NatLit(v);
                    }
                    if (ShouldAddAsStar(m, c.Name, e))
                    {
                        return DiscrTreeKey.Star;
                    }
                }
                int nargs = e.GetAppNumArgs();
                return Push(DiscrTreeKey.Const(c.Name, nargs), nargs);
            }
            case ProjExpr p:
            {
                // A class projection's structure is an instance, which is not indexed.
                var a = m.Attributes.IsClass(p.TypeName) ? MkNoIndexAnnotation(p.Struct) : p.Struct;
                int nargs = e.GetAppNumArgs();
                todo.Add(a);
                return Push(DiscrTreeKey.Proj(p.TypeName, p.Index, nargs), nargs);
            }
            case FVarExpr f:
            {
                int nargs = e.GetAppNumArgs();
                return Push(DiscrTreeKey.FVar(f.Id, nargs), nargs);
            }
            case MVarExpr mv:
                return mv.Id == TmpStar.Id ? DiscrTreeKey.Star
                    : m.IsReadOnlyOrSyntheticOpaque(mv.Id) ? DiscrTreeKey.Other
                    : DiscrTreeKey.Star;
            case ForallExpr f:
                todo.Add(f.BinderType);
                return DiscrTreeKey.Arrow;
            default:
                return DiscrTreeKey.Other;
        }

        DiscrTreeKey Push(DiscrTreeKey k, int nargs)
        {
            var info = m.GetFunInfoNArgs(fn, nargs);
            if (noIndexAtArgs)
            {
                for (int i = 0; i < nargs; i++)
                {
                    todo.Add(TmpStar);
                }
            }
            else
            {
                PushArgsAux(m, info.ParamInfo, nargs - 1, e, todo);
            }
            return k;
        }
    }

    /// <summary>
    /// The key of a query term and its subterms still to visit, last first (Lean's <c>getKeyArgs</c>).
    /// With <paramref name="isMatch"/>, a metavariable keys as <see cref="DiscrTreeKey.Other"/>, since
    /// matching does not assign the query's metavariables.
    /// </summary>
    internal static (DiscrTreeKey Key, ImmutableList<Expr> Args) GetKeyArgs(MetaM m, Expr e, bool isMatch, bool root)
    {
        e = ReduceDT(m, e, root);
        if (!root && ToNatLit(e) is { } v)
        {
            return (DiscrTreeKey.NatLit(v), []);
        }
        switch (e.GetAppFn())
        {
            case NatLitExpr or StrLitExpr:
                return (DiscrTreeKey.Lit(e.GetAppFn()), []);
            case ConstExpr c:
            {
                if (m.Config.IsDefEqStuckEx && e.HasExprMVar)
                {
                    // `c …` did not unfold or reduce because of metavariables: postpone instance resolution.
                    if (m.IsReducible(c.Name))
                    {
                        throw new IsDefEqStuckException();
                    }
                    if (m.GetMatcherInfo(c.Name) is { } info && e.GetAppNumArgs() >= info.Arity)
                    {
                        var args = e.GetAppArgs();
                        for (int i = info.FirstDiscrPos; i < info.FirstDiscrPos + info.NumDiscrs; i++)
                        {
                            if (args[i].HasExprMVar)
                            {
                                throw new IsDefEqStuckException();
                            }
                        }
                    }
                    else if (m.Env.Find(c.Name) is RecursorInfo)
                    {
                        throw new IsDefEqStuckException();
                    }
                }
                return (DiscrTreeKey.Const(c.Name, e.GetAppNumArgs()), [.. e.GetAppRevArgs()]);
            }
            case FVarExpr f:
                return (DiscrTreeKey.FVar(f.Id, e.GetAppNumArgs()), [.. e.GetAppRevArgs()]);
            case MVarExpr mv:
                if (isMatch)
                {
                    return (DiscrTreeKey.Other, []);
                }
                // With isDefEqStuckEx, a read-only metavariable may be assigned later: a wildcard.
                return (m.Config.IsDefEqStuckEx || !m.IsReadOnlyOrSyntheticOpaque(mv.Id) ? DiscrTreeKey.Star : DiscrTreeKey.Other, []);
            case ProjExpr p:
                return (DiscrTreeKey.Proj(p.TypeName, p.Index, e.GetAppNumArgs()), [p.Struct, .. e.GetAppRevArgs()]);
            case ForallExpr f:
                return (DiscrTreeKey.Arrow, [f.BinderType]);
            default:
                return (DiscrTreeKey.Other, []);
        }
    }
}

// The keys of a simp lemma (Lean/Meta/Tactic/Simp/SimpTheorems.lean: mkSimpTheoremFromConst,
// preprocess, mkSimpTheoremKeys), on types only; simp (U17) builds the proofs.
public sealed partial class MetaM
{
    private static readonly Name EqName = Name.From("Eq");
    private static readonly Name IffName = Name.From("Iff");
    private static readonly Name NeName = Name.From("Ne");
    private static readonly Name NotName = Name.From("Not");
    private static readonly Name AndName = Name.From("And");
    private static readonly Name TrueName = Name.From("True");
    private static readonly Name BoolName = Name.From("Bool");
    private static readonly Name FalseName = Name.From("False");

    /// <summary>
    /// The discrimination-tree keys Lean gives the simp lemma <paramref name="declName"/>, one path per
    /// simp theorem it makes (a conjunction makes several), computed from its kernel-checked type
    /// with Lean's preprocessing (<c>↔</c> to <c>=</c>, <c>¬p</c> to <c>p = False</c>, <c>p</c> to
    /// <c>p = True</c>, conjunctions split, <paramref name="inverse"/> swaps the sides) under
    /// <c>simpGlobalConfig</c> (reducible, no iota, no projection reduction, no zeta-delta).
    /// </summary>
    /// <exception cref="MetaException">The lemma is unknown, or not of a form simp accepts.</exception>
    public IReadOnlyList<ImmutableArray<DiscrTreeKey>> MkSimpTheoremKeys(Name declName, bool inverse = false)
    {
        ArgumentNullException.ThrowIfNull(declName);
        var type = GetConstInfo(declName).Type;
        return WithConfig(
            c => c with { Iota = false, Proj = ProjReductionKind.No, ZetaDelta = false, Transparency = TransparencyMode.Reducible },
            () =>
            {
                var types = inverse || ShouldPreprocessSimp(type) ? PreprocessSimp(type, inverse) : [type];
                return types.Select(t => SimpTheoremKeys(t)).ToList();
            });
    }

    private static (Expr Lhs, Expr Rhs)? EqSides(Expr e) =>
        ExprOps.IsAppOfArity(e, EqName, 3) ? (((AppExpr)((AppExpr)e).Fn).Arg, ((AppExpr)e).Arg) : null;

    private static Expr MkEqAt(Level u, Expr type, Expr lhs, Expr rhs) =>
        Expr.App(Expr.Const(EqName, u), type, lhs, rhs);

    private static Expr MkPropEq(Expr lhs, Expr rhs) => MkEqAt(Level.One, Expr.Prop, lhs, rhs);

    private static Expr MkBoolEq(Expr lhs, bool rhs) => MkEqAt(Level.One, Expr.Const(BoolName), lhs, MetaNames.MkBool(rhs));

    internal bool ShouldPreprocessSimp(Expr type) =>
        ForallTelescopeReducing(type, (_, result) => EqSides(result) is null);

    private List<Expr> PreprocessSimp(Expr type, bool inv)
    {
        type = Whnf(type);
        if (type is ForallExpr)
        {
            return ForallTelescopeReducing(type, (xs, body) =>
                PreprocessSimp(body, inv).Select(t => MkForallFVars(xs, t)).ToList());
        }
        if (ExprOps.IsAppOfArity(type, EqName, 3))
        {
            var args = type.GetAppArgs();
            return [inv ? MkEqAt(((ConstExpr)type.GetAppFn()).Levels[0], args[0], args[2], args[1]) : type];
        }
        if (ExprOps.IsAppOfArity(type, IffName, 2))
        {
            var args = type.GetAppArgs();
            return [inv ? MkPropEq(args[1], args[0]) : MkPropEq(args[0], args[1])];
        }
        if (ExprOps.IsAppOfArity(type, NeName, 3))
        {
            var args = type.GetAppArgs();
            if (inv)
            {
                throw new MetaException("Invalid `←` modifier: cannot be applied to simp theorems of the form `a ≠ b`");
            }
            return [NegatedEq(args[0], args[1], args[2], ((ConstExpr)type.GetAppFn()).Levels[0])];
        }
        if (ExprOps.IsAppOfArity(type, NotName, 1))
        {
            if (inv)
            {
                throw new MetaException("Invalid `←` modifier: cannot be applied to simp theorems of the form `¬ P`");
            }
            var p = ((AppExpr)type).Arg;
            if (ExprOps.IsAppOfArity(p, EqName, 3))
            {
                var args = p.GetAppArgs();
                if (args[2].IsConstOf(MetaNames.BoolTrue) || args[2].IsConstOf(MetaNames.BoolFalse))
                {
                    return [NegatedEq(args[0], args[1], args[2], ((ConstExpr)p.GetAppFn()).Levels[0])];
                }
            }
            return [MkPropEq(p, Expr.Const(FalseName))];
        }
        if (ExprOps.IsAppOfArity(type, AndName, 2))
        {
            var args = type.GetAppArgs();
            return [.. PreprocessSimp(args[0], inv), .. PreprocessSimp(args[1], inv)];
        }
        if (inv)
        {
            throw new MetaException("Invalid `←` modifier: cannot be applied to a rule that rewrites to `True`");
        }
        return [MkPropEq(type, Expr.Const(TrueName))];

        // `lhs ≠ rhs`: `lhs = false` or `lhs = true` for a Bool constant, else `(lhs = rhs) = False`.
        static Expr NegatedEq(Expr type, Expr lhs, Expr rhs, Level u) =>
            rhs.IsConstOf(MetaNames.BoolTrue) ? MkBoolEq(lhs, false)
            : rhs.IsConstOf(MetaNames.BoolFalse) ? MkBoolEq(lhs, true)
            : MkPropEq(MkEqAt(u, type, lhs, rhs), Expr.Const(FalseName));
    }

    internal ImmutableArray<DiscrTreeKey> SimpTheoremKeys(Expr type, bool noIndexAtArgs = false) => WithNewMCtxDepth(() =>
    {
        var (_, _, body) = ForallMetaTelescopeReducing(type);
        body = WhnfR(body);
        return EqSides(body) is var (lhs, _)
            ? DiscrTree.MkPath(this, lhs, noIndexAtArgs)
            : throw new MetaException($"Unexpected kind of simp theorem {body}");
    });
}
