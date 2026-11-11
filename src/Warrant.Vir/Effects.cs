namespace Warrant.Vir;

/// <summary>
/// Why a unit can raise (plan M6 KTD11): the construct that raises, where it is, and the callee it reaches the unit through.
/// </summary>
/// <param name="Construct">The construct, as a diagnostic names it, e.g. <c>division</c> or <c>throw</c>.</param>
/// <param name="Unit">The key of the unit that contains the construct.</param>
/// <param name="Node">The construct's node in <paramref name="Unit"/>; its ID is <see cref="VirTree.IdOf"/> of it there.</param>
/// <param name="Callee">
/// The callee the cause reaches the unit through: the unit's first raising callee when the construct is in another unit, or
/// the callee a call to a method with <c>Spec.Requires</c> names; null when the construct is the unit's own.
/// </param>
public sealed record RaiseCause(string Construct, string Unit, VirNode Node, string? Callee);

/// <summary>The result of <see cref="Effects.Analyze"/>: which units can raise, why, and which are recursive.</summary>
public sealed class EffectAnalysis
{
    private readonly Dictionary<string, RaiseCause> _causes;
    private readonly HashSet<string> _recursive;

    internal EffectAnalysis(Dictionary<string, RaiseCause> causes, HashSet<string> recursive)
    {
        _causes = causes;
        _recursive = recursive;
    }

    /// <summary>The cause of every unit that can raise, by key.</summary>
    public IReadOnlyDictionary<string, RaiseCause> Causes => _causes;

    /// <summary>Whether a function or theorem can raise, and so translates into the effect monad (or, for a theorem, is rejected).</summary>
    /// <param name="key">The unit's key.</param>
    /// <returns>True when it can raise.</returns>
    public bool IsRaising(string key) => _causes.ContainsKey(key);

    /// <summary>Why a unit can raise.</summary>
    /// <param name="key">The unit's key.</param>
    /// <returns>The cause, or null when the unit cannot raise or was not analysed.</returns>
    public RaiseCause? CauseOf(string key) => _causes.TryGetValue(key, out var cause) ? cause : null;

    /// <summary>Whether a unit lies on a cycle of the call graph: in a component of two or more, or calling itself.</summary>
    /// <param name="key">The unit's key.</param>
    /// <returns>True when it is recursive.</returns>
    public bool IsRecursive(string key) => _recursive.Contains(key);
}

/// <summary>
/// Raise-ability (plan M6 KTD11), one pure function over VIR that extraction, the analyzer and translation all call. A
/// function or theorem can raise exactly when it contains a raising construct, or calls a unit that can raise. All units of
/// one strongly connected component of the call graph are raising together, since each calls the others.
/// </summary>
/// <remarks>
/// The raising constructs: <c>throw</c> (statement or expression); <c>/</c> or <c>%</c> whose divisor is not a literal other
/// than 0 and -1; checked <c>+</c>, <c>-</c>, <c>*</c> or unary <c>-</c>; a checked conversion other than a widening; any
/// arithmetic on <c>decimal</c> but unary minus; a nullable read or non-null unwrap; a modelled member that throws
/// (<see cref="ThrowingModelledMembers"/>); an external call; <c>await</c>; <c>Spec.Assert</c>; and, in a function, a call to
/// a function that has <c>Spec.Requires</c>, so the walker sees the call and its precondition. A theorem's statement is
/// scanned the same way (KTD11's third rejection), apart from that last rule. The conditions of <c>Spec.Requires</c> and
/// <c>Spec.Ensures</c> are claims, never run, so they are not scanned; their partial operations get well-definedness
/// obligations instead (KTD26).
/// </remarks>
public static class Effects
{
    /// <summary>
    /// The modelled members that can throw (KTD23): <c>Math.Abs</c> of <c>int.MinValue</c> or <c>long.MinValue</c>.
    /// Extraction's table of modelled members must agree.
    /// </summary>
    public static IReadOnlyCollection<string> ThrowingModelledMembers { get; } = new HashSet<string>(StringComparer.Ordinal)
    {
        "M:System.Math.Abs(System.Int32)",
        "M:System.Math.Abs(System.Int64)",
    };

    /// <summary>Whether a function's body states a precondition: a leading <see cref="RequiresStmt"/>.</summary>
    /// <param name="unit">The unit.</param>
    /// <returns>True for a function whose block body has a <c>Spec.Requires</c> among its statements.</returns>
    public static bool HasRequires(VirUnit unit) =>
        unit.Kind == VirUnitKind.Function && unit.Body is BlockStmt block && block.Stmts.Any(s => s is RequiresStmt);

    /// <summary>
    /// Analyses a set of units: the functions and theorems among them, with calls to units outside the set ignored.
    /// Deterministic: units and calls are visited in ordinal key order and pre-order.
    /// </summary>
    /// <param name="units">The units, in any order; keys must be distinct.</param>
    /// <returns>The analysis.</returns>
    public static EffectAnalysis Analyze(IEnumerable<VirUnit> units)
    {
        var byKey = new SortedDictionary<string, VirUnit>(StringComparer.Ordinal);
        foreach (var unit in units)
        {
            if (unit.Kind is VirUnitKind.Function or VirUnitKind.Theorem)
            {
                byKey.Add(unit.Key, unit);
            }
        }
        var requires = new HashSet<string>(byKey.Values.Where(HasRequires).Select(u => u.Key), StringComparer.Ordinal);
        var calls = byKey.ToDictionary(p => p.Key, p => Calls(p.Value).Where(c => byKey.ContainsKey(c.Target)).ToList(), StringComparer.Ordinal);
        var causes = new Dictionary<string, RaiseCause>(StringComparer.Ordinal);
        var recursive = new HashSet<string>(StringComparer.Ordinal);

        // Components come out callees first, so every callee outside a component is decided before it.
        foreach (var component in Components(byKey.Keys, k => calls[k].Select(c => c.Target)))
        {
            if (component.Count > 1 || calls[component[0]].Any(c => string.Equals(c.Target, component[0], StringComparison.Ordinal)))
            {
                recursive.UnionWith(component);
            }
            foreach (var key in component)
            {
                if (LocalCause(byKey[key], requires) is { } local)
                {
                    causes[key] = local;
                }
            }
            // Within a component a cause spreads along calls until nothing changes; a unit takes its first raising callee.
            bool changed = true;
            while (changed)
            {
                changed = false;
                foreach (var key in component)
                {
                    if (causes.ContainsKey(key))
                    {
                        continue;
                    }
                    foreach (var call in calls[key])
                    {
                        if (causes.TryGetValue(call.Target, out var via))
                        {
                            causes[key] = via with { Callee = call.Target };
                            changed = true;
                            break;
                        }
                    }
                }
            }
        }
        return new EffectAnalysis(causes, recursive);
    }

    /// <summary>The unit's own first raising construct in pre-order, or null when it has none.</summary>
    private static RaiseCause? LocalCause(VirUnit unit, HashSet<string> requires)
    {
        foreach (var node in Executed(unit))
        {
            string? construct = Construct(node);
            if (construct is not null)
            {
                return new RaiseCause(construct, unit.Key, node, null);
            }
            if (unit.Kind == VirUnitKind.Function && node is CallExpr call && requires.Contains(call.Target))
            {
                return new RaiseCause("call to a method with Spec.Requires", unit.Key, node, call.Target);
            }
        }
        return null;
    }

    /// <summary>The name of the raising construct a node is, or null when the node cannot raise by itself.</summary>
    private static string? Construct(VirNode node) => node switch
    {
        ThrowStmt or ThrowExpr => "throw",
        BinaryExpr { Op: BinaryOp.Div } b when !SafeDivisor(b.R) => "division",
        BinaryExpr { Op: BinaryOp.Rem } b when !SafeDivisor(b.R) => "remainder",
        BinaryExpr b when b.Type == VirType.Decimal => "decimal arithmetic",
        BinaryExpr { Overflow: VirOverflow.Checked, Op: BinaryOp.Add or BinaryOp.Sub or BinaryOp.Mul } => "checked arithmetic",
        UnaryExpr { Overflow: VirOverflow.Checked, Op: UnaryOp.Neg } u when u.Type != VirType.Decimal => "checked arithmetic",
        ConvertExpr { Overflow: VirOverflow.Checked } c when !Widening(c.From, c.To) => "checked narrowing",
        UnwrapExpr { Kind: UnwrapKind.Value } => "nullable read",
        UnwrapExpr => "non-null unwrap",
        ModelledCallExpr m when ThrowingModelledMembers.Contains(m.Member) => $"modelled member {m.Member}",
        ExternalCallExpr => "external call",
        AwaitExpr => "await",
        AssertStmt => "Spec.Assert",
        _ => null,
    };

    /// <summary>A divisor that can neither be zero nor make <c>MinValue / -1</c> overflow: an integer literal other than 0 and -1.</summary>
    private static bool SafeDivisor(VirExpr divisor) =>
        divisor is LitExpr { Value: not 0 and not -1 } lit && (lit.Type == VirType.Int32 || lit.Type == VirType.Int64);

    private static bool Widening(VirType from, VirType to) => from == to || (from == VirType.Int32 && to == VirType.Int64);

    /// <summary>The calls a unit makes, in pre-order, outside its <c>Spec.Requires</c> and <c>Spec.Ensures</c>.</summary>
    private static IEnumerable<CallExpr> Calls(VirUnit unit) => Executed(unit).OfType<CallExpr>();

    /// <summary>The nodes of a unit's body and statement in pre-order, skipping the claims of <c>Requires</c> and <c>Ensures</c>.</summary>
    private static IEnumerable<VirNode> Executed(VirUnit unit)
    {
        var stack = new Stack<VirNode>();
        if (unit.Statement is { } statement)
        {
            stack.Push(statement);
        }
        if (unit.Body is { } body)
        {
            stack.Push(body);
        }
        while (stack.Count > 0)
        {
            var node = stack.Pop();
            if (node is RequiresStmt or EnsuresStmt)
            {
                continue;
            }
            yield return node;
            foreach (var child in VirTree.Children(node).Reverse())
            {
                stack.Push(child);
            }
        }
    }

    /// <summary>
    /// The strongly connected components of a graph (Tarjan's algorithm, as <c>Graph.OnCycles</c> in Extraction), each
    /// sorted ordinally, in the order they complete: a component comes after every component it reaches.
    /// </summary>
    private static List<List<string>> Components(IEnumerable<string> nodes, Func<string, IEnumerable<string>> edges)
    {
        var all = new SortedSet<string>(nodes, StringComparer.Ordinal);
        var index = new Dictionary<string, int>(StringComparer.Ordinal);
        var low = new Dictionary<string, int>(StringComparer.Ordinal);
        var onStack = new HashSet<string>(StringComparer.Ordinal);
        var stack = new Stack<string>();
        var result = new List<List<string>>();
        int next = 0;

        IEnumerable<string> Successors(string n) =>
            edges(n).Where(all.Contains).Distinct(StringComparer.Ordinal).OrderBy(s => s, StringComparer.Ordinal);

        void Connect(string v)
        {
            index[v] = low[v] = next++;
            stack.Push(v);
            onStack.Add(v);
            foreach (var w in Successors(v))
            {
                if (!index.TryGetValue(w, out int wIndex))
                {
                    Connect(w);
                    low[v] = Math.Min(low[v], low[w]);
                }
                else if (onStack.Contains(w))
                {
                    low[v] = Math.Min(low[v], wIndex);
                }
            }
            if (low[v] == index[v])
            {
                var component = new List<string>();
                string w;
                do
                {
                    w = stack.Pop();
                    onStack.Remove(w);
                    component.Add(w);
                }
                while (!string.Equals(w, v, StringComparison.Ordinal));
                component.Sort(StringComparer.Ordinal);
                result.Add(component);
            }
        }

        foreach (var n in all)
        {
            if (!index.ContainsKey(n))
            {
                Connect(n);
            }
        }
        return result;
    }
}
