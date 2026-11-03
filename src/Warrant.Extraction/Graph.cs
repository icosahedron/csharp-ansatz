namespace Warrant.Extraction;

/// <summary>Deterministic graph algorithms over unit keys: nodes and edges are visited in ordinal key order.</summary>
internal static class Graph
{
    /// <summary>The nodes that lie on a cycle: in a strongly connected component of two or more, or with an edge to themselves.</summary>
    /// <param name="nodes">The nodes.</param>
    /// <param name="edges">The successors of a node; successors that are not nodes are ignored.</param>
    /// <returns>The nodes on a cycle.</returns>
    public static SortedSet<string> OnCycles(IEnumerable<string> nodes, Func<string, IEnumerable<string>> edges)
    {
        var all = new SortedSet<string>(nodes, StringComparer.Ordinal);
        var index = new Dictionary<string, int>(StringComparer.Ordinal);
        var low = new Dictionary<string, int>(StringComparer.Ordinal);
        var onStack = new HashSet<string>(StringComparer.Ordinal);
        var stack = new Stack<string>();
        var result = new SortedSet<string>(StringComparer.Ordinal);
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
                while (w != v);
                if (component.Count > 1 || Successors(v).Contains(v, StringComparer.Ordinal))
                {
                    result.UnionWith(component);
                }
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

    /// <summary>Orders nodes so that every dependency comes first; ties broken by key (ordinal). The graph must be acyclic.</summary>
    /// <param name="nodes">The nodes.</param>
    /// <param name="deps">The dependencies of a node; those that are not nodes are ignored.</param>
    /// <returns>The nodes in dependency order.</returns>
    public static List<string> TopologicalOrder(IEnumerable<string> nodes, Func<string, IEnumerable<string>> deps)
    {
        var all = new SortedSet<string>(nodes, StringComparer.Ordinal);
        var remaining = new Dictionary<string, int>(StringComparer.Ordinal);
        var users = new Dictionary<string, List<string>>(StringComparer.Ordinal);
        foreach (var n in all)
        {
            var ds = deps(n).Where(all.Contains).Distinct(StringComparer.Ordinal).ToList();
            remaining[n] = ds.Count;
            foreach (var d in ds)
            {
                if (!users.TryGetValue(d, out var list))
                {
                    users[d] = list = [];
                }
                list.Add(n);
            }
        }
        var ready = new SortedSet<string>(all.Where(n => remaining[n] == 0), StringComparer.Ordinal);
        var order = new List<string>();
        while (ready.Count > 0)
        {
            var n = ready.Min!;
            ready.Remove(n);
            order.Add(n);
            if (users.TryGetValue(n, out var list))
            {
                foreach (var u in list)
                {
                    if (--remaining[u] == 0)
                    {
                        ready.Add(u);
                    }
                }
            }
        }
        if (order.Count != all.Count)
        {
            throw new InvalidOperationException("The unit graph has a cycle.");
        }
        return order;
    }
}
