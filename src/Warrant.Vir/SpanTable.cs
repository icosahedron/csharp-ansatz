namespace Warrant.Vir;

/// <summary>A source span. Lines and columns are one-based; the end is exclusive.</summary>
/// <param name="Path">The source path, relative as the compilation gives it.</param>
/// <param name="StartLine">The first line.</param>
/// <param name="StartColumn">The first column.</param>
/// <param name="EndLine">The last line.</param>
/// <param name="EndColumn">The column just past the end.</param>
public sealed record VirSpan(string Path, int StartLine, int StartColumn, int EndLine, int EndColumn);

/// <summary>
/// The side table from node ID to source span. It is not part of the unit, so it is in neither hash,
/// and moving code does not change a unit's hashes (KTD5).
/// </summary>
public sealed class SpanTable
{
    private readonly Dictionary<int, VirSpan> _spans;

    /// <summary>Creates a table from node IDs to spans.</summary>
    /// <param name="spans">The spans by node ID.</param>
    public SpanTable(IEnumerable<KeyValuePair<int, VirSpan>> spans)
    {
        _spans = new Dictionary<int, VirSpan>();
        foreach (var pair in spans)
        {
            _spans.Add(pair.Key, pair.Value);
        }
    }

    /// <summary>The number of nodes with a span.</summary>
    public int Count => _spans.Count;

    /// <summary>
    /// The node IDs that have a span, with their spans, in ascending node-ID order: the input a table is rebuilt from
    /// with <see cref="SpanTable(IEnumerable{KeyValuePair{int, VirSpan}})"/>.
    /// </summary>
    public IEnumerable<KeyValuePair<int, VirSpan>> Entries => _spans.OrderBy(pair => pair.Key);

    /// <summary>Builds the table for a unit by numbering its nodes in pre-order.</summary>
    /// <param name="unit">The unit.</param>
    /// <param name="spanOf">The span of a node instance, or null if it has none.</param>
    /// <returns>The table.</returns>
    public static SpanTable Build(VirUnit unit, Func<VirNode, VirSpan?> spanOf)
    {
        var spans = new List<KeyValuePair<int, VirSpan>>();
        int id = 0;
        foreach (var node in VirTree.PreOrder(unit))
        {
            if (spanOf(node) is { } span)
            {
                spans.Add(new KeyValuePair<int, VirSpan>(id, span));
            }
            id++;
        }
        return new SpanTable(spans);
    }

    /// <summary>Looks up a node's span.</summary>
    /// <param name="nodeId">The node ID.</param>
    /// <param name="span">The span, if found.</param>
    /// <returns>Whether the node has a span.</returns>
    public bool TryGetSpan(int nodeId, out VirSpan? span) => _spans.TryGetValue(nodeId, out span);
}
