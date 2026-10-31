namespace LeanSharp.Lean4Export;

/// <summary>
/// An integer-indexed table of export records. Indices may be sparse, but each may be defined
/// only once and only referenced after its definition.
/// </summary>
internal sealed class IndexTable<T>
    where T : class
{
    private readonly string _kind;
    private T?[] _items = new T?[1024];

    public IndexTable(string kind) => _kind = kind;

    /// <summary>The number of defined entries.</summary>
    public int Count { get; private set; }

    public void Define(int index, T value, long line)
    {
        if (index >= _items.Length)
        {
            int size = _items.Length;
            while (size <= index)
            {
                size = size < (1 << 30) ? size * 2 : int.MaxValue;
            }
            Array.Resize(ref _items, size);
        }
        if (_items[index] is not null)
        {
            throw new Lean4ExportFormatException(line, $"{_kind} index {index} is defined more than once");
        }
        _items[index] = value;
        Count++;
    }

    public T Get(int index, long line) =>
        (index < _items.Length ? _items[index] : null)
        ?? throw new Lean4ExportFormatException(line, $"reference to undefined {_kind} index {index}");
}
