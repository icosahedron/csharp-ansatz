using System.Collections;

namespace Warrant.Vir;

/// <summary>
/// An immutable list with structural equality, so that VIR records containing lists compare by value.
/// Build one with <see cref="VirList.Of{T}(T[])"/> or the constructor.
/// </summary>
/// <typeparam name="T">The element type.</typeparam>
public sealed class VirList<T> : IReadOnlyList<T>, IEquatable<VirList<T>>
{
    private readonly T[] _items;

    /// <summary>Copies the given items into a new list.</summary>
    /// <param name="items">The elements, in order.</param>
    public VirList(IEnumerable<T> items) => _items = items.ToArray();

    /// <summary>The empty list.</summary>
#pragma warning disable CA1000 // Same idiom as ImmutableArray<T>.Empty.
    public static VirList<T> Empty { get; } = new(Array.Empty<T>());
#pragma warning restore CA1000

    /// <inheritdoc/>
    public int Count => _items.Length;

    /// <inheritdoc/>
    public T this[int index] => _items[index];

    /// <inheritdoc/>
    public IEnumerator<T> GetEnumerator() => ((IEnumerable<T>)_items).GetEnumerator();

    IEnumerator IEnumerable.GetEnumerator() => _items.GetEnumerator();

    /// <inheritdoc/>
    public bool Equals(VirList<T>? other)
    {
        if (other is null || other._items.Length != _items.Length)
        {
            return false;
        }
        var cmp = EqualityComparer<T>.Default;
        for (int i = 0; i < _items.Length; i++)
        {
            if (!cmp.Equals(_items[i], other._items[i]))
            {
                return false;
            }
        }
        return true;
    }

    /// <inheritdoc/>
    public override bool Equals(object? obj) => obj is VirList<T> other && Equals(other);

    /// <inheritdoc/>
    public override int GetHashCode()
    {
        unchecked
        {
            int hash = 17;
            var cmp = EqualityComparer<T>.Default;
            foreach (var item in _items)
            {
                hash = (hash * 31) + (item is null ? 0 : cmp.GetHashCode(item));
            }
            return hash;
        }
    }

    /// <summary>Structural equality.</summary>
    /// <param name="left">The left list.</param>
    /// <param name="right">The right list.</param>
    /// <returns>Whether both are null, or have equal elements in the same order.</returns>
    public static bool operator ==(VirList<T>? left, VirList<T>? right) => left is null ? right is null : left.Equals(right);

    /// <summary>Structural inequality.</summary>
    /// <param name="left">The left list.</param>
    /// <param name="right">The right list.</param>
    /// <returns>The negation of <c>==</c>.</returns>
    public static bool operator !=(VirList<T>? left, VirList<T>? right) => !(left == right);
}

/// <summary>Factory methods for <see cref="VirList{T}"/>.</summary>
public static class VirList
{
    /// <summary>Creates a list of the given items.</summary>
    /// <typeparam name="T">The element type.</typeparam>
    /// <param name="items">The elements, in order.</param>
    /// <returns>A new list.</returns>
    public static VirList<T> Of<T>(params T[] items) => new(items);
}
