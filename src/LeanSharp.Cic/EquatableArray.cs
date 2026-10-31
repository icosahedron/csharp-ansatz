using System.Collections;
using System.Collections.Immutable;
using System.Runtime.CompilerServices;

namespace LeanSharp.Cic;

/// <summary>
/// An immutable array with structural equality, so records containing arrays compare by value.
/// </summary>
/// <typeparam name="T">The element type.</typeparam>
[CollectionBuilder(typeof(EquatableArray), nameof(EquatableArray.Create))]
public readonly struct EquatableArray<T> : IEquatable<EquatableArray<T>>, IReadOnlyList<T>
{
    private readonly ImmutableArray<T> _items;

    /// <summary>Wraps an immutable array.</summary>
    public EquatableArray(ImmutableArray<T> items) => _items = items;

    /// <summary>The empty array.</summary>
#pragma warning disable CA1000 // Same idiom as ImmutableArray<T>.Empty.
    public static EquatableArray<T> Empty => new(ImmutableArray<T>.Empty);
#pragma warning restore CA1000

    /// <summary>The underlying immutable array (never default).</summary>
    public ImmutableArray<T> AsImmutableArray() => _items.IsDefault ? ImmutableArray<T>.Empty : _items;

    /// <inheritdoc/>
    public int Count => _items.IsDefault ? 0 : _items.Length;

    /// <inheritdoc/>
    public T this[int index] => AsImmutableArray()[index];

    /// <summary>Returns a struct enumerator over the elements.</summary>
    public ImmutableArray<T>.Enumerator GetEnumerator() => AsImmutableArray().GetEnumerator();

    IEnumerator<T> IEnumerable<T>.GetEnumerator() => ((IEnumerable<T>)AsImmutableArray()).GetEnumerator();

    IEnumerator IEnumerable.GetEnumerator() => ((IEnumerable)AsImmutableArray()).GetEnumerator();

    /// <inheritdoc/>
    public bool Equals(EquatableArray<T> other)
    {
        var a = AsImmutableArray();
        var b = other.AsImmutableArray();
        if (a.Length != b.Length)
        {
            return false;
        }
        var cmp = EqualityComparer<T>.Default;
        for (int i = 0; i < a.Length; i++)
        {
            if (!cmp.Equals(a[i], b[i]))
            {
                return false;
            }
        }
        return true;
    }

    /// <inheritdoc/>
    public override bool Equals(object? obj) => obj is EquatableArray<T> other && Equals(other);

    /// <inheritdoc/>
    public override int GetHashCode()
    {
        var hash = new HashCode();
        foreach (var item in AsImmutableArray())
        {
            hash.Add(item);
        }
        return hash.ToHashCode();
    }

    /// <summary>Equality operator (structural).</summary>
    public static bool operator ==(EquatableArray<T> left, EquatableArray<T> right) => left.Equals(right);

    /// <summary>Inequality operator (structural).</summary>
    public static bool operator !=(EquatableArray<T> left, EquatableArray<T> right) => !left.Equals(right);

    /// <summary>Converts from an immutable array.</summary>
    public static implicit operator EquatableArray<T>(ImmutableArray<T> items) => new(items);

    /// <summary>Converts from an array (copied).</summary>
    public static implicit operator EquatableArray<T>(T[] items) => new(ImmutableArray.Create(items));

    /// <inheritdoc/>
    public override string ToString() => "[" + string.Join(", ", AsImmutableArray()) + "]";
}

/// <summary>Factory methods for <see cref="EquatableArray{T}"/>.</summary>
public static class EquatableArray
{
    /// <summary>Creates an array from the given items.</summary>
    public static EquatableArray<T> Create<T>(params ReadOnlySpan<T> items) => new(ImmutableArray.Create(items));

    /// <summary>Creates an array from a sequence.</summary>
    public static EquatableArray<T> ToEquatableArray<T>(this IEnumerable<T> items) => new(items.ToImmutableArray());
}
