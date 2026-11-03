using System.Security.Cryptography;
using System.Text;

namespace Warrant.Vir;

/// <summary>
/// A SHA-256 hash of VIR (docs/m4/04, "Hashes"; KTD21). Compares by value; <see cref="ToString"/> is lowercase hex.
/// </summary>
public sealed class VirHash : IEquatable<VirHash>
{
    private readonly byte[] _bytes;

    private VirHash(byte[] bytes) => _bytes = bytes;

    /// <summary>The unit hash: SHA-256 over the unit's canonical encoding (<see cref="VirWriter.Write"/>).</summary>
    /// <param name="unit">The unit.</param>
    /// <returns>The unit hash.</returns>
    public static VirHash OfUnit(VirUnit unit) => Sha256(VirWriter.Write(unit));

    /// <summary>
    /// The closure hash: SHA-256 over the unit hash followed by the closure hashes of the unit's <c>deps</c>,
    /// in key order.
    /// </summary>
    /// <param name="unit">The unit.</param>
    /// <param name="depClosures">The closure hash of each of the unit's deps, by key; other entries are ignored.</param>
    /// <returns>The closure hash.</returns>
    /// <exception cref="KeyNotFoundException">A dep has no closure hash in <paramref name="depClosures"/>.</exception>
    public static VirHash Closure(VirUnit unit, IReadOnlyDictionary<string, VirHash> depClosures)
    {
        var data = new List<byte>(32 * (unit.Deps.Count + 1));
        data.AddRange(OfUnit(unit)._bytes);
        foreach (var dep in unit.Deps)
        {
            if (!depClosures.TryGetValue(dep, out var hash))
            {
                throw new KeyNotFoundException($"No closure hash for '{dep}', a dep of '{unit.Key}'.");
            }
            data.AddRange(hash._bytes);
        }
        return Sha256(data.ToArray());
    }

    /// <summary>The closure hash of every unit in a set that contains all of its units' deps.</summary>
    /// <param name="units">The units, in any order; keys must be distinct.</param>
    /// <returns>Each unit's closure hash, by key.</returns>
    /// <exception cref="KeyNotFoundException">A dep is not in the set.</exception>
    /// <exception cref="InvalidOperationException">The deps form a cycle.</exception>
    public static IReadOnlyDictionary<string, VirHash> Closures(IEnumerable<VirUnit> units)
    {
        var byKey = new Dictionary<string, VirUnit>(StringComparer.Ordinal);
        foreach (var unit in units)
        {
            byKey.Add(unit.Key, unit);
        }
        var done = new Dictionary<string, VirHash>(StringComparer.Ordinal);
        var visiting = new HashSet<string>(StringComparer.Ordinal);
        foreach (var key in byKey.Keys)
        {
            Visit(key);
        }
        return done;

        void Visit(string key)
        {
            if (done.ContainsKey(key))
            {
                return;
            }
            if (!byKey.TryGetValue(key, out var unit))
            {
                throw new KeyNotFoundException($"The dep '{key}' is not in the set of units.");
            }
            if (!visiting.Add(key))
            {
                throw new InvalidOperationException($"The deps of '{key}' form a cycle.");
            }
            foreach (var dep in unit.Deps)
            {
                Visit(dep);
            }
            visiting.Remove(key);
            done.Add(key, Closure(unit, done));
        }
    }

    /// <summary>The 32 hash bytes.</summary>
    /// <returns>A copy of the bytes.</returns>
    public byte[] ToByteArray() => (byte[])_bytes.Clone();

    /// <summary>The hash as 64 lowercase hex digits.</summary>
    /// <returns>The hex string.</returns>
    public override string ToString()
    {
        var hex = new StringBuilder(_bytes.Length * 2);
        foreach (var b in _bytes)
        {
            hex.Append(b.ToString("x2", System.Globalization.CultureInfo.InvariantCulture));
        }
        return hex.ToString();
    }

    /// <inheritdoc/>
    public bool Equals(VirHash? other) => other is not null && _bytes.SequenceEqual(other._bytes);

    /// <inheritdoc/>
    public override bool Equals(object? obj) => obj is VirHash other && Equals(other);

    /// <inheritdoc/>
    public override int GetHashCode() => BitConverter.ToInt32(_bytes, 0);

    internal static VirHash Sha256(byte[] data)
    {
        // SHA256.HashData does not exist on netstandard2.0; one call for both builds keeps them identical.
        using var sha = SHA256.Create();
#pragma warning disable CA1850
        return new VirHash(sha.ComputeHash(data));
#pragma warning restore CA1850
    }
}
