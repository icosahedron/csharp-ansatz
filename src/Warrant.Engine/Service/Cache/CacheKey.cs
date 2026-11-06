using System.Collections.Immutable;
using System.Globalization;
using System.Security.Cryptography;
using System.Text;
using Warrant.Vir;

namespace Warrant.Engine.Service.Cache;

/// <summary>
/// What a cache key is made of (M5b KTD13, docs/m5b/04): everything a unit's outcome depends on except the budgets, which
/// an entry stores and compares instead.
/// </summary>
/// <param name="Closure">The unit's VIR closure hash (<see cref="VirHash.Closure"/>): its VIR, its facts and every callee's closure.</param>
/// <param name="Bundle">The semantics bundle file's SHA-256.</param>
/// <param name="Sidecar">The attribute sidecar file's SHA-256.</param>
/// <param name="Names">
/// The display names of the units in the closure, the unit's own among them, in key order: cached goal text and messages
/// print them, and the VIR does not hold them.
/// </param>
public sealed record CacheKeyInputs(string Closure, string Bundle, string Sidecar, ImmutableArray<CacheName> Names)
{
    /// <summary>
    /// The key: SHA-256, as 64 lowercase hex digits, over <see cref="CacheEntry.FormatVersion"/>, the toolchain identity
    /// and these inputs, each string length-prefixed so no two lists of inputs share an encoding.
    /// </summary>
    /// <param name="toolchain">The toolchain identity (<see cref="Toolchain.Identity"/>).</param>
    /// <returns>The key.</returns>
    public string Key(string toolchain)
    {
        ArgumentNullException.ThrowIfNull(toolchain);
        var text = new StringBuilder();
        void Add(string value) => text.Append(value.Length.ToString(CultureInfo.InvariantCulture)).Append(':').Append(value);
        Add("warrant-cache");
        Add(CacheEntry.FormatVersion.ToString(CultureInfo.InvariantCulture));
        Add(toolchain);
        Add(Bundle);
        Add(Sidecar);
        Add(Closure);
        foreach (var name in Names)
        {
            Add(name.Key);
            Add(name.DisplayName);
        }
        return Convert.ToHexStringLower(SHA256.HashData(Encoding.UTF8.GetBytes(text.ToString())));
    }

    /// <summary>
    /// The key inputs of every unit of a request whose closure is complete: a unit whose VIR could not be read, or that
    /// depends on one, or on a key the request does not hold, has none and is never cached.
    /// </summary>
    /// <param name="units">The request's readable units, with their display names (null for the fallback).</param>
    /// <param name="bundleSha256">The bundle file's SHA-256.</param>
    /// <param name="sidecarSha256">The sidecar file's SHA-256.</param>
    /// <returns>The inputs, by unit key.</returns>
    public static Dictionary<string, CacheKeyInputs> ForUnits(IEnumerable<EngineUnit> units, string bundleSha256, string sidecarSha256)
    {
        ArgumentNullException.ThrowIfNull(units);
        var byKey = new Dictionary<string, EngineUnit>(StringComparer.Ordinal);
        foreach (var unit in units)
        {
            byKey.TryAdd(unit.Unit.Key, unit);
        }
        var closures = new Dictionary<string, VirHash?>(StringComparer.Ordinal);
        var visiting = new HashSet<string>(StringComparer.Ordinal);

        VirHash? ClosureOf(string key)
        {
            if (closures.TryGetValue(key, out var known))
            {
                return known;
            }
            if (!byKey.TryGetValue(key, out var unit) || !visiting.Add(key))
            {
                return null;
            }
            Dictionary<string, VirHash>? deps = new(StringComparer.Ordinal);
            VirHash? hash = null;
            foreach (var dep in unit.Unit.Deps)
            {
                if (ClosureOf(dep) is not { } depHash)
                {
                    deps = null;
                    break;
                }
                deps[dep] = depHash;
            }
            if (deps is not null)
            {
                hash = VirHash.Closure(unit.Unit, deps);
            }
            visiting.Remove(key);
            closures[key] = hash;
            return hash;
        }

        var displays = byKey.ToDictionary(p => p.Key, p => Pipeline.Display(p.Value), StringComparer.Ordinal);
        var result = new Dictionary<string, CacheKeyInputs>(StringComparer.Ordinal);
        foreach (var (key, unit) in byKey)
        {
            if (ClosureOf(key) is not { } closure)
            {
                continue;
            }
            ImmutableArray<CacheName> names =
            [
                .. Pipeline.ClosureOf(unit, byKey).Append(key).Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal)
                    .Select(k => new CacheName(k, displays[k])),
            ];
            result.Add(key, new CacheKeyInputs(closure.ToString(), bundleSha256, sidecarSha256, names));
        }
        return result;
    }
}

/// <summary>A unit's display name in a key (<see cref="CacheKeyInputs.Names"/>).</summary>
/// <param name="Key">The unit's key.</param>
/// <param name="DisplayName">Its C# display name, or the fallback derived from its key.</param>
public sealed record CacheName(string Key, string DisplayName);
