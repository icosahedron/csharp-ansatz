namespace Warrant.Cic;

/// <summary>
/// Deterministic 64-bit hash mixing for CIC terms.
/// </summary>
/// <remarks>
/// <see cref="System.HashCode"/> and <see cref="string.GetHashCode()"/> are randomized per process.
/// CIC hashes are deterministic instead, so that kernel behaviour (cache hit patterns, traces) is
/// reproducible across runs. These hashes are for in-memory tables only; persistent content
/// addressing will use a cryptographic hash over a canonical encoding.
/// </remarks>
internal static class Hashing
{
    private const ulong Prime1 = 0x9E3779B185EBCA87UL;
    private const ulong Prime2 = 0xC2B2AE3D27D4EB4FUL;

    /// <summary>Combines two hash values (order-sensitive).</summary>
    public static ulong Mix(ulong h, ulong v)
    {
        h ^= Avalanche(v + Prime2);
        h = (h << 27) | (h >> 37);
        return (h * Prime1) + 0x27D4EB2F165667C5UL;
    }

    /// <summary>Combines three hash values (order-sensitive).</summary>
    public static ulong Mix(ulong h, ulong a, ulong b) => Mix(Mix(h, a), b);

    /// <summary>Combines four hash values (order-sensitive).</summary>
    public static ulong Mix(ulong h, ulong a, ulong b, ulong c) => Mix(Mix(Mix(h, a), b), c);

    /// <summary>A deterministic hash of a string's UTF-16 code units.</summary>
    public static ulong String(string s)
    {
        // FNV-1a over UTF-16 code units, then avalanche.
        ulong h = 0xCBF29CE484222325UL;
        foreach (char c in s)
        {
            h ^= c;
            h *= 0x100000001B3UL;
        }
        return Avalanche(h ^ (ulong)s.Length);
    }

    /// <summary>The 64-bit finalizer from MurmurHash3.</summary>
    public static ulong Avalanche(ulong h)
    {
        h ^= h >> 33;
        h *= 0xFF51AFD7ED558CCDUL;
        h ^= h >> 33;
        h *= 0xC4CEB9FE1A85EC53UL;
        h ^= h >> 33;
        return h;
    }

    /// <summary>Folds a 64-bit hash into the 32 bits <see cref="object.GetHashCode"/> returns.</summary>
    public static int Fold(ulong h) => (int)(h ^ (h >> 32));
}
