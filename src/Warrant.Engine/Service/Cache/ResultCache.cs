namespace Warrant.Engine.Service.Cache;

/// <summary>A cache entry that was read and checked, with the outcome it holds.</summary>
/// <param name="Entry">The entry.</param>
/// <param name="Outcome">Its outcome, with the declarations of its certificate.</param>
public sealed record CachedResult(CacheEntry Entry, UnitOutcome Outcome);

/// <summary>
/// Where finished units' outcomes are kept (M5b KTD14, docs/m5b/04). The verification service reads and writes through
/// it; <see cref="NullResultCache"/> keeps nothing, for <c>explain</c>, tests and requests without a cache directory.
/// </summary>
public interface IResultCache
{
    /// <summary>
    /// Reads the entry for a key, checking its hash, format and toolchain; an entry that fails a check is deleted and
    /// read as absent.
    /// </summary>
    /// <param name="directory">The project's cache directory.</param>
    /// <param name="key">The key.</param>
    /// <param name="fromDisk">Reads the file even when a copy in memory is still current, as recheck does.</param>
    /// <returns>The entry, or null when there is none or it was bad.</returns>
    CachedResult? Read(string directory, string key, bool fromDisk = false);

    /// <summary>
    /// Stores an entry under its key, replacing any entry already there; the directory is created if it is missing. A
    /// failure to write is not an error: the entry is simply absent.
    /// </summary>
    /// <param name="directory">The project's cache directory.</param>
    /// <param name="entry">The entry.</param>
    /// <returns>Whether the entry was stored.</returns>
    bool Write(string directory, CacheEntry entry);

    /// <summary>Removes the entry for a key, from disk and memory.</summary>
    /// <param name="directory">The project's cache directory.</param>
    /// <param name="key">The key.</param>
    void Delete(string directory, string key);
}

/// <summary>A cache that keeps nothing: every read misses.</summary>
public sealed class NullResultCache : IResultCache
{
    private NullResultCache()
    {
    }

    /// <summary>The one instance.</summary>
    public static NullResultCache Instance { get; } = new();

    /// <inheritdoc/>
    public CachedResult? Read(string directory, string key, bool fromDisk = false) => null;

    /// <inheritdoc/>
    public bool Write(string directory, CacheEntry entry) => false;

    /// <inheritdoc/>
    public void Delete(string directory, string key)
    {
    }
}

/// <summary>
/// The result cache on disk (M5b KTD14): one JSON file per entry, <c>&lt;key&gt;.json</c>, in the project's cache
/// directory, written to a temporary file and renamed into place; with a bounded map in memory in front of it, keyed by
/// directory and key. A copy in memory counts only while its file still exists with the length and last-write time it
/// had when it was read, so a deleted directory, a deleted entry and a hand edit all reach the disk. Safe to use from
/// several threads and processes at once.
/// </summary>
public sealed class FileResultCache : IResultCache
{
    /// <summary>The most entries kept in memory by default.</summary>
    public const int DefaultCapacity = 4096;

    private readonly int _capacity;
    private readonly string _toolchain;
    private readonly Dictionary<(string Directory, string Key), LinkedListNode<Memo>> _memory = [];
    private readonly LinkedList<Memo> _recent = new();
    private readonly Lock _lock = new();

    /// <summary>A cache for this process's toolchain.</summary>
    /// <param name="capacity">The most entries kept in memory.</param>
    /// <param name="toolchain">The toolchain identity entries must carry; <see cref="Toolchain.Identity"/> when null.</param>
    public FileResultCache(int capacity = DefaultCapacity, string? toolchain = null)
    {
        ArgumentOutOfRangeException.ThrowIfNegativeOrZero(capacity);
        _capacity = capacity;
        _toolchain = toolchain ?? Toolchain.Identity;
    }

    /// <summary>The number of entries held in memory.</summary>
    public int MemoryCount
    {
        get
        {
            lock (_lock)
            {
                return _memory.Count;
            }
        }
    }

    /// <summary>The file an entry is stored in.</summary>
    /// <param name="directory">The cache directory.</param>
    /// <param name="key">The key.</param>
    /// <returns>The path.</returns>
    public static string PathOf(string directory, string key) => Path.Combine(Path.GetFullPath(directory), key + ".json");

    /// <inheritdoc/>
    public CachedResult? Read(string directory, string key, bool fromDisk = false)
    {
        ArgumentNullException.ThrowIfNull(directory);
        ArgumentNullException.ThrowIfNull(key);
        var id = (Path.GetFullPath(directory), key);
        var path = PathOf(directory, key);
        if (!fromDisk && Remembered(id) is { } memo)
        {
            var info = new FileInfo(path);
            if (info.Exists && info.Length == memo.Length && info.LastWriteTimeUtc == memo.LastWriteUtc)
            {
                return memo.Result;
            }
            Forget(id);
        }

        byte[] bytes;
        long length;
        DateTime lastWrite;
        try
        {
            using var stream = new FileStream(path, FileMode.Open, FileAccess.Read, FileShare.ReadWrite | FileShare.Delete);
            length = stream.Length;
            lastWrite = File.GetLastWriteTimeUtc(stream.SafeFileHandle);
            bytes = new byte[length];
            stream.ReadExactly(bytes);
        }
        catch (Exception ex) when (ex is IOException or UnauthorizedAccessException)
        {
            // Absent, or being replaced: a miss, and the file is left to whoever is writing it.
            Forget(id);
            return null;
        }

        CachedResult result;
        try
        {
            var entry = CacheEntry.FromFile(bytes, key, _toolchain);
            result = new CachedResult(entry, entry.Outcome.ToOutcome(entry.Declarations()));
        }
        catch (FormatException)
        {
            Delete(directory, key);
            return null;
        }
        Remember(id, new Memo(id, result, length, lastWrite));
        return result;
    }

    /// <inheritdoc/>
    public bool Write(string directory, CacheEntry entry)
    {
        ArgumentNullException.ThrowIfNull(directory);
        ArgumentNullException.ThrowIfNull(entry);
        var path = PathOf(directory, entry.Key);
        var temporary = $"{path}.{Guid.NewGuid():N}.tmp";
        try
        {
            Directory.CreateDirectory(Path.GetDirectoryName(path)!);
            File.WriteAllBytes(temporary, entry.ToFile());
            File.Move(temporary, path, overwrite: true);
            return true;
        }
        catch (Exception ex) when (ex is IOException or UnauthorizedAccessException)
        {
            TryDelete(temporary);
            return false;
        }
    }

    /// <inheritdoc/>
    public void Delete(string directory, string key)
    {
        ArgumentNullException.ThrowIfNull(directory);
        ArgumentNullException.ThrowIfNull(key);
        Forget((Path.GetFullPath(directory), key));
        TryDelete(PathOf(directory, key));
    }

    private static void TryDelete(string path)
    {
        try
        {
            File.Delete(path);
        }
        catch (Exception ex) when (ex is IOException or UnauthorizedAccessException)
        {
            // Already gone, or in use: a bad entry left behind is deleted by the next reader.
        }
    }

    private Memo? Remembered((string, string) id)
    {
        lock (_lock)
        {
            if (!_memory.TryGetValue(id, out var node))
            {
                return null;
            }
            _recent.Remove(node);
            _recent.AddFirst(node);
            return node.Value;
        }
    }

    private void Remember((string, string) id, Memo memo)
    {
        lock (_lock)
        {
            if (_memory.Remove(id, out var old))
            {
                _recent.Remove(old);
            }
            _memory.Add(id, _recent.AddFirst(memo));
            while (_memory.Count > _capacity)
            {
                var last = _recent.Last!;
                _recent.RemoveLast();
                _memory.Remove(last.Value.Id);
            }
        }
    }

    private void Forget((string, string) id)
    {
        lock (_lock)
        {
            if (_memory.Remove(id, out var node))
            {
                _recent.Remove(node);
            }
        }
    }

    private sealed record Memo((string Directory, string Key) Id, CachedResult Result, long Length, DateTime LastWriteUtc);
}
