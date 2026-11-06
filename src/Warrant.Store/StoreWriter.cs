using System.Buffers.Binary;
using System.Security.Cryptography;
using Warrant.Cic;

namespace Warrant.Store;

/// <summary>
/// Writes a new version of a store (KTD17): declarations stream into <c>decls.bin</c> in a temporary directory; committing
/// writes <c>names.idx</c> and <c>manifest.json</c>, renames the directory to <c>v1-&lt;hash12&gt;</c>, replaces
/// <c>current</c> and deletes the versions no reader has open. A version is never changed once written, and readers of
/// an earlier version are not disturbed. Only one writer works on a store at a time; a second one fails at once.
/// </summary>
/// <remarks>
/// The version's name is a hash of its manifest and its records, so the same input written twice makes the same,
/// byte-identical, version directory. A writer disposed without <see cref="Commit"/> leaves the store as it was.
/// </remarks>
public sealed class StoreWriter : IDisposable
{
    private readonly string _store;
    private readonly FileStream _lock;
    private readonly string _temporary;
    private readonly FileStream _declarations;
    private readonly List<NameIndex.Entry> _entries = [];
    private readonly HashSet<Name> _names = [];
    private readonly Dictionary<string, RecordLocation> _records = new(StringComparer.Ordinal);
    private readonly IncrementalHash _content = IncrementalHash.CreateHash(HashAlgorithmName.SHA256);
    private readonly HashSet<Name> _quotients = [];
    private bool _done;

    private StoreWriter(string store, FileStream lockFile)
    {
        _store = store;
        _lock = lockFile;
        _temporary = Path.Combine(store, ".tmp-" + Convert.ToHexStringLower(RandomNumberGenerator.GetBytes(8)));
        Directory.CreateDirectory(_temporary);
        _declarations = new FileStream(Path.Combine(_temporary, StoreFormat.DeclarationsFile), FileMode.CreateNew, FileAccess.ReadWrite, FileShare.None, 1 << 16);
        _declarations.Write(new byte[StoreFormat.HeaderSize]);
    }

    /// <summary>Starts a new version of the store in <paramref name="storeDirectory"/>, creating the directory if needed.</summary>
    /// <exception cref="IOException">Another writer is writing the store.</exception>
    public static StoreWriter Create(string storeDirectory)
    {
        ArgumentNullException.ThrowIfNull(storeDirectory);
        var store = Path.GetFullPath(storeDirectory);
        Directory.CreateDirectory(store);
        FileStream lockFile;
        try
        {
            lockFile = new FileStream(Path.Combine(store, StoreFormat.LockFile), FileMode.OpenOrCreate, FileAccess.ReadWrite, FileShare.None);
        }
        catch (IOException ex)
        {
            throw new IOException($"{store}: another import is writing this store", ex);
        }
        // On Unix, .NET takes an flock for FileShare.None, so a second writer fails there too.
        try
        {
            DeleteTemporaries(store);
            return new StoreWriter(store, lockFile);
        }
        catch
        {
            lockFile.Dispose();
            throw;
        }
    }

    /// <summary>The number of records written.</summary>
    public int Declarations => _records.Count;

    /// <summary>The number of constants written.</summary>
    public int Constants => _entries.Count;

    /// <summary>Whether a constant of that name has been written.</summary>
    public bool Contains(Name name) => _names.Contains(name);

    /// <summary>Appends a declaration. Identical records are stored once.</summary>
    /// <exception cref="InvalidOperationException">A constant of the declaration is already in the store.</exception>
    public void Add(Declaration declaration)
    {
        ArgumentNullException.ThrowIfNull(declaration);
        ObjectDisposedException.ThrowIf(_done, this);
        foreach (var c in declaration.Constants)
        {
            if (_names.Contains(c.Name))
            {
                throw new InvalidOperationException($"'{c.Name}' is already in the store");
            }
        }
        var record = RecordCodec.Encode(declaration);
        var hash = SHA256.HashData(record);
        var key = Convert.ToHexStringLower(hash);
        if (!_records.TryGetValue(key, out var location))
        {
            Span<byte> length = stackalloc byte[4];
            BinaryPrimitives.WriteInt32LittleEndian(length, record.Length);
            _declarations.Write(length);
            location = new RecordLocation(_declarations.Position, record.Length);
            _declarations.Write(record);
            _records.Add(key, location);
            _content.AppendData(hash);
        }
        foreach (var c in declaration.Constants)
        {
            _names.Add(c.Name);
            _entries.Add(new NameIndex.Entry(NameIndex.Key(c.Name), c.Kind, location));
            if (c is QuotInfo)
            {
                _quotients.Add(c.Name);
            }
        }
    }

    /// <summary>
    /// Finishes the version and makes it the store's current one.
    /// </summary>
    /// <param name="sources">The files the declarations came from.</param>
    /// <param name="lean">Their Lean version.</param>
    /// <param name="lean4Export">Their lean4export format version.</param>
    /// <param name="mode"><see cref="Manifest.Trusted"/> or <see cref="Manifest.Verified"/>.</param>
    /// <param name="verifiedBy">In verified mode, the toolchain identity that checked them.</param>
    /// <returns>The version directory's name.</returns>
    public string Commit(IReadOnlyList<ManifestSource> sources, string lean, string lean4Export, string mode, string? verifiedBy)
    {
        ObjectDisposedException.ThrowIf(_done, this);
        var manifest = new Manifest(StoreFormat.Version, lean, lean4Export, sources, mode, verifiedBy, _quotients.Count == 4, _records.Count, _entries.Count);
        var manifestBytes = manifest.ToBytes();

        long length = _declarations.Length;
        Span<byte> header = stackalloc byte[StoreFormat.HeaderSize];
        StoreFormat.WriteHeader(header, StoreFormat.DeclarationsMagic, length);
        _declarations.Position = 0;
        _declarations.Write(header);
        _declarations.Flush(flushToDisk: true);
        _declarations.Dispose();
        NameIndex.Write(Path.Combine(_temporary, StoreFormat.IndexFile), _entries);
        File.WriteAllBytes(Path.Combine(_temporary, StoreFormat.ManifestFile), manifestBytes);

        _content.AppendData(manifestBytes);
        var version = StoreFormat.VersionPrefix + Convert.ToHexStringLower(_content.GetHashAndReset())[..12];
        var target = Path.Combine(_store, version);
        if (Directory.Exists(target))
        {
            // The same content, written before: keep the version readers may already hold.
            Directory.Delete(_temporary, recursive: true);
        }
        else
        {
            Directory.Move(_temporary, target);
        }
        WriteCurrent(version);
        DeleteOtherVersions(version);
        Finish();
        return version;
    }

    /// <summary>Discards an uncommitted version and releases the store.</summary>
    public void Dispose()
    {
        if (_done)
        {
            return;
        }
        _declarations.Dispose();
        try
        {
            Directory.Delete(_temporary, recursive: true);
        }
        catch (Exception ex) when (ex is IOException or UnauthorizedAccessException)
        {
            // The next writer deletes it.
        }
        Finish();
    }

    private void Finish()
    {
        _done = true;
        _content.Dispose();
        _lock.Dispose();
    }

    /// <summary>Replaces <c>current</c> by renaming a new file over it, which readers see whole or not at all.</summary>
    private void WriteCurrent(string version)
    {
        var path = Path.Combine(_store, StoreFormat.CurrentFile);
        var temporary = path + ".tmp";
        File.WriteAllText(temporary, version + "\n");
        for (int attempt = 0; ; attempt++)
        {
            try
            {
                File.Move(temporary, path, overwrite: true);
                return;
            }
            catch (IOException) when (attempt < 20)
            {
                // A reader has current open for a moment on Windows.
                Thread.Sleep(50);
            }
        }
    }

    /// <summary>
    /// Deletes every other version that can be deleted. Readers open their files with delete sharing, so a version can be
    /// deleted while it is read: on Unix its files live on until the last reader closes them, and on Windows a version
    /// whose files are still open stays until a later import.
    /// </summary>
    private void DeleteOtherVersions(string keep)
    {
        foreach (var directory in Directory.EnumerateDirectories(_store))
        {
            var name = Path.GetFileName(directory);
            if (name == keep || !StoreFormat.IsVersionName(name))
            {
                continue;
            }
            try
            {
                Directory.Delete(directory, recursive: true);
            }
            catch (Exception ex) when (ex is IOException or UnauthorizedAccessException)
            {
            }
        }
    }

    /// <summary>Temporary directories of writers that did not finish; only called while holding the store's lock.</summary>
    private static void DeleteTemporaries(string store)
    {
        foreach (var directory in Directory.EnumerateDirectories(store, ".tmp-*"))
        {
            try
            {
                Directory.Delete(directory, recursive: true);
            }
            catch (Exception ex) when (ex is IOException or UnauthorizedAccessException)
            {
            }
        }
    }
}
