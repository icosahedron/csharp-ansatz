using System.Buffers;
using System.Buffers.Binary;
using Microsoft.Win32.SafeHandles;
using Warrant.Cic;

namespace Warrant.Store;

/// <summary>
/// Reads one version of a store (KTD17): the one <c>current</c> named when it was opened, which it keeps until it is
/// disposed, whatever later imports do. <c>names.idx</c> is mapped read-only; records are read from <c>decls.bin</c> by
/// offset. Both files are opened with read and delete sharing, so a later import can replace the store and delete this
/// version while it is read. Thread-safe.
/// </summary>
public sealed class StoreReader : IDisposable
{
    private readonly SafeFileHandle _declarations;
    private readonly NameIndex.Reader _index;

    private StoreReader(string store, string version)
    {
        StoreDirectory = store;
        Version = version;
        VersionDirectory = Path.Combine(store, version);
        Manifest = Manifest.Read(Path.Combine(VersionDirectory, StoreFormat.ManifestFile));
        DeclarationsPath = Path.Combine(VersionDirectory, StoreFormat.DeclarationsFile);
        _declarations = File.OpenHandle(DeclarationsPath, FileMode.Open, FileAccess.Read, FileShare.Read | FileShare.Delete);
        try
        {
            DeclarationsLength = RandomAccess.GetLength(_declarations);
            Span<byte> header = stackalloc byte[StoreFormat.HeaderSize];
            int read = RandomAccess.Read(_declarations, header, 0);
            StoreFormat.CheckHeader(DeclarationsPath, header[..read], StoreFormat.DeclarationsMagic, DeclarationsLength, "store declarations");
            _index = new NameIndex.Reader(Path.Combine(VersionDirectory, StoreFormat.IndexFile), DeclarationsLength);
            if (_index.Count != Manifest.Constants)
            {
                _index.Dispose();
                throw new StoreFormatException(Path.Combine(VersionDirectory, StoreFormat.IndexFile),
                    $"the index has {_index.Count} constants but the manifest says {Manifest.Constants}");
            }
        }
        catch
        {
            _declarations.Dispose();
            throw;
        }
    }

    /// <summary>The store's directory.</summary>
    public string StoreDirectory { get; }

    /// <summary>The version this reader holds, such as <c>v1-3f9a12c4be07</c>.</summary>
    public string Version { get; }

    /// <summary>The version's directory.</summary>
    public string VersionDirectory { get; }

    /// <summary>The version's manifest.</summary>
    public Manifest Manifest { get; }

    /// <summary>The number of constants the index maps.</summary>
    public int ConstantCount => _index.Count;

    private string DeclarationsPath { get; }

    private long DeclarationsLength { get; }

    /// <summary>Opens the store's current version.</summary>
    /// <exception cref="StoreFormatException">The store or its current version is malformed.</exception>
    /// <exception cref="IOException">The directory is not a store.</exception>
    public static StoreReader Open(string storeDirectory)
    {
        ArgumentNullException.ThrowIfNull(storeDirectory);
        var store = Path.GetFullPath(storeDirectory);
        for (int attempt = 0; ; attempt++)
        {
            var version = ReadCurrent(store);
            try
            {
                return new StoreReader(store, version);
            }
            catch (Exception ex) when (attempt < 5 && ex is FileNotFoundException or DirectoryNotFoundException)
            {
                // An import replaced the store and deleted that version between reading current and opening it.
            }
        }
    }

    private static string ReadCurrent(string store)
    {
        var path = Path.Combine(store, StoreFormat.CurrentFile);
        string text;
        try
        {
            using var stream = new FileStream(path, FileMode.Open, FileAccess.Read, FileShare.ReadWrite | FileShare.Delete);
            using var reader = new StreamReader(stream);
            text = reader.ReadToEnd().Trim();
        }
        catch (Exception ex) when (ex is FileNotFoundException or DirectoryNotFoundException)
        {
            throw new IOException($"{store} is not a Warrant store: it has no '{StoreFormat.CurrentFile}' file", ex);
        }
        return StoreFormat.IsVersionName(text) ? text : throw new StoreFormatException(path, $"'{text}' is not a store version");
    }

    /// <summary>Finds the record that holds a constant.</summary>
    /// <exception cref="StoreFormatException">The index entry is malformed.</exception>
    public bool TryFind(Name name, out ConstantKind kind, out RecordLocation record)
    {
        ArgumentNullException.ThrowIfNull(name);
        return _index.TryFind(name, out kind, out record);
    }

    /// <summary>
    /// The name of the index's entry at <paramref name="index"/>, from 0 to <see cref="ConstantCount"/> - 1, in the index's
    /// order, which is not the stored order: for choosing constants without reading their records (<c>warrant sample-store</c>).
    /// </summary>
    /// <exception cref="ArgumentOutOfRangeException"><paramref name="index"/> is out of range.</exception>
    /// <exception cref="StoreFormatException">The entry's key is malformed.</exception>
    public Name NameAt(int index) => _index.NameAt(index);

    /// <summary>Reads and decodes a record.</summary>
    /// <exception cref="StoreFormatException">The record is malformed.</exception>
    public Declaration Read(RecordLocation record, NameInterner? interner = null)
    {
        if (record.Offset < StoreFormat.HeaderSize || record.Length < 0 || record.Offset > DeclarationsLength - record.Length)
        {
            throw new StoreFormatException(DeclarationsPath, $"no record of {record.Length} bytes at byte {record.Offset}");
        }
        var buffer = ArrayPool<byte>.Shared.Rent(record.Length);
        try
        {
            var span = buffer.AsSpan(0, record.Length);
            ReadExactly(span, record.Offset);
            return RecordCodec.Decode(span, interner, DeclarationsPath, record.Offset);
        }
        finally
        {
            ArrayPool<byte>.Shared.Return(buffer);
        }
    }

    /// <summary>Every record, in the order the import stored them.</summary>
    /// <exception cref="StoreFormatException">A record is malformed.</exception>
    public IEnumerable<Declaration> ReadAll(NameInterner? interner = null)
    {
        long position = StoreFormat.HeaderSize;
        var lengthBytes = new byte[4];
        while (position < DeclarationsLength)
        {
            if (DeclarationsLength - position < 4)
            {
                throw new StoreFormatException(DeclarationsPath, $"a record's length at byte {position} is cut off");
            }
            ReadExactly(lengthBytes, position);
            int length = BinaryPrimitives.ReadInt32LittleEndian(lengthBytes);
            position += 4;
            yield return Read(new RecordLocation(position, length), interner);
            position += length;
        }
    }

    private void ReadExactly(Span<byte> span, long offset)
    {
        while (span.Length > 0)
        {
            int read = RandomAccess.Read(_declarations, span, offset);
            if (read == 0)
            {
                throw new StoreFormatException(DeclarationsPath, $"the file ends at byte {offset}, inside a record");
            }
            span = span[read..];
            offset += read;
        }
    }

    /// <summary>Closes the version's files.</summary>
    public void Dispose()
    {
        _index.Dispose();
        _declarations.Dispose();
    }
}
