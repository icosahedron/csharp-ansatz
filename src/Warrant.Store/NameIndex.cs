using System.Buffers;
using System.Buffers.Binary;
using System.IO.MemoryMappedFiles;
using Warrant.Cic;

namespace Warrant.Store;

/// <summary>Where a record is in <c>decls.bin</c>.</summary>
/// <param name="Offset">The offset of its first byte.</param>
/// <param name="Length">Its length.</param>
public readonly record struct RecordLocation(long Offset, int Length);

/// <summary>
/// <c>names.idx</c> (KTD17): after the header, the entry count, then fixed-size entries sorted by name key, then the keys.
/// A name's key is its components from the root, each a tag byte (1 string, 2 number) and a varint (the UTF-8 length, or
/// the number), the string's bytes following; keys compare as bytes, so the order is the same everywhere and needs no
/// parsing of names.
/// </summary>
/// <remarks>
/// <code>
/// header(16) count:u32 reserved:u32
/// entry(32)  = keyOffset:i64 keyLength:i32 kind:u8 pad:3 recordOffset:i64 recordLength:i32 pad:4
/// keys       = the keys, which keyOffset counts from the end of the entries
/// </code>
/// </remarks>
internal static class NameIndex
{
    public const int EntrySize = 32;

    public const int EntriesStart = StoreFormat.HeaderSize + 8;

    /// <summary>A name's key.</summary>
    public static byte[] Key(Name name)
    {
        var components = name.Components();
        var writer = new ByteWriter();
        foreach (var c in components)
        {
            if (c.Kind == NameKind.Str)
            {
                writer.Byte(1);
                writer.String(c.StringComponent);
            }
            else
            {
                writer.Byte(2);
                writer.VarUInt(c.NumericComponent);
            }
        }
        return writer.WrittenSpan.ToArray();
    }

    public sealed record Entry(byte[] Key, ConstantKind Kind, RecordLocation Record);

    /// <summary>Writes the index file for the entries, which must have distinct keys.</summary>
    public static void Write(string path, List<Entry> entries)
    {
        entries.Sort((a, b) => a.Key.AsSpan().SequenceCompareTo(b.Key));
        long keyBytes = 0;
        foreach (var e in entries)
        {
            keyBytes += e.Key.Length;
        }
        long length = EntriesStart + (long)EntrySize * entries.Count + keyBytes;
        using var file = new FileStream(path, FileMode.CreateNew, FileAccess.Write, FileShare.None, 1 << 16);
        Span<byte> header = stackalloc byte[EntriesStart];
        StoreFormat.WriteHeader(header, StoreFormat.IndexMagic, length);
        BinaryPrimitives.WriteUInt32LittleEndian(header[16..], (uint)entries.Count);
        BinaryPrimitives.WriteUInt32LittleEndian(header[20..], 0);
        file.Write(header);
        Span<byte> entry = stackalloc byte[EntrySize];
        long keyOffset = 0;
        foreach (var e in entries)
        {
            entry.Clear();
            BinaryPrimitives.WriteInt64LittleEndian(entry, keyOffset);
            BinaryPrimitives.WriteInt32LittleEndian(entry[8..], e.Key.Length);
            entry[12] = (byte)e.Kind;
            BinaryPrimitives.WriteInt64LittleEndian(entry[16..], e.Record.Offset);
            BinaryPrimitives.WriteInt32LittleEndian(entry[24..], e.Record.Length);
            file.Write(entry);
            keyOffset += e.Key.Length;
        }
        foreach (var e in entries)
        {
            file.Write(e.Key);
        }
    }

    /// <summary>A mapped index, read-only; thread-safe.</summary>
    public sealed class Reader : IDisposable
    {
        private readonly string _path;
        private readonly MemoryMappedFile _map;
        private readonly MemoryMappedViewAccessor _view;
        private readonly long _length;
        private readonly long _keysStart;
        private readonly long _declarationsLength;

        /// <summary>Opens and checks an index whose records lie in a <c>decls.bin</c> of <paramref name="declarationsLength"/> bytes.</summary>
        /// <exception cref="StoreFormatException">The file is not a well-formed index.</exception>
        public Reader(string path, long declarationsLength)
        {
            _path = path;
            _declarationsLength = declarationsLength;
            var stream = new FileStream(path, FileMode.Open, FileAccess.Read, FileShare.Read | FileShare.Delete);
            try
            {
                _length = stream.Length;
                Span<byte> header = stackalloc byte[EntriesStart];
                int read = stream.ReadAtLeast(header, header.Length, throwOnEndOfStream: false);
                StoreFormat.CheckHeader(path, header[..read], StoreFormat.IndexMagic, _length, "store index");
                if (read < EntriesStart)
                {
                    throw new StoreFormatException(path, "the index ends inside its header");
                }
                Count = checked((int)BinaryPrimitives.ReadUInt32LittleEndian(header[16..]));
                _keysStart = EntriesStart + (long)EntrySize * Count;
                if (Count < 0 || _keysStart > _length)
                {
                    throw new StoreFormatException(path, $"the index claims {Count} entries, more than the file holds");
                }
                _map = MemoryMappedFile.CreateFromFile(stream, null, 0, MemoryMappedFileAccess.Read, HandleInheritability.None, leaveOpen: false);
            }
            catch
            {
                stream.Dispose();
                throw;
            }
            _view = _map.CreateViewAccessor(0, _length, MemoryMappedFileAccess.Read);
        }

        /// <summary>The number of entries.</summary>
        public int Count { get; }

        /// <summary>Finds a name's entry by binary search.</summary>
        /// <exception cref="StoreFormatException">An entry the search reads is malformed.</exception>
        public bool TryFind(Name name, out ConstantKind kind, out RecordLocation record)
        {
            var key = Key(name);
            int lo = 0, hi = Count - 1;
            var buffer = ArrayPool<byte>.Shared.Rent(256);
            try
            {
                while (lo <= hi)
                {
                    int mid = lo + ((hi - lo) >> 1);
                    long at = EntriesStart + (long)EntrySize * mid;
                    var (keyOffset, keyLength) = (_view.ReadInt64(at), _view.ReadInt32(at + 8));
                    if (keyOffset < 0 || keyLength < 0 || keyOffset > _length - _keysStart - keyLength)
                    {
                        throw new StoreFormatException(_path, $"entry {mid}'s key lies outside the file");
                    }
                    if (buffer.Length < keyLength)
                    {
                        ArrayPool<byte>.Shared.Return(buffer);
                        buffer = ArrayPool<byte>.Shared.Rent(keyLength);
                    }
                    _view.ReadArray(_keysStart + keyOffset, buffer, 0, keyLength);
                    int order = buffer.AsSpan(0, keyLength).SequenceCompareTo(key);
                    if (order == 0)
                    {
                        (kind, record) = EntryAt(mid, at);
                        return true;
                    }
                    if (order < 0)
                    {
                        lo = mid + 1;
                    }
                    else
                    {
                        hi = mid - 1;
                    }
                }
            }
            finally
            {
                ArrayPool<byte>.Shared.Return(buffer);
            }
            kind = default;
            record = default;
            return false;
        }

        private (ConstantKind, RecordLocation) EntryAt(int index, long at)
        {
            byte kind = _view.ReadByte(at + 12);
            long offset = _view.ReadInt64(at + 16);
            int length = _view.ReadInt32(at + 24);
            if (kind > (byte)ConstantKind.Recursor)
            {
                throw new StoreFormatException(_path, $"entry {index} has the constant kind {kind}");
            }
            if (offset < StoreFormat.HeaderSize + 4 || length < 0 || offset > _declarationsLength - length)
            {
                throw new StoreFormatException(_path, $"entry {index}'s record lies outside {StoreFormat.DeclarationsFile}");
            }
            return ((ConstantKind)kind, new RecordLocation(offset, length));
        }

        public void Dispose()
        {
            _view.Dispose();
            _map.Dispose();
        }
    }
}
