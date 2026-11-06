using System.Buffers;
using System.Buffers.Binary;
using System.Text;

namespace Warrant.Store;

/// <summary>A store file that is not what this Warrant reads: truncated, of another kind or format version, or malformed.</summary>
public sealed class StoreFormatException : Exception
{
    /// <summary>Creates the exception for a file.</summary>
    /// <param name="path">The file.</param>
    /// <param name="message">What is wrong with it.</param>
    public StoreFormatException(string path, string message)
        : base($"{path}: {message}") => FilePath = path;

    /// <summary>Creates the exception.</summary>
    public StoreFormatException()
        : this("", "the store is malformed")
    {
    }

    /// <summary>Creates the exception with a message.</summary>
    /// <param name="message">The message.</param>
    public StoreFormatException(string message)
        : base(message) => FilePath = "";

    /// <summary>Creates the exception with a message and a cause.</summary>
    /// <param name="message">The message.</param>
    /// <param name="innerException">The cause.</param>
    public StoreFormatException(string message, Exception innerException)
        : base(message, innerException) => FilePath = "";

    /// <summary>The file that is malformed.</summary>
    public string FilePath { get; }
}

/// <summary>
/// The parts every mapped store file shares (KTD17): a 16-byte header of a four-byte magic number, the format version and
/// the file's length, which a reader checks against the file before it reads anything else, because reading past the end
/// of a truncated mapped file raises SIGBUS on Unix instead of an exception.
/// </summary>
internal static class StoreFormat
{
    /// <summary>The format this Warrant writes and reads.</summary>
    public const int Version = 1;

    /// <summary>The header's size.</summary>
    public const int HeaderSize = 16;

    /// <summary><c>decls.bin</c>'s magic number, "WRTD".</summary>
    public static ReadOnlySpan<byte> DeclarationsMagic => "WRTD"u8;

    /// <summary><c>names.idx</c>'s magic number, "WRTI".</summary>
    public static ReadOnlySpan<byte> IndexMagic => "WRTI"u8;

    public const string DeclarationsFile = "decls.bin";

    public const string IndexFile = "names.idx";

    public const string ManifestFile = "manifest.json";

    public const string CurrentFile = "current";

    public const string LockFile = ".lock";

    /// <summary>The prefix of a version directory: <c>v1-</c> and twelve hex digits of the version's hash.</summary>
    public const string VersionPrefix = "v1-";

    /// <summary>Whether a name is a version directory's.</summary>
    public static bool IsVersionName(string name) =>
        name.Length == VersionPrefix.Length + 12 && name.StartsWith(VersionPrefix, StringComparison.Ordinal)
        && !name.AsSpan(VersionPrefix.Length).ContainsAnyExcept(LowerHex);

    private static readonly System.Buffers.SearchValues<char> LowerHex = System.Buffers.SearchValues.Create("0123456789abcdef");

    public static void WriteHeader(Span<byte> header, ReadOnlySpan<byte> magic, long length)
    {
        magic.CopyTo(header);
        BinaryPrimitives.WriteInt32LittleEndian(header[4..], Version);
        BinaryPrimitives.WriteInt64LittleEndian(header[8..], length);
    }

    /// <summary>Checks a header against the file's real length.</summary>
    /// <exception cref="StoreFormatException">The header is not this kind of file's, of this version, or of this length.</exception>
    public static void CheckHeader(string path, ReadOnlySpan<byte> header, ReadOnlySpan<byte> magic, long actualLength, string kind)
    {
        if (actualLength < HeaderSize || header.Length < HeaderSize)
        {
            throw new StoreFormatException(path, $"the file is {actualLength} bytes, too short for a {kind} header");
        }
        if (!header[..4].SequenceEqual(magic))
        {
            throw new StoreFormatException(path, $"not a {kind} file (wrong magic number)");
        }
        int version = BinaryPrimitives.ReadInt32LittleEndian(header[4..]);
        if (version != Version)
        {
            throw new StoreFormatException(path, version > Version
                ? $"format version {version} is newer than this Warrant reads ({Version})"
                : $"format version {version} is not one this Warrant reads ({Version})");
        }
        long length = BinaryPrimitives.ReadInt64LittleEndian(header[8..]);
        if (length != actualLength)
        {
            throw new StoreFormatException(path, $"the header records {length} bytes but the file has {actualLength}; it is truncated or was changed");
        }
    }
}

/// <summary>Appends little-endian values and LEB128 varints to a growable buffer.</summary>
internal sealed class ByteWriter
{
    private readonly ArrayBufferWriter<byte> _buffer = new(256);

    public int Length => _buffer.WrittenCount;

    public ReadOnlySpan<byte> WrittenSpan => _buffer.WrittenSpan;

    public void Clear() => _buffer.Clear();

    public void Byte(byte value)
    {
        _buffer.GetSpan(1)[0] = value;
        _buffer.Advance(1);
    }

    public void Bool(bool value) => Byte(value ? (byte)1 : (byte)0);

    public void VarUInt(ulong value)
    {
        var span = _buffer.GetSpan(10);
        int n = 0;
        while (value >= 0x80)
        {
            span[n++] = (byte)(value | 0x80);
            value >>= 7;
        }
        span[n++] = (byte)value;
        _buffer.Advance(n);
    }

    public void VarInt(int value)
    {
        ArgumentOutOfRangeException.ThrowIfNegative(value);
        VarUInt((ulong)value);
    }

    public void Bytes(ReadOnlySpan<byte> bytes)
    {
        VarInt(bytes.Length);
        bytes.CopyTo(_buffer.GetSpan(bytes.Length));
        _buffer.Advance(bytes.Length);
    }

    public void String(string value)
    {
        int count = Encoding.UTF8.GetByteCount(value);
        VarInt(count);
        Encoding.UTF8.GetBytes(value, _buffer.GetSpan(count));
        _buffer.Advance(count);
    }

    public void Append(ReadOnlySpan<byte> bytes)
    {
        bytes.CopyTo(_buffer.GetSpan(bytes.Length));
        _buffer.Advance(bytes.Length);
    }
}

/// <summary>Reads what <see cref="ByteWriter"/> wrote, with every read bounds-checked; a malformed record is a <see cref="StoreFormatException"/>.</summary>
internal ref struct ByteReader
{
    private static readonly UTF8Encoding StrictUtf8 = new(encoderShouldEmitUTF8Identifier: false, throwOnInvalidBytes: true);

    private readonly ReadOnlySpan<byte> _data;
    private readonly string _path;
    private readonly long _offset;
    private int _position;

    /// <param name="data">The bytes.</param>
    /// <param name="path">The file they came from, for messages.</param>
    /// <param name="offset">Where in the file they start, for messages.</param>
    public ByteReader(ReadOnlySpan<byte> data, string path, long offset)
    {
        _data = data;
        _path = path;
        _offset = offset;
        _position = 0;
    }

    public readonly bool AtEnd => _position == _data.Length;

    public readonly StoreFormatException Malformed(string what) =>
        new(_path, $"the record at byte {_offset} is malformed: {what} (at its byte {_position})");

    public byte Byte()
    {
        if (_position >= _data.Length)
        {
            throw Malformed("it ends early");
        }
        return _data[_position++];
    }

    public bool Bool() => Byte() switch
    {
        0 => false,
        1 => true,
        var b => throw Malformed($"{b} is not a boolean"),
    };

    public ulong VarUInt()
    {
        ulong value = 0;
        for (int shift = 0; shift < 64; shift += 7)
        {
            byte b = Byte();
            if (shift == 63 && b > 1)
            {
                throw Malformed("a number overflows 64 bits");
            }
            value |= (ulong)(b & 0x7F) << shift;
            if (b < 0x80)
            {
                return value;
            }
        }
        throw Malformed("a number overflows 64 bits");
    }

    public int VarInt()
    {
        ulong value = VarUInt();
        return value <= int.MaxValue ? (int)value : throw Malformed($"{value} is out of range");
    }

    /// <summary>An index into a table of <paramref name="count"/> entries.</summary>
    public int Index(int count, string table)
    {
        int index = VarInt();
        return index < count ? index : throw Malformed($"{table} index {index} is not below {count}");
    }

    public ReadOnlySpan<byte> Bytes()
    {
        int length = VarInt();
        if (length > _data.Length - _position)
        {
            throw Malformed("it ends early");
        }
        var bytes = _data.Slice(_position, length);
        _position += length;
        return bytes;
    }

    public string String()
    {
        var bytes = Bytes();
        try
        {
            return StrictUtf8.GetString(bytes);
        }
        catch (DecoderFallbackException)
        {
            throw Malformed("a string is not UTF-8");
        }
    }
}
