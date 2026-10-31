namespace LeanSharp.Lean4Export;

/// <summary>Splits a byte stream into newline-terminated lines without decoding them.</summary>
/// <remarks>
/// The returned memory is only valid until the next call to <see cref="TryReadLine"/>.
/// </remarks>
internal sealed class LineReader
{
    private readonly Stream _stream;
    private byte[] _buffer = new byte[1 << 16];
    private int _start;
    private int _end;
    private bool _eof;

    public LineReader(Stream stream) => _stream = stream;

    /// <summary>The 1-based number of the line most recently returned.</summary>
    public long LineNumber { get; private set; }

    public bool TryReadLine(out ReadOnlyMemory<byte> line)
    {
        while (true)
        {
            int nl = _buffer.AsSpan(_start, _end - _start).IndexOf((byte)'\n');
            if (nl >= 0)
            {
                line = TrimCarriageReturn(_buffer.AsMemory(_start, nl));
                _start += nl + 1;
                LineNumber++;
                return true;
            }
            if (_eof)
            {
                if (_start < _end)
                {
                    line = TrimCarriageReturn(_buffer.AsMemory(_start, _end - _start));
                    _start = _end;
                    LineNumber++;
                    return true;
                }
                line = default;
                return false;
            }
            Fill();
        }
    }

    private void Fill()
    {
        // Move the partial line to the front, growing the buffer if it is full.
        int pending = _end - _start;
        if (_start > 0)
        {
            Buffer.BlockCopy(_buffer, _start, _buffer, 0, pending);
            _start = 0;
            _end = pending;
        }
        if (_end == _buffer.Length)
        {
            Array.Resize(ref _buffer, _buffer.Length * 2);
        }
        int read = _stream.Read(_buffer, _end, _buffer.Length - _end);
        if (read == 0)
        {
            _eof = true;
        }
        _end += read;
    }

    private static ReadOnlyMemory<byte> TrimCarriageReturn(ReadOnlyMemory<byte> line) =>
        line.Length > 0 && line.Span[^1] == (byte)'\r' ? line[..^1] : line;
}
