using System.IO.Compression;
using Warrant.Cic;

namespace Warrant.Lean4Export;

/// <summary>Convenience entry points for lean4export files.</summary>
public static class Lean4Export
{
    /// <summary>
    /// Opens an export file for reading, transparently decompressing gzip (detected by its magic
    /// bytes, not the file extension).
    /// </summary>
    public static Stream OpenRead(string path)
    {
        var file = new FileStream(path, FileMode.Open, FileAccess.Read, FileShare.Read, 1 << 16, FileOptions.SequentialScan);
        Span<byte> magic = stackalloc byte[2];
        int n = file.ReadAtLeast(magic, 2, throwOnEndOfStream: false);
        file.Position = 0;
        return n == 2 && magic[0] == 0x1F && magic[1] == 0x8B
            ? new GZipStream(file, CompressionMode.Decompress)
            : file;
    }

    /// <summary>Reads a whole export file.</summary>
    /// <exception cref="Lean4ExportFormatException">The file is malformed.</exception>
    public static ExportFile ReadFile(string path)
    {
        using var reader = new Lean4ExportReader(OpenRead(path));
        var declarations = reader.ReadDeclarations().ToList();
        return new ExportFile(reader.Metadata, declarations, reader.Statistics);
    }

    /// <summary>Reads an export file into a new environment (without type checking).</summary>
    /// <exception cref="Lean4ExportFormatException">The file is malformed.</exception>
    /// <exception cref="DuplicateConstantException">The file declares a constant twice.</exception>
    public static Env LoadEnv(string path)
    {
        var env = new Env();
        using var reader = new Lean4ExportReader(OpenRead(path));
        foreach (var d in reader.ReadDeclarations())
        {
            env.Add(d);
        }
        return env;
    }
}
