namespace Warrant.Lean4Export;

/// <summary>The <c>meta</c> object that starts every lean4export file.</summary>
/// <param name="ExporterName">The exporting tool (for example <c>lean4export</c>).</param>
/// <param name="ExporterVersion">The exporting tool's version.</param>
/// <param name="LeanGithash">The commit of the Lean toolchain the data came from.</param>
/// <param name="LeanVersion">The version of the Lean toolchain the data came from.</param>
/// <param name="FormatVersion">The export format version (for example <c>3.1.0</c>).</param>
public sealed record ExportMetadata(
    string ExporterName,
    string ExporterVersion,
    string LeanGithash,
    string LeanVersion,
    string FormatVersion);

/// <summary>Counts of the records read from or written to an export.</summary>
/// <param name="Names">Name table entries (excluding the implicit anonymous name).</param>
/// <param name="Levels">Level table entries (excluding the implicit level zero).</param>
/// <param name="Exprs">Expression table entries.</param>
/// <param name="DeclarationLines">Declaration lines.</param>
public sealed record ExportStatistics(int Names, int Levels, int Exprs, int DeclarationLines);

/// <summary>The fully read contents of an export file.</summary>
/// <param name="Metadata">The file's metadata.</param>
/// <param name="Declarations">The declarations, in file order.</param>
/// <param name="Statistics">Record counts.</param>
public sealed record ExportFile(
    ExportMetadata Metadata,
    IReadOnlyList<Warrant.Cic.Declaration> Declarations,
    ExportStatistics Statistics);

/// <summary>A malformed or unsupported lean4export file.</summary>
public sealed class Lean4ExportFormatException : Exception
{
    /// <summary>Creates the exception for a problem on <paramref name="lineNumber"/> (1-based).</summary>
    public Lean4ExportFormatException(long lineNumber, string message, Exception? innerException = null)
        : base($"line {lineNumber}: {message}", innerException) => LineNumber = lineNumber;

    /// <summary>Creates the exception.</summary>
    public Lean4ExportFormatException()
    {
    }

    /// <summary>Creates the exception with a message.</summary>
    public Lean4ExportFormatException(string message)
        : base(message)
    {
    }

    /// <summary>Creates the exception with a message and inner exception.</summary>
    public Lean4ExportFormatException(string message, Exception innerException)
        : base(message, innerException)
    {
    }

    /// <summary>The 1-based line on which the problem was found (0 if unknown).</summary>
    public long LineNumber { get; }
}
