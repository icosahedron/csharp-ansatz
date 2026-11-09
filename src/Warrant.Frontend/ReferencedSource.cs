using System.Security.Cryptography;
using System.Text;
using Microsoft.CodeAnalysis.CSharp;

namespace Warrant.Frontend;

/// <summary>
/// A referenced project's compilation, rebuilt from the source its own build recorded (#32; docs/m5a/07, "Types from
/// referenced projects"). A <c>[Closed]</c> class's shape and construction checks need its source, which the project being
/// verified sees only as metadata. Every project that imports <c>Warrant.Build</c> writes a record after its compile:
/// <c>obj/&lt;configuration&gt;/&lt;framework&gt;/warrant.source</c>, holding its assembly name, its compiler arguments and the
/// SHA-256 of every file those arguments read, hashed before and after the compile and written only when both agree.
/// <see cref="Load"/> reads those files, hashes them and declines if any differs, then compiles from the bytes it hashed
/// (#127), so the source checked is the source the referenced assembly was compiled from. The files include the assemblies
/// the arguments reference and the analyzers and generators they load (#51).
/// </summary>
/// <remarks>
/// The record's format, one entry per line, as <c>Warrant.Build.targets</c> writes it:
/// <code>
/// warrant-source 2
/// assembly=&lt;assembly name&gt;
/// args=&lt;full path of the argument file&gt;
/// project=&lt;full path of the project directory&gt;
/// file=&lt;SHA-256, hex&gt;|&lt;full path&gt;
/// </code>
/// Opening a record only reads it; the source is hashed and compiled by <see cref="Load"/>, which a run calls only for an
/// assembly whose closed class it uses, so a referenced project that cannot be reproduced costs nothing unless it matters.
/// Format 1, from a Warrant.Build before #51, lists no referenced assemblies or analyzers; <see cref="Load"/> declines it
/// and says to rebuild the project. A build in which the project is up to date rewrites such a record in format 2 when its
/// sources are unchanged.
/// </remarks>
public sealed class ReferencedSource
{
    private const string Header = "warrant-source 2";
    private const string OldHeader = "warrant-source 1";

    private readonly string _recordPath;
    private readonly string _argsFile;
    private readonly string _project;
    private readonly Dictionary<string, string> _hashes;
    private readonly bool _oldFormat;
    private readonly string? _problem;
    private CSharpCompilation? _compilation;

    private ReferencedSource(string recordPath, string? assemblyName, string argsFile, string project, Dictionary<string, string> hashes, bool oldFormat, string? problem)
    {
        _recordPath = recordPath;
        AssemblyName = assemblyName;
        _argsFile = argsFile;
        _project = project;
        _hashes = hashes;
        _oldFormat = oldFormat;
        _problem = problem;
    }

    /// <summary>
    /// The referenced assembly's name, or null when the record does not name one; such a record can never be used, because
    /// it cannot be matched to a reference.
    /// </summary>
    public string? AssemblyName { get; }

    /// <summary>
    /// Reads a record. A record that is not one Warrant can use (another format, an unknown line, a missing entry) is still
    /// opened, and <see cref="Load"/> reports why, so a referenced project that cannot be used costs nothing unless one of
    /// its closed classes is used (#120).
    /// </summary>
    /// <param name="recordPath">The record.</param>
    /// <returns>The record, not yet checked against the files it names.</returns>
    public static ReferencedSource Open(string recordPath)
    {
        ArgumentNullException.ThrowIfNull(recordPath);
        var lines = File.ReadAllLines(recordPath, Encoding.UTF8).Where(l => l.Length > 0).ToList();
        string? assembly = lines.Where(l => l.StartsWith("assembly=", StringComparison.Ordinal)).Select(l => l["assembly=".Length..]).FirstOrDefault();
        if (lines.Count == 0 || (lines[0] != Header && lines[0] != OldHeader))
        {
            return Unusable(recordPath, assembly, $"{recordPath}: not a Warrant source record this Warrant can read");
        }
        string? argsFile = null, project = null;
        var hashes = new Dictionary<string, string>(PathComparer);
        foreach (var line in lines.Skip(1))
        {
            int eq = line.IndexOf('=', StringComparison.Ordinal);
            var (key, value) = eq < 0 ? (line, "") : (line[..eq], line[(eq + 1)..]);
            switch (key)
            {
                case "assembly":
                    assembly = value;
                    break;
                case "args":
                    argsFile = value;
                    break;
                case "project":
                    project = value;
                    break;
                case "file" when value.IndexOf('|', StringComparison.Ordinal) is var bar and > 0:
                    hashes[Path.GetFullPath(value[(bar + 1)..])] = value[..bar];
                    break;
                default:
                    return Unusable(recordPath, assembly, $"{recordPath}: unexpected line '{line}'");
            }
        }
        if (string.IsNullOrEmpty(assembly) || string.IsNullOrEmpty(argsFile) || string.IsNullOrEmpty(project))
        {
            return Unusable(recordPath, assembly, $"{recordPath}: the assembly, args or project line is missing");
        }
        return new ReferencedSource(recordPath, assembly, Path.GetFullPath(argsFile), Path.GetFullPath(project), hashes, lines[0] == OldHeader, null);
    }

    private static ReferencedSource Unusable(string recordPath, string? assembly, string problem) =>
        new(recordPath, string.IsNullOrEmpty(assembly) ? null : assembly, "", "", new Dictionary<string, string>(PathComparer), false, problem);

    /// <summary>
    /// Checks that the files the record names are unchanged and rebuilds the compilation, once; later calls return the
    /// first call's compilation.
    /// </summary>
    /// <param name="pathBase">The directory tree paths are made relative to: the directory of the project being verified.</param>
    /// <returns>The referenced project's compilation, generated sources included, with no errors.</returns>
    /// <exception cref="InvalidDataException">
    /// A file the compiler read changed or is missing from the record, the arguments compile another assembly, or the
    /// source does not compile.
    /// </exception>
    public CSharpCompilation Load(string pathBase)
    {
        ArgumentNullException.ThrowIfNull(pathBase);
        if (_compilation is not null)
        {
            return _compilation;
        }
        if (_problem is not null)
        {
            throw new InvalidDataException(_problem);
        }
        if (_oldFormat)
        {
            throw new InvalidDataException(
                $"{_recordPath} was written by an older Warrant.Build and does not list {AssemblyName}'s references; build {AssemblyName} again, or rebuild it if that does not rewrite the record");
        }

        // Every file the compiler read: the arguments themselves, the sources, the generators' additional files, the
        // analyzer configuration, the referenced assemblies, and the analyzer and generator assemblies with every assembly
        // beside them, which the generator loader resolves their dependencies from (#51). Each must be in the record with
        // the hash it had when the assembly was compiled. A reference decides what the source means (a base class, a
        // constant) and a generator adds source, so either changing changes what is checked.
        //
        // Each file is read once, and the compilation is built from the bytes that were hashed (#127): an edit after the
        // check cannot reach it. The one exception is Roslyn's AnalyzerFileReference, which reads an analyzer's metadata from
        // disk to find its generator types (the code it runs comes from these bytes), so the analyzers are hashed again
        // once the generators have run.
        var snapshot = new Dictionary<string, byte[]>(PathComparer);
        byte[] Read(string path)
        {
            var full = Path.GetFullPath(path);
            if (!snapshot.TryGetValue(full, out var bytes))
            {
                snapshot[full] = bytes = Checked(full);
            }
            return bytes;
        }

        var argsLines = CompilationFactory.Lines(Read(_argsFile));
        if (argsLines.Any(l => l.StartsWith('@')))
        {
            throw new InvalidDataException($"{_argsFile}: a response file (@file) is not covered by {AssemblyName}'s source record");
        }
        var args = CompilationFactory.ParseCscArgs(_argsFile, argsLines, _project);
        foreach (var file in ReadFiles(args))
        {
            Read(file);
        }

        var compilation = CompilationFactory.FromCscArgs(_argsFile, _project, pathBase, Read, out var generatorProblems);
        foreach (var analyzer in Analyzers(args))
        {
            Checked(analyzer);
        }
        if (!string.Equals(compilation.AssemblyName, AssemblyName, StringComparison.Ordinal))
        {
            throw new InvalidDataException($"{_recordPath}: the arguments compile '{compilation.AssemblyName}', not '{AssemblyName}'");
        }
        if (CompilationFactory.Failure(compilation, generatorProblems) is { } failure)
        {
            throw new InvalidDataException($"{AssemblyName}'s recorded source does not compile: {failure.Message}");
        }
        return _compilation = compilation;
    }

    /// <summary>The full paths of the files an argument list makes the compiler and the generator loader read.</summary>
    private List<string> ReadFiles(CSharpCommandLineArguments args)
    {
        var read = new List<string>();
        read.AddRange(args.SourceFiles.Select(f => f.Path));
        read.AddRange(args.AdditionalFiles.Select(f => f.Path));
        read.AddRange(args.AnalyzerConfigPaths);
        read.AddRange(args.MetadataReferences.Select(r => r.Reference));
        foreach (var analyzer in Analyzers(args))
        {
            read.Add(analyzer);
            if (Path.GetDirectoryName(analyzer) is { } directory && Directory.Exists(directory))
            {
                read.AddRange(Directory.EnumerateFiles(directory, "*.dll"));
            }
        }
        return read.Select(f => Path.GetFullPath(Path.Combine(_project, f))).Distinct(PathComparer).Order(PathComparer).ToList();
    }

    private IEnumerable<string> Analyzers(CSharpCommandLineArguments args) =>
        args.AnalyzerReferences.Select(r => Path.GetFullPath(Path.Combine(_project, r.FilePath))).Distinct(PathComparer);

    /// <summary>A file's bytes, read once, after checking that they hash to what the record says.</summary>
    private byte[] Checked(string full)
    {
        if (!_hashes.TryGetValue(full, out var recorded))
        {
            throw new InvalidDataException($"{_recordPath}: {full}, which {AssemblyName} is compiled from, is not in the record; build {AssemblyName} again");
        }
        byte[] bytes;
        try
        {
            bytes = File.ReadAllBytes(full);
        }
        catch (Exception e) when (e is IOException or UnauthorizedAccessException)
        {
            throw new InvalidDataException($"{full} changed since {AssemblyName} was compiled; build {AssemblyName} again", e);
        }
        if (!string.Equals(Convert.ToHexString(SHA256.HashData(bytes)), recorded, StringComparison.OrdinalIgnoreCase))
        {
            throw new InvalidDataException($"{full} changed since {AssemblyName} was compiled; build {AssemblyName} again");
        }
        return bytes;
    }

    private static StringComparer PathComparer =>
        OperatingSystem.IsWindows() || OperatingSystem.IsMacOS() ? StringComparer.OrdinalIgnoreCase : StringComparer.Ordinal;
}
