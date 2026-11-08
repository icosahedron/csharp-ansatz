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
/// <see cref="Load"/> hashes those files again and declines if any differs, so the source checked is the source the
/// referenced assembly was compiled from, unless a file changed and changed back in between. The files include the
/// assemblies the arguments reference and the analyzers and generators they load (#51).
/// </summary>
/// <remarks>
/// The record's format, one entry per line, as <c>Warrant.Build.targets</c> writes it:
/// <code>
/// warrant-source 1
/// assembly=&lt;assembly name&gt;
/// args=&lt;full path of the argument file&gt;
/// project=&lt;full path of the project directory&gt;
/// file=&lt;SHA-256, hex&gt;|&lt;full path&gt;
/// </code>
/// Opening a record only reads it; the source is hashed and compiled by <see cref="Load"/>, which a run calls only for an
/// assembly whose closed class it uses, so a referenced project that cannot be reproduced costs nothing unless it matters.
/// </remarks>
public sealed class ReferencedSource
{
    private const string Header = "warrant-source 1";

    private readonly string _recordPath;
    private readonly string _argsFile;
    private readonly string _project;
    private readonly Dictionary<string, string> _hashes;
    private CSharpCompilation? _compilation;

    private ReferencedSource(string recordPath, string assemblyName, string argsFile, string project, Dictionary<string, string> hashes)
    {
        _recordPath = recordPath;
        AssemblyName = assemblyName;
        _argsFile = argsFile;
        _project = project;
        _hashes = hashes;
    }

    /// <summary>The referenced assembly's name.</summary>
    public string AssemblyName { get; }

    /// <summary>Reads a record.</summary>
    /// <param name="recordPath">The record.</param>
    /// <returns>The record, not yet checked against the files it names.</returns>
    /// <exception cref="InvalidDataException">The record is malformed.</exception>
    public static ReferencedSource Open(string recordPath)
    {
        ArgumentNullException.ThrowIfNull(recordPath);
        var lines = File.ReadAllLines(recordPath, Encoding.UTF8).Where(l => l.Length > 0).ToList();
        if (lines.Count == 0 || lines[0] != Header)
        {
            throw new InvalidDataException($"{recordPath}: not a Warrant source record");
        }
        string? assembly = null, argsFile = null, project = null;
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
                    throw new InvalidDataException($"{recordPath}: unexpected line '{line}'");
            }
        }
        if (string.IsNullOrEmpty(assembly) || string.IsNullOrEmpty(argsFile) || string.IsNullOrEmpty(project))
        {
            throw new InvalidDataException($"{recordPath}: the assembly, args or project line is missing");
        }
        return new ReferencedSource(recordPath, assembly, Path.GetFullPath(argsFile), Path.GetFullPath(project), hashes);
    }

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

        // Every file the compiler read: the arguments themselves, the sources, the generators' additional files, the
        // analyzer configuration, the referenced assemblies, and the analyzer and generator assemblies with every assembly
        // beside them, which the generator loader resolves their dependencies from (#51). Each must be in the record with
        // the hash it had when the assembly was compiled. A reference decides what the source means (a base class, a
        // constant) and a generator adds source, so either changing changes what is checked.
        var files = ReadFiles(CompilationFactory.ParseCscArgs(Checked(_argsFile), _project));
        foreach (var file in files)
        {
            Checked(file);
        }

        // The compilation reads the files again, so they are checked again once it is built and its generators have run:
        // an edit in between is caught, unless it was undone before the second check, as for any edit (the summary).
        var compilation = CompilationFactory.FromCscArgs(_argsFile, _project, pathBase, out var generatorProblems);
        foreach (var file in ReadFiles(CompilationFactory.ParseCscArgs(Checked(_argsFile), _project)).Concat(files).Distinct(PathComparer))
        {
            Checked(file);
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
    /// <exception cref="InvalidDataException">The arguments name a response file, which the record does not cover.</exception>
    private List<string> ReadFiles(CSharpCommandLineArguments args)
    {
        if (File.ReadAllLines(_argsFile, Encoding.UTF8).Any(l => l.StartsWith('@')))
        {
            throw new InvalidDataException($"{_argsFile}: a response file (@file) is not covered by {AssemblyName}'s source record");
        }
        var read = new List<string>();
        read.AddRange(args.SourceFiles.Select(f => f.Path));
        read.AddRange(args.AdditionalFiles.Select(f => f.Path));
        read.AddRange(args.AnalyzerConfigPaths);
        read.AddRange(args.MetadataReferences.Select(r => r.Reference));
        foreach (var analyzer in args.AnalyzerReferences.Select(r => Path.GetFullPath(Path.Combine(_project, r.FilePath))))
        {
            read.Add(analyzer);
            if (Path.GetDirectoryName(analyzer) is { } directory && Directory.Exists(directory))
            {
                read.AddRange(Directory.EnumerateFiles(directory, "*.dll"));
            }
        }
        return read.Select(f => Path.GetFullPath(Path.Combine(_project, f))).Distinct(PathComparer).Order(PathComparer).ToList();
    }

    private string Checked(string file)
    {
        var full = Path.GetFullPath(file);
        if (!_hashes.TryGetValue(full, out var recorded))
        {
            throw new InvalidDataException($"{_recordPath}: {full}, which {AssemblyName} is compiled from, is not in the record; build {AssemblyName} again");
        }
        if (!File.Exists(full) || !string.Equals(Sha256(full), recorded, StringComparison.OrdinalIgnoreCase))
        {
            throw new InvalidDataException($"{full} changed since {AssemblyName} was compiled; build {AssemblyName} again");
        }
        return full;
    }

    private static StringComparer PathComparer =>
        OperatingSystem.IsWindows() || OperatingSystem.IsMacOS() ? StringComparer.OrdinalIgnoreCase : StringComparer.Ordinal;

    private static string Sha256(string path)
    {
        using var stream = File.OpenRead(path);
        return Convert.ToHexString(SHA256.HashData(stream));
    }
}
