using System.Collections.Immutable;
using System.Text;
using Basic.Reference.Assemblies;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.Text;

namespace Warrant.Frontend;

/// <summary>A source file for a compilation: its path, relative and with forward slashes, and its text.</summary>
/// <param name="Path">The relative path, e.g. <c>accepted/Payments.cs</c>.</param>
/// <param name="Text">The source text.</param>
public sealed record SourceFile(string Path, string Text);

/// <summary>
/// Builds the <see cref="CSharpCompilation"/> that extraction reads (docs/m4/03, "Building the compilation").
/// The options decide what the C# means, so they are trusted input (KTD22): .NET 10 reference assemblies plus the
/// <c>Warrant</c> package from its embedded image, C# 14, nullable analysis on, deterministic, source paths
/// relative and sorted, and overflow checking as an explicit parameter.
/// </summary>
public static class CompilationFactory
{
    private const string WarrantResource = "Warrant.dll";

    private static readonly Lazy<PortableExecutableReference> WarrantImage = new(LoadWarrant);

    private static readonly Lazy<ImmutableArray<MetadataReference>> AllReferences = new(() =>
        ImmutableArray.CreateRange<MetadataReference>(Net100.References.All).Add(WarrantImage.Value));

    /// <summary>The language version pinned for the corpus.</summary>
    public static LanguageVersion LanguageVersion => LanguageVersion.CSharp14;

    /// <summary>The parse options: C# 14, no preprocessor symbols.</summary>
    public static CSharpParseOptions ParseOptions { get; } =
        new CSharpParseOptions(LanguageVersion.CSharp14, DocumentationMode.Parse, SourceCodeKind.Regular);

    /// <summary>The <c>Warrant</c> package, loaded from the image embedded in this assembly.</summary>
    public static MetadataReference WarrantReference => WarrantImage.Value;

    /// <summary>Every reference a compilation gets: <c>Basic.Reference.Assemblies.Net100</c> and the <c>Warrant</c> package.</summary>
    public static ImmutableArray<MetadataReference> References => AllReferences.Value;

    /// <summary>The compilation options for a library compiled with or without overflow checking.</summary>
    /// <param name="checkOverflow">Whether arithmetic is checked by default (<c>CheckForOverflowUnderflow</c>).</param>
    /// <returns>The options.</returns>
    public static CSharpCompilationOptions Options(bool checkOverflow) =>
        new CSharpCompilationOptions(
                OutputKind.DynamicallyLinkedLibrary,
                checkOverflow: checkOverflow,
                nullableContextOptions: NullableContextOptions.Enable,
                deterministic: true,
                concurrentBuild: false);

    /// <summary>Compiles sources in memory, ordered by path (ordinal), so the compilation does not depend on input order.</summary>
    /// <param name="sources">The sources.</param>
    /// <param name="checkOverflow">Whether arithmetic is checked by default.</param>
    /// <param name="assemblyName">The assembly name.</param>
    /// <returns>The compilation.</returns>
    public static CSharpCompilation Create(IEnumerable<SourceFile> sources, bool checkOverflow, string assemblyName = "Corpus")
    {
        ArgumentNullException.ThrowIfNull(sources);
        var trees = sources
            .Select(s => s with { Path = s.Path.Replace('\\', '/') })
            .OrderBy(s => s.Path, StringComparer.Ordinal)
            .Select(s => CSharpSyntaxTree.ParseText(SourceText.From(s.Text, Encoding.UTF8), ParseOptions, s.Path));
        return CSharpCompilation.Create(assemblyName, trees, References, Options(checkOverflow));
    }

    /// <summary>Reads files under a root directory and compiles them; each tree's path is its path relative to the root.</summary>
    /// <param name="root">The directory the paths are relative to.</param>
    /// <param name="paths">The files, absolute or relative to <paramref name="root"/>.</param>
    /// <param name="checkOverflow">Whether arithmetic is checked by default.</param>
    /// <param name="assemblyName">The assembly name.</param>
    /// <returns>The compilation.</returns>
    public static CSharpCompilation FromFiles(string root, IEnumerable<string> paths, bool checkOverflow, string assemblyName = "Corpus")
    {
        ArgumentNullException.ThrowIfNull(paths);
        var fullRoot = Path.GetFullPath(root);
        var sources = paths.Select(p =>
        {
            var full = Path.GetFullPath(Path.Combine(fullRoot, p));
            return new SourceFile(Path.GetRelativePath(fullRoot, full), File.ReadAllText(full, Encoding.UTF8));
        });
        return Create(sources, checkOverflow, assemblyName);
    }

    /// <summary>
    /// Builds the compilation the compiler builds, from <c>@(CscCommandLineArgs)</c> written one argument per line
    /// (KTD21; docs/m5a/07, "Reproducing the compilation"). Roslyn's own parser reads the arguments, so the parse options
    /// (defines, language version, features), compilation options (checked, nullable, unsafe, warnings), sources,
    /// references and analyzer configuration are exactly the compiler's. The source generators among the compiler's
    /// analyzers run as they run in Csc, so the compilation holds the generated sources too; analyzers are not run.
    /// Each tree's path is its path relative to <paramref name="projectDirectory"/>, with forward slashes; sources keep
    /// the compiler's order, followed by the generated sources.
    /// </summary>
    /// <param name="argsFile">The argument file, e.g. <c>obj/warrant.csc.args</c>.</param>
    /// <param name="projectDirectory">The directory relative paths in the arguments are relative to (<c>$(MSBuildProjectDirectory)</c>).</param>
    /// <returns>The compilation, which may have errors: see <see cref="Failure"/>.</returns>
    /// <exception cref="InvalidDataException">The arguments are not valid compiler arguments.</exception>
    public static CSharpCompilation FromCscArgs(string argsFile, string projectDirectory) =>
        FromCscArgs(argsFile, projectDirectory, out _);

    /// <summary>As <see cref="FromCscArgs(string, string)"/>, and says why a source generator could not run.</summary>
    /// <param name="argsFile">The argument file.</param>
    /// <param name="projectDirectory">The directory relative paths in the arguments are relative to.</param>
    /// <param name="generatorProblems">Why a generator failed to load or threw; empty when every generator ran.</param>
    /// <returns>The compilation, which may have errors: see <see cref="Failure"/>.</returns>
    /// <exception cref="InvalidDataException">The arguments are not valid compiler arguments.</exception>
    public static CSharpCompilation FromCscArgs(string argsFile, string projectDirectory, out IReadOnlyList<string> generatorProblems) =>
        FromCscArgs(argsFile, projectDirectory, projectDirectory, File.ReadAllBytes, out generatorProblems);

    /// <summary>
    /// As <see cref="FromCscArgs(string, string, out IReadOnlyList{string})"/>, with each tree's path relative to
    /// <paramref name="pathBase"/> instead of the project's directory. A referenced project's sources are named relative to
    /// the project being verified, so diagnostics about them point at the right files (#32). Every file the compilation and
    /// its generators read, the argument file included, is read through <paramref name="read"/>, given its full path; a
    /// referenced project uses it to compile from the bytes it checked against its record (#127).
    /// </summary>
    internal static CSharpCompilation FromCscArgs(
        string argsFile, string projectDirectory, string pathBase, Func<string, byte[]> read, out IReadOnlyList<string> generatorProblems)
    {
        var fullProject = Path.GetFullPath(projectDirectory);
        var fullBase = Path.GetFullPath(pathBase);
        var args = ParseCscArgs(argsFile, Lines(read(Path.GetFullPath(argsFile))), fullProject);

        // The trees first get the paths Csc gives them, their full paths, because that is what the source generators see
        // (#54): a generator may key its output on a tree's path. Once the generators have run, every tree is named
        // relative to the path base, as Warrant names them everywhere else.
        var trees = args.SourceFiles.Select(file =>
        {
            var path = Path.GetFullPath(file.Path);
            using var stream = new MemoryStream(read(path), writable: false);
            var text = SourceText.From(stream, args.Encoding, args.ChecksumAlgorithm);
            return CSharpSyntaxTree.ParseText(text, args.ParseOptions, path);
        }).ToList();
        var references = args.MetadataReferences.Select(r =>
        {
            var path = Path.GetFullPath(Path.Combine(fullProject, r.Reference));
            return (MetadataReference)MetadataReference.CreateFromImage(ImmutableArray.Create(read(path)), r.Properties, filePath: path);
        });

        var options = args.CompilationOptions;
        AnalyzerConfigSet? set = null;
        if (args.AnalyzerConfigPaths.Length > 0)
        {
            var configs = args.AnalyzerConfigPaths
                .Select(p => Path.GetFullPath(Path.Combine(fullProject, p)))
                .Select(p => AnalyzerConfig.Parse(SourceText.From(Text(read(p))), p))
                .ToList();
            set = AnalyzerConfigSet.Create(configs);
            // Each tree's options under both its names: the full path while the generators run, the relative one after.
            var treeOptions = new Dictionary<string, AnalyzerConfigOptionsResult>(StringComparer.Ordinal);
            foreach (var tree in trees)
            {
                var result = set.GetOptionsForSourcePath(tree.FilePath);
                treeOptions[tree.FilePath] = result;
                treeOptions[Relative(fullBase, tree.FilePath)] = result;
            }
            options = options.WithSyntaxTreeOptionsProvider(new AnalyzerConfigTreeOptions(set.GlobalConfigOptions, treeOptions));
        }
        var compilation = CSharpCompilation.Create(args.CompilationName, trees, references, options);

        var analyzers = args.AnalyzerReferences.Select(r => Path.GetFullPath(Path.Combine(fullProject, r.FilePath))).ToList();
        var additionalFiles = args.AdditionalFiles.Select(f => Path.GetFullPath(Path.Combine(fullProject, f.Path))).ToList();
        // Csc puts the generated trees under the generated-files directory, or else beside the output assembly.
        var generatedBase = args.GeneratedFilesOutputDirectory ?? args.OutputDirectory;
        (compilation, generatorProblems) = SourceGenerators.Run(compilation, analyzers, additionalFiles, set, args.ParseOptions, fullBase, read, generatedBase);

        var renamed = compilation.SyntaxTrees.Select(t => t.WithFilePath(Relative(fullBase, t.FilePath))).ToList();
        return compilation.RemoveAllSyntaxTrees().AddSyntaxTrees(renamed);
    }

    /// <summary>A path as Warrant names a tree: relative to <paramref name="fullBase"/>, with forward slashes.</summary>
    private static string Relative(string fullBase, string path) =>
        (Path.IsPathRooted(path) ? Path.GetRelativePath(fullBase, path) : path).Replace('\\', '/');

    /// <summary>A file's text as <see cref="File.ReadAllText(string, Encoding)"/> reads it with UTF-8: a byte order mark decides.</summary>
    internal static string Text(byte[] bytes)
    {
        using var reader = new StreamReader(new MemoryStream(bytes, writable: false), Encoding.UTF8, detectEncodingFromByteOrderMarks: true);
        return reader.ReadToEnd();
    }

    /// <summary>A file's lines as <see cref="File.ReadAllLines(string, Encoding)"/> reads them with UTF-8.</summary>
    internal static string[] Lines(byte[] bytes)
    {
        using var reader = new StreamReader(new MemoryStream(bytes, writable: false), Encoding.UTF8, detectEncodingFromByteOrderMarks: true);
        var lines = new List<string>();
        while (reader.ReadLine() is { } line)
        {
            lines.Add(line);
        }
        return [.. lines];
    }

    /// <summary>Parses an argument file's lines, one argument per line.</summary>
    /// <param name="argsFile">The argument file, named in errors.</param>
    /// <param name="lines">Its lines.</param>
    /// <param name="fullProject">The directory relative paths are relative to.</param>
    /// <exception cref="InvalidDataException">The arguments are not valid compiler arguments.</exception>
    internal static CSharpCommandLineArguments ParseCscArgs(string argsFile, string[] lines, string fullProject)
    {
        var args = CSharpCommandLineParser.Default.Parse(lines.Where(l => l.Length > 0), fullProject, sdkDirectory: null);
        var errors = args.Errors.Where(d => d.Severity == DiagnosticSeverity.Error).ToList();
        if (errors.Count > 0)
        {
            throw new InvalidDataException(
                $"{argsFile}: " + string.Join("; ", errors.Select(d => d.GetMessage(System.Globalization.CultureInfo.InvariantCulture))));
        }
        return args;
    }

    /// <summary>
    /// The calls in <c>[Verified]</c> and <c>[Theorem]</c> members that a generated interceptor replaces. Warrant
    /// translates the method a call names, and the compiler emits the interceptor instead, so these calls are rejected.
    /// </summary>
    /// <param name="compilation">The compilation, generated sources included.</param>
    /// <param name="cancellationToken">Cancels the search.</param>
    /// <returns>Each intercepted call's location and its interceptor.</returns>
    public static IReadOnlyList<(Location Location, IMethodSymbol Interceptor)> InterceptedCalls(
        CSharpCompilation compilation, CancellationToken cancellationToken = default)
    {
        ArgumentNullException.ThrowIfNull(compilation);
        return SourceGenerators.InterceptedCalls(compilation, cancellationToken);
    }

    /// <summary>
    /// Why a compilation does not compile, or null if it has no errors (WRT0012). A compilation from
    /// <see cref="FromCscArgs(string, string, out IReadOnlyList{string})"/> fails this way when a source generator could not
    /// run, and the failure names what is missing and why the generator did not run.
    /// </summary>
    /// <param name="compilation">The compilation.</param>
    /// <param name="generatorProblems">Why a source generator could not run, from <see cref="FromCscArgs(string, string, out IReadOnlyList{string})"/>.</param>
    /// <param name="cancellationToken">Cancels the check.</param>
    /// <returns>The failure, or null.</returns>
    public static CompilationFailure? Failure(
        CSharpCompilation compilation, IReadOnlyList<string>? generatorProblems = null, CancellationToken cancellationToken = default)
    {
        ArgumentNullException.ThrowIfNull(compilation);
        // A warning made an error (/warnaserror) is not counted: Csc may have suppressed it with a DiagnosticSuppressor,
        // which Warrant does not run (#32, a nullable suppressor), and no warning changes what the code means.
        var errors = compilation.GetDiagnostics(cancellationToken).Where(d => d.Severity == DiagnosticSeverity.Error && !d.IsWarningAsError).ToList();
        var problems = generatorProblems ?? [];
        // A generator that did not run fails the compilation even when the code compiles without its output: Csc may
        // have run it (a newer compiler, a different loader), and output such as an interceptor or a closer overload
        // changes what the code means without any error here.
        return errors.Count == 0 && problems.Count == 0 ? null : new CompilationFailure(errors, problems);
    }

    private static PortableExecutableReference LoadWarrant()
    {
        using var stream = typeof(CompilationFactory).Assembly.GetManifestResourceStream(WarrantResource)
            ?? throw new InvalidOperationException($"The embedded resource '{WarrantResource}' is missing.");
        using var copy = new MemoryStream();
        stream.CopyTo(copy);
        return MetadataReference.CreateFromImage(ImmutableArray.Create(copy.ToArray()), filePath: WarrantResource);
    }
}
