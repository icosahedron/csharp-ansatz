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
    /// references and analyzer configuration are exactly the compiler's. Analyzers and source generators are not run.
    /// Each tree's path is its path relative to <paramref name="projectDirectory"/>, with forward slashes; sources keep
    /// the compiler's order.
    /// </summary>
    /// <param name="argsFile">The argument file, e.g. <c>obj/warrant.csc.args</c>.</param>
    /// <param name="projectDirectory">The directory relative paths in the arguments are relative to (<c>$(MSBuildProjectDirectory)</c>).</param>
    /// <returns>The compilation, which may have errors: see <see cref="Failure"/>.</returns>
    /// <exception cref="InvalidDataException">The arguments are not valid compiler arguments.</exception>
    public static CSharpCompilation FromCscArgs(string argsFile, string projectDirectory)
    {
        var fullProject = Path.GetFullPath(projectDirectory);
        var lines = File.ReadAllLines(argsFile, Encoding.UTF8).Where(l => l.Length > 0).ToArray();
        var args = CSharpCommandLineParser.Default.Parse(lines, fullProject, sdkDirectory: null);
        var errors = args.Errors.Where(d => d.Severity == DiagnosticSeverity.Error).ToList();
        if (errors.Count > 0)
        {
            throw new InvalidDataException(
                $"{argsFile}: " + string.Join("; ", errors.Select(d => d.GetMessage(System.Globalization.CultureInfo.InvariantCulture))));
        }

        var trees = args.SourceFiles.Select(file =>
        {
            using var stream = File.OpenRead(file.Path);
            var text = SourceText.From(stream, args.Encoding, args.ChecksumAlgorithm);
            var path = Path.GetRelativePath(fullProject, file.Path).Replace('\\', '/');
            return CSharpSyntaxTree.ParseText(text, args.ParseOptions, path);
        }).ToList();
        var references = args.MetadataReferences.Select(r =>
            (MetadataReference)MetadataReference.CreateFromFile(Path.GetFullPath(Path.Combine(fullProject, r.Reference)), r.Properties));

        var options = args.CompilationOptions;
        if (args.AnalyzerConfigPaths.Length > 0)
        {
            var configs = args.AnalyzerConfigPaths
                .Select(p => Path.GetFullPath(Path.Combine(fullProject, p)))
                .Select(p => AnalyzerConfig.Parse(SourceText.From(File.ReadAllText(p, Encoding.UTF8)), p))
                .ToList();
            var set = AnalyzerConfigSet.Create(configs);
            var treeOptions = trees.ToDictionary(
                t => t.FilePath,
                t => set.GetOptionsForSourcePath(Path.GetFullPath(Path.Combine(fullProject, t.FilePath))),
                StringComparer.Ordinal);
            options = options.WithSyntaxTreeOptionsProvider(new AnalyzerConfigTreeOptions(set.GlobalConfigOptions, treeOptions));
        }
        return CSharpCompilation.Create(args.CompilationName, trees, references, options);
    }

    /// <summary>
    /// Why a compilation does not compile, or null if it has no errors. Source generators run only inside Csc, so a
    /// compilation from <see cref="FromCscArgs"/> that needs generated code fails here, naming what it is missing (WRT0012).
    /// </summary>
    /// <param name="compilation">The compilation.</param>
    /// <param name="cancellationToken">Cancels the check.</param>
    /// <returns>The failure, or null.</returns>
    public static CompilationFailure? Failure(CSharpCompilation compilation, CancellationToken cancellationToken = default)
    {
        ArgumentNullException.ThrowIfNull(compilation);
        var errors = compilation.GetDiagnostics(cancellationToken).Where(d => d.Severity == DiagnosticSeverity.Error).ToList();
        return errors.Count == 0 ? null : new CompilationFailure(errors);
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
