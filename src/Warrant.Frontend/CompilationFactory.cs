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

    private static PortableExecutableReference LoadWarrant()
    {
        using var stream = typeof(CompilationFactory).Assembly.GetManifestResourceStream(WarrantResource)
            ?? throw new InvalidOperationException($"The embedded resource '{WarrantResource}' is missing.");
        using var copy = new MemoryStream();
        stream.CopyTo(copy);
        return MetadataReference.CreateFromImage(ImmutableArray.Create(copy.ToArray()), filePath: WarrantResource);
    }
}
