using System.Collections.Immutable;
using System.Reflection;
using System.Reflection.Metadata;
using System.Reflection.PortableExecutable;
using System.Runtime.Loader;
using System.Text;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Diagnostics;
using Microsoft.CodeAnalysis.Text;

namespace Warrant.Frontend;

/// <summary>
/// Runs a project's source generators as Csc does (docs/m5a/07, "Source generators"), so the compilation Warrant reads
/// holds the generated sources the compiled assembly holds. The generators come from the compiler's <c>/analyzer:</c>
/// arguments and see its <c>/additionalfile:</c> arguments and analyzer configuration. Analyzers are not run: they
/// report diagnostics but do not change the program.
/// </summary>
internal static class SourceGenerators
{
    /// <summary>Runs every C# generator in <paramref name="analyzers"/> over <paramref name="compilation"/>.</summary>
    /// <param name="compilation">The compilation of the project's own sources.</param>
    /// <param name="analyzers">The analyzer assemblies, as full paths.</param>
    /// <param name="additionalFiles">The additional files, as full paths.</param>
    /// <param name="configs">The analyzer configuration, or null when there is none.</param>
    /// <param name="parseOptions">The compiler's parse options, which the generated trees are parsed with.</param>
    /// <param name="projectDirectory">The project directory, which tree paths are relative to.</param>
    /// <returns>The compilation with the generated trees, and the problems that kept a generator from running.</returns>
    public static (CSharpCompilation Compilation, IReadOnlyList<string> Problems) Run(
        CSharpCompilation compilation,
        IReadOnlyList<string> analyzers,
        IReadOnlyList<string> additionalFiles,
        AnalyzerConfigSet? configs,
        CSharpParseOptions parseOptions,
        string projectDirectory)
    {
        if (analyzers.Count == 0)
        {
            return (compilation, []);
        }

        var problems = new List<string>();
        var loader = new Loader(analyzers);
        var generators = new List<ISourceGenerator>();
        foreach (var path in analyzers)
        {
            var reference = new AnalyzerFileReference(path, loader);
            var failures = new List<string>();
            reference.AnalyzerLoadFailed += (_, e) => failures.Add(
                $"{Path.GetFileName(path)}: {e.ErrorCode}"
                + (string.IsNullOrEmpty(e.Message) ? "" : ", " + e.Message)
                + (e.Exception is { } ex ? ", " + ex.GetType().Name + ": " + ex.Message : "")
                + (e.ReferencedCompilerVersion is { } version ? ", built for compiler " + version : ""));
            generators.AddRange(reference.GetGenerators(LanguageNames.CSharp));
            // An analyzer that fails to load changes nothing Warrant translates; a generator, or a file that cannot be
            // read well enough to tell, may have written code the compiler compiled.
            if (failures.Count > 0 && MayDeclareGenerator(path))
            {
                problems.AddRange(failures);
            }
        }
        if (generators.Count == 0)
        {
            return (compilation, problems);
        }

        var texts = additionalFiles.Select(p => (AdditionalText)new FileText(p)).ToImmutableArray();
        var options = new ConfigOptionsProvider(configs, projectDirectory);
        GeneratorDriver driver = CSharpGeneratorDriver.Create(generators, texts, parseOptions, options);
        driver = driver.RunGeneratorsAndUpdateCompilation(compilation, out var updated, out var diagnostics);

        // A generator that throws is reported as a warning (CS8784, CS8785) and its output dropped, so the compilation
        // can then miss what it would have written. Its message says why.
        problems.AddRange(diagnostics
            .Where(d => d.Severity == DiagnosticSeverity.Error || d.Id is "CS8784" or "CS8785")
            .Select(d => d.GetMessage(System.Globalization.CultureInfo.InvariantCulture)));
        return ((CSharpCompilation)updated, problems);
    }

    /// <summary>
    /// The calls in <c>[Verified]</c> and <c>[Theorem]</c> members that a generated interceptor replaces
    /// (<c>[InterceptsLocation]</c>). The compiler emits the interceptor instead of the method the semantic model names,
    /// which is the method Warrant translates, so such a call does not mean what Warrant would prove about it.
    /// </summary>
    /// <param name="compilation">The compilation, generated trees included.</param>
    /// <param name="cancellationToken">Cancels the search.</param>
    /// <returns>Each intercepted call's location and the interceptor that replaces it.</returns>
    public static IReadOnlyList<(Location Location, IMethodSymbol Interceptor)> InterceptedCalls(
        CSharpCompilation compilation, CancellationToken cancellationToken = default)
    {
        var found = new List<(Location, IMethodSymbol)>();
        foreach (var tree in compilation.SyntaxTrees)
        {
            var model = compilation.GetSemanticModel(tree);
            foreach (var call in tree.GetRoot(cancellationToken).DescendantNodes().OfType<InvocationExpressionSyntax>())
            {
#pragma warning disable RSEXPERIMENTAL002 // GetInterceptorMethod is experimental in Roslyn 5.
                var interceptor = model.GetInterceptorMethod(call, cancellationToken);
#pragma warning restore RSEXPERIMENTAL002
                if (interceptor is not null && InVerifiedCode(model, call, cancellationToken))
                {
                    found.Add((call.GetLocation(), interceptor));
                }
            }
        }
        return found;
    }

    /// <summary>
    /// Whether an analyzer assembly declares a type marked <c>[Microsoft.CodeAnalysis.Generator]</c>, read from its
    /// metadata without loading it. A file whose metadata cannot be read counts as declaring one, so it fails closed.
    /// </summary>
    internal static bool MayDeclareGenerator(string path)
    {
        try
        {
            using var stream = File.OpenRead(path);
            using var pe = new PEReader(stream);
            if (!pe.HasMetadata)
            {
                return true;
            }
            var reader = pe.GetMetadataReader();
            foreach (var handle in reader.CustomAttributes)
            {
                var attribute = reader.GetCustomAttribute(handle);
                if (attribute.Constructor.Kind == HandleKind.MemberReference
                    && reader.GetMemberReference((MemberReferenceHandle)attribute.Constructor).Parent is { Kind: HandleKind.TypeReference } parent)
                {
                    var type = reader.GetTypeReference((TypeReferenceHandle)parent);
                    if (reader.StringComparer.Equals(type.Name, "GeneratorAttribute")
                        && reader.StringComparer.Equals(type.Namespace, "Microsoft.CodeAnalysis"))
                    {
                        return true;
                    }
                }
            }
            return false;
        }
        catch (Exception e) when (e is IOException or UnauthorizedAccessException or BadImageFormatException or InvalidOperationException)
        {
            return true;
        }
    }

    private static bool InVerifiedCode(SemanticModel model, SyntaxNode node, CancellationToken cancellationToken)
    {
        // The nearest member declaration: a method, a property (whose accessors are not member declarations), a field.
        foreach (var ancestor in node.Ancestors())
        {
            if (ancestor is MemberDeclarationSyntax and not BaseTypeDeclarationSyntax and not BaseNamespaceDeclarationSyntax
                && model.GetDeclaredSymbol(ancestor, cancellationToken) is { } member)
            {
                return member.GetAttributes().Any(a => a.AttributeClass?.ToDisplayString() is "Warrant.VerifiedAttribute" or "Warrant.TheoremAttribute");
            }
        }
        return false;
    }

    /// <summary>
    /// Loads analyzer assemblies into one context of their own. Microsoft.CodeAnalysis comes from the default context,
    /// so generators share Warrant's Roslyn; any other dependency is found beside the analyzers, as Csc finds it.
    /// </summary>
    private sealed class Loader : IAnalyzerAssemblyLoader
    {
        private readonly AssemblyLoadContext _context = new("warrant-analyzers");
        private readonly Dictionary<string, string> _byName = new(StringComparer.OrdinalIgnoreCase);

        public Loader(IEnumerable<string> paths)
        {
            foreach (var path in paths)
            {
                AddDependencyLocation(path);
            }
            _context.Resolving += (context, name) =>
                name.Name is { } simple && _byName.TryGetValue(simple, out var path) ? Load(context, path) : null;
        }

        public void AddDependencyLocation(string fullPath)
        {
            _byName.TryAdd(Path.GetFileNameWithoutExtension(fullPath), fullPath);
            var directory = Path.GetDirectoryName(fullPath);
            if (directory is not null && Directory.Exists(directory))
            {
                foreach (var dll in Directory.EnumerateFiles(directory, "*.dll"))
                {
                    _byName.TryAdd(Path.GetFileNameWithoutExtension(dll), dll);
                }
            }
        }

        public Assembly LoadFromPath(string fullPath) => Load(_context, fullPath);

        // From the bytes, not the path, so the file is not locked while Warrant runs.
        private static Assembly Load(AssemblyLoadContext context, string path)
        {
            using var stream = new MemoryStream(File.ReadAllBytes(path));
            return context.LoadFromStream(stream);
        }
    }

    private sealed class FileText(string path) : AdditionalText
    {
        public override string Path { get; } = path;

        public override SourceText GetText(CancellationToken cancellationToken = default) =>
            SourceText.From(File.ReadAllText(Path, Encoding.UTF8), Encoding.UTF8);
    }

    /// <summary>The analyzer configuration as generators see it: the global options, and each file's own.</summary>
    private sealed class ConfigOptionsProvider(AnalyzerConfigSet? configs, string projectDirectory) : AnalyzerConfigOptionsProvider
    {
        public override AnalyzerConfigOptions GlobalOptions { get; } =
            new Options(configs?.GlobalConfigOptions.AnalyzerOptions ?? ImmutableDictionary<string, string>.Empty);

        public override AnalyzerConfigOptions GetOptions(SyntaxTree tree) => For(tree.FilePath);

        public override AnalyzerConfigOptions GetOptions(AdditionalText textFile) => For(textFile.Path);

        private Options For(string path) =>
            configs is null
                ? new Options(ImmutableDictionary<string, string>.Empty)
                : new Options(configs.GetOptionsForSourcePath(System.IO.Path.GetFullPath(System.IO.Path.Combine(projectDirectory, path))).AnalyzerOptions);
    }

    private sealed class Options(ImmutableDictionary<string, string> values) : AnalyzerConfigOptions
    {
        public override bool TryGetValue(string key, [System.Diagnostics.CodeAnalysis.NotNullWhen(true)] out string? value) =>
            values.TryGetValue(key, out value);
    }
}
