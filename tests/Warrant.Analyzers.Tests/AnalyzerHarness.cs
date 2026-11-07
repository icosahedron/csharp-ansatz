extern alias analyzers;

using System.Collections.Concurrent;
using System.Collections.Immutable;
using System.Globalization;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.Diagnostics;
using WarrantAnalyzer = analyzers::Warrant.Analyzers.WarrantAnalyzer;

namespace Warrant.Analyzers.Tests;

/// <summary>Runs <see cref="WarrantAnalyzer"/> over a compilation the way the IDE does: concurrently, every analyzer exception recorded.</summary>
internal static class AnalyzerHarness
{
    /// <summary>The Roslyn major version this test project is built for.</summary>
#if ROSLYN48
    public const int RoslynMajor = 4;
#else
    public const int RoslynMajor = 5;
#endif

    /// <summary>A compilation of the files (name, text) against the running framework and Warrant.dll, in C# 12, which Roslyn 4.8 also reads.</summary>
    public static CSharpCompilation Compile(params (string Path, string Text)[] files)
    {
        var parse = new CSharpParseOptions(LanguageVersion.CSharp12);
        var trees = files.Select(f => CSharpSyntaxTree.ParseText(f.Text, parse, f.Path)).ToList();
        var platform = ((string)AppContext.GetData("TRUSTED_PLATFORM_ASSEMBLIES")!).Split(Path.PathSeparator)
            .Where(p => Path.GetFileName(p) is var n && (n.StartsWith("System.", StringComparison.Ordinal) || n is "netstandard.dll" or "mscorlib.dll"));
        var references = platform.Append(typeof(VerifiedAttribute).Assembly.Location).Select(p => MetadataReference.CreateFromFile(p));
        return CSharpCompilation.Create("Sample", trees, references, new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary));
    }

    /// <summary>The analyzer's diagnostics, sorted by file, position, ID and message, one line each, and every exception the analyzer threw.</summary>
    public static async Task<(List<string> Lines, List<Exception> Exceptions)> Run(Compilation compilation)
    {
        var exceptions = new ConcurrentQueue<Exception>();
        var options = new CompilationWithAnalyzersOptions(
            new AnalyzerOptions(ImmutableArray<AdditionalText>.Empty),
            onAnalyzerException: (ex, _, _) => exceptions.Enqueue(ex),
            concurrentAnalysis: true,
            logAnalyzerExecutionTime: false);
        var analysis = compilation.WithAnalyzers(ImmutableArray.Create<DiagnosticAnalyzer>(new WarrantAnalyzer()), options);
        var diagnostics = await analysis.GetAnalyzerDiagnosticsAsync().ConfigureAwait(false);
        return ([.. Lines(diagnostics)], [.. exceptions]);
    }

    /// <summary>Diagnostics as <c>path(line,col,line,col): severity ID: message</c>, sorted.</summary>
    public static IEnumerable<string> Lines(IEnumerable<Diagnostic> diagnostics) =>
        diagnostics
            .Select(d => (Span: d.Location.GetLineSpan(), d))
            .OrderBy(p => p.Span.Path, StringComparer.Ordinal)
            .ThenBy(p => p.d.Location.SourceSpan.Start)
            .ThenBy(p => p.d.Id, StringComparer.Ordinal)
            .ThenBy(p => p.d.GetMessage(CultureInfo.InvariantCulture), StringComparer.Ordinal)
            .Select(p => Line(p.Span.Path, p.Span.StartLinePosition.Line + 1, p.Span.StartLinePosition.Character + 1,
                p.Span.EndLinePosition.Line + 1, p.Span.EndLinePosition.Character + 1,
                p.d.Severity == DiagnosticSeverity.Warning ? "warning" : "error", p.d.Id, p.d.GetMessage(CultureInfo.InvariantCulture)));

    public static string Line(string path, int startLine, int startColumn, int endLine, int endColumn, string severity, string id, string message) =>
        string.Create(CultureInfo.InvariantCulture, $"{path}({startLine},{startColumn},{endLine},{endColumn}): {severity} {id}: {message}");
}
