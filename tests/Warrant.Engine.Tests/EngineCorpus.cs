using System.Text.Json;
using Microsoft.CodeAnalysis.CSharp;
using Warrant.Extraction;
using Warrant.Frontend;
using Warrant.Kernel;

namespace Warrant.Engine.Tests;

/// <summary>
/// The checked semantics bundle, loaded once through the engine's own loader, and the engine's runs over the M4 corpus
/// (tests/corpus/m4), each computed once.
/// </summary>
public sealed class EngineFixture
{
    private readonly Dictionary<string, EngineResult> _runs = new(StringComparer.Ordinal);

    public EngineFixture() => Bundle = SemanticsBundle.Load(TestData.Path(SemanticsBundle.FileName));

    public SemanticsBundle Bundle { get; }

    /// <summary>The engine's run over a named corpus compilation, at <see cref="KernelLimits.Corpus"/>.</summary>
    public EngineResult Run(string compilation)
    {
        lock (_runs)
        {
            if (!_runs.TryGetValue(compilation, out var result))
            {
                result = Pipeline.Run(EngineCorpus.Inputs(EngineCorpus.Extract(compilation)), Bundle, KernelLimits.Corpus);
                _runs.Add(compilation, result);
            }
            return result;
        }
    }
}

/// <summary>Compiles and extracts the M4 corpus and inline sources (test-only: the engine never sees Roslyn).</summary>
internal static class EngineCorpus
{
    public static string Root { get; } = Path.Combine(AppContext.BaseDirectory, "corpus", "m4");

    public static JsonElement Expected { get; } = JsonDocument.Parse(File.ReadAllText(Path.Combine(Root, "expected.json"))).RootElement;

    public static IEnumerable<string> Compilations =>
        Expected.GetProperty("compilations").EnumerateArray().Select(c => c.GetProperty("name").GetString()!);

    public static ExtractionResult Extract(string name) => Extract(Compile(name));

    /// <summary>Extracts a compilation, which must compile without errors.</summary>
    public static ExtractionResult Extract(CSharpCompilation compilation)
    {
        var result = Extractor.Extract(compilation);
        Assert.False(result.HasCompileErrors, string.Join("\n", result.Diagnostics.Select(d => d.Message)));
        return result;
    }

    /// <summary>The compilation extraction reads for a named corpus compilation (expected.json).</summary>
    public static CSharpCompilation Compile(string name)
    {
        var spec = Expected.GetProperty("compilations").EnumerateArray().Single(c => c.GetProperty("name").GetString() == name);
        var excluded = spec.TryGetProperty("exclude", out var ex) ? ex.EnumerateArray().Select(e => e.GetString()!).ToHashSet() : [];
        var files = new List<string>();
        foreach (var glob in spec.GetProperty("files").EnumerateArray().Select(f => f.GetString()!))
        {
            var dir = Path.GetDirectoryName(glob)!;
            files.AddRange(Directory.GetFiles(Path.Combine(Root, dir), Path.GetFileName(glob))
                .Select(f => dir + "/" + Path.GetFileName(f))
                .Where(f => !excluded.Contains(f)));
        }
        files.Sort(StringComparer.Ordinal);
        return CompilationFactory.FromFiles(Root, files, spec.GetProperty("checkOverflow").GetBoolean());
    }

    /// <summary>Compiles and extracts one in-memory source file, which must extract without diagnostics.</summary>
    public static ExtractionResult Inline(string source)
    {
        var result = Extractor.Extract(CompilationFactory.Create([new SourceFile("Test.cs", "using Warrant;\n" + source)], checkOverflow: false));
        Assert.True(
            result.Diagnostics.Count == 0,
            string.Join("\n", result.Diagnostics.Select(d => $"{d.Id} {d.MemberKey} {d.Construct} {d.Message}")));
        return result;
    }

    public static IReadOnlyList<EngineUnit> Inputs(ExtractionResult result) =>
        [.. result.Units.Select(u => new EngineUnit(u.Unit, u.DisplayName, u.Spans))];
}
