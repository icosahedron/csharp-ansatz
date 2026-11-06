using System.Text.Json;
using Microsoft.CodeAnalysis.CSharp;
using Warrant.Extraction;
using Warrant.Kernel;
using Warrant.Meta;
using Warrant.Vir;

namespace Warrant.Engine.Tests;

/// <summary>
/// The checked semantics bundle, loaded once per test process through the engine's own loader, and the engine's runs
/// over the M4 corpus (tests/corpus/m4), each computed once.
/// </summary>
public sealed class EngineFixture
{
    private readonly Dictionary<string, (IReadOnlyList<EngineUnit> Inputs, EngineResult Result)> _runs = new(StringComparer.Ordinal);

    /// <summary>The checked, frozen bundle, loaded once per test process and shared with the differential fixture.</summary>
    internal static readonly Lazy<SemanticsBundle> SharedBundle = new(() => SemanticsBundle.Load(TestData.Path(SemanticsBundle.FileName)));

    public SemanticsBundle Bundle { get; } = SharedBundle.Value;

    /// <summary>The attribute sidecar, loaded once per test process against the bundle's SHA-256.</summary>
    internal static readonly Lazy<Sidecar> SharedSidecar =
        new(() => Sidecar.Load(TestData.Path(AttributeSidecarFixture.FileName), AttributeSidecarFixture.BundleSha256));

    /// <summary>The options of the corpus runs: the default budgets with the corpus kernel fuel, and the sidecar.</summary>
    public EngineOptions Options { get; } = EngineOptions.Default with { Kernel = KernelLimits.Corpus, Attributes = SharedSidecar.Value };

    /// <summary>
    /// The engine's run over a named corpus compilation, at <see cref="KernelLimits.Corpus"/>: an M4 compilation by its
    /// name, an M5a one as <c>m5a/name</c>.
    /// </summary>
    public EngineResult Run(string compilation) => Get(compilation).Result;

    /// <summary>A unit's span table in a named corpus compilation, as <see cref="Run"/> extracted it.</summary>
    public SpanTable? Spans(string compilation, string key) => Get(compilation).Inputs.Single(u => u.Unit.Key == key).Spans;

    private (IReadOnlyList<EngineUnit> Inputs, EngineResult Result) Get(string compilation)
    {
        lock (_runs)
        {
            if (!_runs.TryGetValue(compilation, out var run))
            {
                var set = compilation.StartsWith("m5a/", StringComparison.Ordinal) ? CorpusSet.M5a : CorpusSet.M4;
                var name = set == CorpusSet.M5a ? compilation["m5a/".Length..] : compilation;
                var inputs = EngineCorpus.Inputs(EngineCorpus.Extract(set.Compile(name)));
                run = (inputs, Pipeline.Run(inputs, Bundle, Options));
                _runs.Add(compilation, run);
            }
            return run;
        }
    }
}

/// <summary>Compiles and extracts the M4 corpus and inline sources (test-only: the engine never sees Roslyn).</summary>
internal static class EngineCorpus
{
    public static string Root => CorpusCompilations.Root;

    public static JsonElement Expected => CorpusCompilations.Expected;

    public static IEnumerable<string> Compilations => CorpusCompilations.Names;

    public static ExtractionResult Extract(string name) => Extract(Compile(name));

    /// <summary>Extracts a compilation, which must compile without errors.</summary>
    public static ExtractionResult Extract(CSharpCompilation compilation)
    {
        var result = Extractor.Extract(compilation);
        Assert.False(result.HasCompileErrors, string.Join("\n", result.Diagnostics.Select(d => d.Message)));
        return result;
    }

    /// <summary>The compilation extraction reads for a named corpus compilation (expected.json).</summary>
    public static CSharpCompilation Compile(string name) => CorpusCompilations.Compile(name);

    /// <summary>Compiles and extracts one in-memory source file, which must extract without diagnostics.</summary>
    public static ExtractionResult Inline(string source) => CorpusCompilations.Inline(source);

    public static IReadOnlyList<EngineUnit> Inputs(ExtractionResult result) =>
        [.. result.Units.Select(u => new EngineUnit(u.Unit, u.DisplayName, u.Spans))];
}
