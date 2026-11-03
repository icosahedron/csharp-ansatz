using System.Text.Json;
using Warrant.Extraction;
using Warrant.Frontend;
using Warrant.Kernel;
using Warrant.Vir;

namespace Warrant.Semantics.Tests;

/// <summary>Compiles and extracts the M4 corpus (tests/corpus/m4) and inline sources, and translates them.</summary>
internal static class TranslationCorpus
{
    public static string Root { get; } = Path.Combine(AppContext.BaseDirectory, "corpus", "m4");

    private static readonly Lazy<JsonDocument> Expected = new(() =>
        JsonDocument.Parse(File.ReadAllText(Path.Combine(Root, "expected.json"))));

    private static readonly Dictionary<string, ExtractionResult> Results = new(StringComparer.Ordinal);

    /// <summary>The extraction of a named corpus compilation, computed once per test run.</summary>
    public static ExtractionResult Extract(string name)
    {
        lock (Results)
        {
            if (!Results.TryGetValue(name, out var result))
            {
                result = ExtractFresh(name);
                Results.Add(name, result);
            }
            return result;
        }
    }

    /// <summary>A new compilation and extraction of a named corpus compilation.</summary>
    public static ExtractionResult ExtractFresh(string name)
    {
        var spec = Expected.Value.RootElement.GetProperty("compilations").EnumerateArray()
            .Single(c => c.GetProperty("name").GetString() == name);
        var files = new List<string>();
        foreach (var glob in spec.GetProperty("files").EnumerateArray().Select(f => f.GetString()!))
        {
            var dir = Path.GetDirectoryName(glob)!;
            files.AddRange(Directory.GetFiles(Path.Combine(Root, dir), Path.GetFileName(glob)).Select(f => dir + "/" + Path.GetFileName(f)));
        }
        files.Sort(StringComparer.Ordinal);
        var result = Extractor.Extract(CompilationFactory.FromFiles(Root, files, spec.GetProperty("checkOverflow").GetBoolean()));
        Assert.False(result.HasCompileErrors, string.Join("\n", result.Diagnostics.Select(d => d.Message)));
        return result;
    }

    /// <summary>The proof expected.json names for each proved theorem of a compilation (<c>rfl</c> or <c>decide</c>).</summary>
    public static Dictionary<string, string> ExpectedProofs(string name) =>
        Expected.Value.RootElement.GetProperty("members").GetProperty(name).EnumerateObject()
            .Where(p => p.Value.TryGetProperty("by", out _))
            .ToDictionary(p => p.Name, p => p.Value.GetProperty("by").GetString()!, StringComparer.Ordinal);

    /// <summary>Compiles and extracts one in-memory source file, which must extract without diagnostics.</summary>
    public static ExtractionResult Inline(string source)
    {
        var result = Extractor.Extract(CompilationFactory.Create([new SourceFile("Test.cs", "using Warrant;\n" + source)], checkOverflow: false));
        Assert.True(
            result.Diagnostics.Count == 0,
            string.Join("\n", result.Diagnostics.Select(d => $"{d.Id} {d.MemberKey} {d.Construct} {d.Message}")));
        return result;
    }

    public static Translation Translate(ExtractionResult result, KernelEnvironment bundle) =>
        Translator.Translate(
            result.Units.Select(u => u.Unit),
            bundle,
            result.Units.ToDictionary(u => u.Key, u => u.DisplayName, StringComparer.Ordinal));

    /// <summary>Admits every declaration of a translation into a fork of the bundle (theorems are not admitted).</summary>
    public static KernelEnvironment Admit(SemanticsBundleFixture bundle, Translation translation)
    {
        var env = bundle.Fork();
        KernelThread.Run(() =>
        {
            foreach (var unit in translation.Units)
            {
                foreach (var declaration in unit.Declarations)
                {
                    try
                    {
                        Kernel.Kernel.Add(env, declaration, KernelLimits.Corpus);
                    }
                    catch (KernelException ex)
                    {
                        Assert.Fail($"{unit.Key} ({declaration.GetType().Name}): {ex.Message}");
                    }
                }
            }
        });
        return env;
    }

    public static VirUnit Unit(ExtractionResult result, string key) =>
        result.Find(key)?.Unit ?? throw new InvalidOperationException($"no unit {key}");
}
