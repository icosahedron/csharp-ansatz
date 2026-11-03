using System.Text.Json;
using Microsoft.CodeAnalysis.CSharp;
using Warrant.Extraction;
using Warrant.Frontend;
using Xunit;

namespace Warrant.TestSupport;

/// <summary>
/// The M4 corpus (<c>tests/corpus/m4</c>, docs/m4/02), which each test project that compiles it copies to
/// <c>corpus/m4</c> in its output directory, and the compilations <c>expected.json</c> names.
/// </summary>
public static class CorpusCompilations
{
    /// <summary>The copied corpus directory.</summary>
    public static string Root { get; } = Path.Combine(AppContext.BaseDirectory, "corpus", "m4");

    private static readonly Lazy<JsonDocument> ExpectedDocument = new(() =>
        JsonDocument.Parse(File.ReadAllText(Path.Combine(Root, "expected.json"))));

    /// <summary>The root of <c>expected.json</c>.</summary>
    public static JsonElement Expected => ExpectedDocument.Value.RootElement;

    /// <summary>The names of the compilations, in file order.</summary>
    public static IEnumerable<string> Names =>
        Expected.GetProperty("compilations").EnumerateArray().Select(c => c.GetProperty("name").GetString()!);

    /// <summary>The relative paths of a named compilation's files, expanding its globs and exclusions, in ordinal order.</summary>
    public static List<string> Files(string name)
    {
        var spec = Spec(name);
        var excluded = spec.TryGetProperty("exclude", out var ex)
            ? ex.EnumerateArray().Select(e => e.GetString()!).ToHashSet(StringComparer.Ordinal)
            : [];
        var files = new List<string>();
        foreach (var glob in spec.GetProperty("files").EnumerateArray().Select(f => f.GetString()!))
        {
            var dir = Path.GetDirectoryName(glob)!;
            var pattern = Path.GetFileName(glob);
            files.AddRange(Directory.GetFiles(Path.Combine(Root, dir), pattern)
                .Select(f => dir + "/" + Path.GetFileName(f))
                .Where(f => !excluded.Contains(f)));
        }
        files.Sort(StringComparer.Ordinal);
        return files;
    }

    /// <summary>Whether a named compilation is compiled with overflow checking.</summary>
    public static bool CheckOverflow(string name) => Spec(name).GetProperty("checkOverflow").GetBoolean();

    /// <summary>The compilation extraction reads for a named corpus compilation.</summary>
    public static CSharpCompilation Compile(string name) => CompilationFactory.FromFiles(Root, Files(name), CheckOverflow(name));

    /// <summary>Compiles and extracts one in-memory source file, which must extract without diagnostics.</summary>
    public static ExtractionResult Inline(string source)
    {
        var result = Extractor.Extract(CompilationFactory.Create([new SourceFile("Test.cs", "using Warrant;\n" + source)], checkOverflow: false));
        Assert.True(
            result.Diagnostics.Count == 0,
            string.Join("\n", result.Diagnostics.Select(d => $"{d.Id} {d.MemberKey} {d.Construct} {d.Message}")));
        return result;
    }

    private static JsonElement Spec(string name) =>
        Expected.GetProperty("compilations").EnumerateArray().Single(c => c.GetProperty("name").GetString() == name);
}
