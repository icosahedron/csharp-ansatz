using System.Text.Json;
using Microsoft.CodeAnalysis.CSharp;
using Warrant.Extraction;
using Warrant.Frontend;

namespace Warrant.Extraction.Tests;

/// <summary>The M4 corpus and its expected outcomes (tests/corpus/m4/expected.json).</summary>
internal static class Corpus
{
    public static string Root { get; } = Path.Combine(AppContext.BaseDirectory, "corpus", "m4");

    private static readonly Lazy<JsonDocument> Expected = new(() =>
        JsonDocument.Parse(File.ReadAllText(Path.Combine(Root, "expected.json"))));

    private static readonly Dictionary<string, ExtractionResult> Results = new(StringComparer.Ordinal);

    public static IEnumerable<string> CompilationNames =>
        Expected.Value.RootElement.GetProperty("compilations").EnumerateArray().Select(c => c.GetProperty("name").GetString()!);

    /// <summary>The relative paths of a named compilation's files, expanding its globs and exclusions.</summary>
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

    public static bool CheckOverflow(string name) => Spec(name).GetProperty("checkOverflow").GetBoolean();

    public static CSharpCompilation Compile(string name) => CompilationFactory.FromFiles(Root, Files(name), CheckOverflow(name));

    /// <summary>The extraction of a named compilation, computed once per test run.</summary>
    public static ExtractionResult Extract(string name)
    {
        lock (Results)
        {
            if (!Results.TryGetValue(name, out var result))
            {
                result = Extractor.Extract(Compile(name));
                Results.Add(name, result);
            }
            return result;
        }
    }

    /// <summary>The expected outcome of every member of a compilation, by key.</summary>
    public static IEnumerable<(string Key, JsonElement Outcome)> Members(string name) =>
        Expected.Value.RootElement.GetProperty("members").GetProperty(name).EnumerateObject().Select(p => (p.Name, p.Value));

    public static JsonElement Member(string name, string key) =>
        Expected.Value.RootElement.GetProperty("members").GetProperty(name).GetProperty(key);

    private static JsonElement Spec(string name) =>
        Expected.Value.RootElement.GetProperty("compilations").EnumerateArray().Single(c => c.GetProperty("name").GetString() == name);
}
