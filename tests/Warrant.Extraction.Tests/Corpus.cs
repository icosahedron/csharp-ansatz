using System.Text.Json;
using Microsoft.CodeAnalysis.CSharp;
using Warrant.Extraction;
using Warrant.TestSupport;

namespace Warrant.Extraction.Tests;

/// <summary>The M4 corpus and its expected outcomes (tests/corpus/m4/expected.json).</summary>
internal static class Corpus
{
    public static string Root => CorpusCompilations.Root;

    private static readonly Dictionary<string, ExtractionResult> Results = new(StringComparer.Ordinal);

    public static IEnumerable<string> CompilationNames => CorpusCompilations.Names;

    /// <summary>The relative paths of a named compilation's files, expanding its globs and exclusions.</summary>
    public static List<string> Files(string name) => CorpusCompilations.Files(name);

    public static bool CheckOverflow(string name) => CorpusCompilations.CheckOverflow(name);

    public static CSharpCompilation Compile(string name) => CorpusCompilations.Compile(name);

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
        CorpusCompilations.Expected.GetProperty("members").GetProperty(name).EnumerateObject().Select(p => (p.Name, p.Value));

    public static JsonElement Member(string name, string key) =>
        CorpusCompilations.Expected.GetProperty("members").GetProperty(name).GetProperty(key);
}
