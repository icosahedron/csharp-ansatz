using System.Text.Json;
using Microsoft.CodeAnalysis.CSharp;
using Warrant.Extraction;
using Warrant.TestSupport;

namespace Warrant.Extraction.Tests;

/// <summary>The M4, M5a and M6 corpora and their expected outcomes (tests/corpus/*/expected.json); the M4 one by default.</summary>
internal static class Corpus
{
    public static string Root => CorpusCompilations.Root;

    private static readonly Dictionary<(string, string), ExtractionResult> Results = [];

    public static IEnumerable<CorpusSet> Sets => [CorpusSet.M4, CorpusSet.M5a, CorpusSet.M6];

    public static CorpusSet Set(string name) => Sets.Single(s => s.Name == name);

    public static IEnumerable<string> CompilationNames => CorpusCompilations.Names;

    /// <summary>The relative paths of a named compilation's files, expanding its globs and exclusions.</summary>
    public static List<string> Files(string name) => CorpusCompilations.Files(name);

    public static bool CheckOverflow(string name) => CorpusCompilations.CheckOverflow(name);

    public static CSharpCompilation Compile(string name) => CorpusCompilations.Compile(name);

    /// <summary>The extraction of a named M4 compilation, computed once per test run.</summary>
    public static ExtractionResult Extract(string name) => Extract(CorpusSet.M4, name);

    /// <summary>The extraction of a named compilation of a corpus, computed once per test run.</summary>
    public static ExtractionResult Extract(CorpusSet set, string name)
    {
        lock (Results)
        {
            if (!Results.TryGetValue((set.Name, name), out var result))
            {
                result = Extractor.Extract(set.Compile(name));
                Results.Add((set.Name, name), result);
            }
            return result;
        }
    }

    /// <summary>The expected outcome of every member of a compilation, by key.</summary>
    public static IEnumerable<(string Key, JsonElement Outcome)> Members(CorpusSet set, string name) =>
        set.Expected.GetProperty("members").GetProperty(name).EnumerateObject().Select(p => (p.Name, p.Value));

    public static JsonElement Member(CorpusSet set, string name, string key) =>
        set.Expected.GetProperty("members").GetProperty(name).GetProperty(key);
}
