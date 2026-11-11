using System.Text.Json;
using Microsoft.CodeAnalysis.CSharp;
using Warrant.Extraction;
using Warrant.Frontend;
using Xunit;

namespace Warrant.TestSupport;

/// <summary>
/// A corpus directory (<c>tests/corpus/&lt;name&gt;</c>), which each test project that compiles it copies to
/// <c>corpus/&lt;name&gt;</c> in its output directory, and the compilations its <c>expected.json</c> names.
/// </summary>
public sealed class CorpusSet
{
    private readonly Lazy<JsonDocument> _expected;

    private CorpusSet(string name)
    {
        Name = name;
        Root = Path.Combine(AppContext.BaseDirectory, "corpus", name);
        _expected = new(() => JsonDocument.Parse(File.ReadAllText(Path.Combine(Root, "expected.json"))));
    }

    /// <summary>The M4 corpus (docs/m4/02).</summary>
    public static CorpusSet M4 { get; } = new("m4");

    /// <summary>The M5a corpus (docs/m5a/01).</summary>
    public static CorpusSet M5a { get; } = new("m5a");

    /// <summary>
    /// The M6 corpus (plan M6 KTD24). Until plan U11 and U13 only the extraction, analyzer and translation tests copy and
    /// read it: the engine, CLI, cross-check and differential tests do not, and pin that (tests/corpus/m6/README.md).
    /// </summary>
    public static CorpusSet M6 { get; } = new("m6");

    /// <summary>The directory name, <c>m4</c>, <c>m5a</c> or <c>m6</c>.</summary>
    public string Name { get; }

    /// <summary>The copied corpus directory.</summary>
    public string Root { get; }

    /// <summary>The root of <c>expected.json</c>.</summary>
    public JsonElement Expected => _expected.Value.RootElement;

    /// <summary>The names of the compilations, in file order.</summary>
    public IEnumerable<string> Names =>
        Expected.GetProperty("compilations").EnumerateArray().Select(c => c.GetProperty("name").GetString()!);

    /// <summary>The relative paths of a named compilation's files, expanding its globs and exclusions, in ordinal order.</summary>
    public List<string> Files(string name)
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
    public bool CheckOverflow(string name) => Spec(name).GetProperty("checkOverflow").GetBoolean();

    /// <summary>The compilation extraction reads for a named corpus compilation.</summary>
    public CSharpCompilation Compile(string name) => CompilationFactory.FromFiles(Root, Files(name), CheckOverflow(name));

    /// <inheritdoc/>
    public override string ToString() => Name;

    private JsonElement Spec(string name) =>
        Expected.GetProperty("compilations").EnumerateArray().Single(c => c.GetProperty("name").GetString() == name);
}

/// <summary>The M4 corpus (<see cref="CorpusSet.M4"/>), which most tests compile, and inline sources.</summary>
public static class CorpusCompilations
{
    /// <summary>The copied M4 corpus directory.</summary>
    public static string Root => CorpusSet.M4.Root;

    /// <summary>The root of the M4 <c>expected.json</c>.</summary>
    public static JsonElement Expected => CorpusSet.M4.Expected;

    /// <summary>The names of the M4 compilations, in file order.</summary>
    public static IEnumerable<string> Names => CorpusSet.M4.Names;

    /// <summary>The relative paths of a named M4 compilation's files, in ordinal order.</summary>
    public static List<string> Files(string name) => CorpusSet.M4.Files(name);

    /// <summary>Whether a named M4 compilation is compiled with overflow checking.</summary>
    public static bool CheckOverflow(string name) => CorpusSet.M4.CheckOverflow(name);

    /// <summary>The compilation extraction reads for a named M4 corpus compilation.</summary>
    public static CSharpCompilation Compile(string name) => CorpusSet.M4.Compile(name);

    /// <summary>Compiles and extracts one in-memory source file, which must extract without diagnostics.</summary>
    public static ExtractionResult Inline(string source)
    {
        var result = Extractor.Extract(CompilationFactory.Create([new SourceFile("Test.cs", "using Warrant;\n" + source)], checkOverflow: false));
        Assert.True(
            result.Diagnostics.Count == 0,
            string.Join("\n", result.Diagnostics.Select(d => $"{d.Id} {d.MemberKey} {d.Construct} {d.Message}")));
        return result;
    }
}
