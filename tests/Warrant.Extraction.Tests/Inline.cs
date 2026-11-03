using Warrant.Extraction;
using Warrant.Frontend;
using Warrant.Vir;

namespace Warrant.Extraction.Tests;

/// <summary>Compiles and extracts a single in-memory source file.</summary>
internal static class Inline
{
    public static ExtractionResult Extract(string source, bool checkOverflow = false) =>
        Extractor.Extract(CompilationFactory.Create([new SourceFile("Test.cs", "using Warrant;\n" + source)], checkOverflow));

    public static VirUnit Unit(ExtractionResult result, string key)
    {
        var unit = result.Find(key);
        Assert.True(unit is not null, $"No unit {key}; diagnostics:\n" + string.Join("\n", result.Diagnostics.Select(d => $"{d.Id} {d.MemberKey} {d.Construct}")));
        return unit.Unit;
    }

    /// <summary>The single diagnostic about a key, as <c>id | construct</c>.</summary>
    public static string Only(ExtractionResult result, string key)
    {
        var d = Assert.Single(result.DiagnosticsFor(key));
        return d.Id + " | " + d.Construct;
    }

    public static IEnumerable<string> NonNull(VirUnit unit) =>
        unit.Assumptions.Where(a => a.Kind == VirAssumptionKind.NonNull).Select(a => a.Subject);
}
