namespace LeanSharp.Lean4Export.Tests;

/// <summary>Locations of the export files under <c>tests/data</c> (copied next to the test assembly).</summary>
internal static class TestData
{
    public static string Path(string relative) =>
        System.IO.Path.Combine(AppContext.BaseDirectory, "data", relative);

    public const string NatAddSucc = "Nat.add_succ.ndjson";
    public const string InitMedium = "init-medium.ndjson.gz";

    /// <summary>Every export file in the corpus.</summary>
    public static readonly string[] All =
    [
        NatAddSucc,
        InitMedium,
        "arena/001_basicDef.ndjson",
        "arena/002_badDef.ndjson",
        "arena/141_falseFromUnsafe.ndjson",
        "arena/proj-of-subst-prop.ndjson",
        "arena/rec-of-subst-prop.ndjson",
        "arena/sparse-name-index.ndjson",
    ];

    public static TheoryData<string> AllFiles() => [.. All];
}
