namespace Warrant.TestSupport;

/// <summary>
/// Paths into <c>tests/data</c>, which each test project copies to <c>data/</c> in its output
/// directory.
/// </summary>
public static class TestData
{
    /// <summary>The path of <paramref name="relative"/> (for example <c>arena/001_basicDef.ndjson</c>) under the copied test data.</summary>
    public static string Path(string relative) => System.IO.Path.Combine(AppContext.BaseDirectory, "data", relative);
}
