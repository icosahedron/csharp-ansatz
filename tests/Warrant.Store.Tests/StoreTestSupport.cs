using Warrant.Cic;
using Warrant.Lean4Export;

namespace Warrant.Store.Tests;

/// <summary>A temporary directory, deleted with what is in it.</summary>
internal sealed class TempDirectory : IDisposable
{
    public string Path { get; } = System.IO.Path.Combine(System.IO.Path.GetTempPath(), "warrant-store-" + Guid.NewGuid().ToString("N")[..12]);

    public string Sub(string name) => System.IO.Path.Combine(Path, name);

    public void Dispose()
    {
        if (Directory.Exists(Path))
        {
            Directory.Delete(Path, recursive: true);
        }
    }
}

internal static class Stores
{
    private static readonly Lazy<ExportFile> BundleFile = new(() => Lean4Export.Lean4Export.ReadFile(TestData.Path(SemanticsBundleFixture.FileName)));

    /// <summary>The semantics bundle's declarations as exported.</summary>
    public static IReadOnlyList<Declaration> Bundle => BundleFile.Value.Declarations;

    /// <summary>The bundle's metadata.</summary>
    public static ExportMetadata Metadata => BundleFile.Value.Metadata;

    /// <summary>Whether a declaration is the <c>Warrant</c> library's, not its Init closure's.</summary>
    public static bool IsWarrants(Declaration d) => d.Constants[0].Name.Components()[0].ToString() == "Warrant";

    /// <summary>Writes a trusted store of the declarations and returns its version.</summary>
    public static string Write(string store, IEnumerable<Declaration> declarations, string mode = Manifest.Trusted)
    {
        using var writer = StoreWriter.Create(store);
        foreach (var d in declarations)
        {
            writer.Add(d);
        }
        return writer.Commit([new ManifestSource("bundle.ndjson.gz", new string('0', 64))], Metadata.LeanVersion, Metadata.FormatVersion, mode, mode == Manifest.Verified ? "test" : null);
    }
}
