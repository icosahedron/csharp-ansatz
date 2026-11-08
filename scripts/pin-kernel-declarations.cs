// Writes src/Warrant.Engine/PinnedDeclarations.ndjson.gz: Lean's declarations that fix what the standard axioms and the
// constants the kernel computes with by name mean (SemanticsBundle.PinnedClosure, #26), taken from the committed bundle.
// Run it whenever tests/data/warrant-semantics.ndjson.gz changes:
//
//   dotnet run scripts/pin-kernel-declarations.cs
//
// SemanticsBundleTests checks that the embedded file is the closure of the committed bundle.
#:project ../src/Warrant.Engine/Warrant.Engine.csproj
using System.IO.Compression;
using Warrant.Engine;
using Warrant.Lean4Export;

// Run from the repository root.
var root = Directory.GetCurrentDirectory();
if (!File.Exists(Path.Combine(root, "tests", "data", SemanticsBundle.FileName)))
{
    Console.Error.WriteLine("Run this from the repository root.");
    return 2;
}
var bundle = Lean4Export.ReadFile(Path.Combine(root, "tests", "data", SemanticsBundle.FileName));
var pinned = SemanticsBundle.PinnedClosure(bundle.Declarations);
var output = Path.Combine(root, "src", "Warrant.Engine", SemanticsBundle.PinnedFileName);
using (var file = File.Create(output))
using (var gzip = new GZipStream(file, CompressionLevel.SmallestSize))
using (var writer = new Lean4ExportWriter(gzip, bundle.Metadata))
{
    writer.WriteAll(pinned);
}
Console.WriteLine($"{output}: {pinned.Count} declarations, {pinned.Sum(d => d.Constants.Count)} constants");
return 0;
