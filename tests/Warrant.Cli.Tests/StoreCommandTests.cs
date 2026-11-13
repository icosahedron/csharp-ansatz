using System.Globalization;
using System.Text.RegularExpressions;
using Warrant.Cic;
using Warrant.Engine;
using Warrant.Engine.Reports;
using Warrant.Lean4Export;
using Warrant.Store;
using Warrant.TestSupport;

namespace Warrant.Cli.Tests;

/// <summary>
/// <c>warrant import</c> and <c>warrant check-store</c> (M5b U13, KTD20): stores built from exports, trusted or verified,
/// and re-checked with Warrant's kernel.
/// </summary>
public sealed class StoreCommandTests : IDisposable
{
    private static readonly string Bundle = Path.Combine(AppContext.BaseDirectory, SemanticsBundle.FileName);

    private readonly string _root = Path.Combine(Path.GetTempPath(), "warrant-store-cli-" + Guid.NewGuid().ToString("N")[..12]);

    public StoreCommandTests() => Directory.CreateDirectory(_root);

    public void Dispose() => Directory.Delete(_root, recursive: true);

    private string Store => Path.Combine(_root, "store");

    private static (int Code, string Output, string Error) Import(params string[] args) => Run(ImportCommand.Run, args);

    private static (int Code, string Output, string Error) CheckStore(params string[] args) => Run(CheckStoreCommand.Run, args);

    private static (int Code, string Output, string Error) Run(Func<string[], TextWriter, TextWriter, int> command, string[] args)
    {
        using var output = new StringWriter { NewLine = "\n" };
        using var error = new StringWriter { NewLine = "\n" };
        int code = command(args, output, error);
        return (code, output.ToString(), error.ToString());
    }

    /// <summary>Writes declarations as a lean4export file.</summary>
    private string Export(string name, IEnumerable<Declaration> declarations)
    {
        var path = Path.Combine(_root, name);
        var source = Lean4Export.Lean4Export.ReadFile(Bundle).Metadata;
        using (var writer = new Lean4ExportWriter(File.Create(path), source))
        {
            writer.WriteAll(declarations.ToList());
        }
        return path;
    }

    /// <summary>The bundle with the proof of its first <c>Warrant</c> theorem replaced by the next one's.</summary>
    private static (List<Declaration> Declarations, Name Tampered) WithASwappedProof()
    {
        var declarations = Lean4Export.Lean4Export.ReadFile(Bundle).Declarations.ToList();
        var theorems = declarations.Select((d, i) => (d, i))
            .Where(p => p.d is ConstantDeclaration { Constant: TheoremInfo t } && t.Name.Components()[0].ToString() == "Warrant")
            .Take(2).ToList();
        var first = (TheoremInfo)((ConstantDeclaration)theorems[0].d).Constant;
        var second = (TheoremInfo)((ConstantDeclaration)theorems[1].d).Constant;
        declarations[theorems[0].i] = new ConstantDeclaration(first with { Proof = second.Proof });
        return (declarations, first.Name);
    }

    [Fact]
    public void ImportingTheBundleVerifiedThenCheckingTheStoreAcceptsEveryConstant()
    {
        var (code, output, error) = Import(Bundle, "--store", Store, "--verified");

        Assert.True(code == 0, error);
        Assert.Matches(@"wrote v1-[0-9a-f]{12}: 3,876 declarations, 4,175 constants in", output);
        using (var reader = StoreReader.Open(Store))
        {
            Assert.Equal(Manifest.Verified, reader.Manifest.Mode);
            Assert.Equal(Warrant.Engine.Service.Toolchain.Identity, reader.Manifest.VerifiedBy);
            Assert.Equal(OutcomeText.FileSha256(Bundle), Assert.Single(reader.Manifest.Sources).Sha256);
        }

        (code, output, error) = CheckStore(Store);

        Assert.True(code == 0, output + error);
        Assert.Matches(@"^checking store .+ \(v1-[0-9a-f]{12}, Lean 4\.35\.0\)\naccepted 3,876, rejected 0, declined 0; 4,175 constants in \d+\.\ds\n$", output);
    }

    [Fact]
    public void AConstantRepeatedIdenticallyIsStoredOnceAndOneThatDiffersFailsTheImportNamingIt()
    {
        var declarations = Lean4Export.Lean4Export.ReadFile(Bundle).Declarations;
        var again = Export("again.ndjson", declarations.Take(200));

        var (code, output, error) = Import(Bundle, again, "--store", Store);

        Assert.True(code == 0, error);
        Assert.Contains("  again.ndjson: 0 declarations stored, 200 repeated\n", output, StringComparison.Ordinal);
        Assert.Contains(": 3,876 declarations, 4,175 constants", output, StringComparison.Ordinal);

        var (tampered, name) = WithASwappedProof();
        var different = Export("different.ndjson", tampered.Where(d => d.Constants[0].Name == name));
        var before = File.ReadAllText(Path.Combine(Store, "current"));

        (code, _, error) = Import(Bundle, different, "--store", Store);

        Assert.Equal(1, code);
        Assert.Equal($"{different}: '{name}' differs from the constant of that name an earlier file declared\n", error);
        Assert.Equal(before, File.ReadAllText(Path.Combine(Store, "current")));
    }

    [Fact]
    public void ATrustedStoreWithATamperedProofFailsCheckStoreAtThatDeclarationAndAVerifiedImportRefusesIt()
    {
        var (declarations, name) = WithASwappedProof();
        var tampered = Export("tampered.ndjson", declarations);

        var (code, _, error) = Import(tampered, "--store", Store);
        Assert.True(code == 0, error);

        (code, var output, _) = CheckStore(Store);

        Assert.Equal(1, code);
        // The first rejection is the tampered theorem; declarations that use it are rejected after it, as unknown.
        var lines = output.Split('\n');
        Assert.StartsWith($"REJECTED {name}: ", lines[1], StringComparison.Ordinal);
        Assert.All(lines.Skip(2).Where(l => l.StartsWith("REJECTED ", StringComparison.Ordinal)),
            l => Assert.Contains($"unknown constant '{name}'", l, StringComparison.Ordinal));
        Assert.Matches(@"\naccepted [\d,]+, rejected [1-9][\d,]*, declined 0; ", output);

        (code, _, error) = Import(tampered, "--store", Path.Combine(_root, "verified"), "--verified");

        Assert.Equal(1, code);
        Assert.StartsWith($"REJECTED {name}: ", error, StringComparison.Ordinal);
        Assert.False(File.Exists(Path.Combine(_root, "verified", "current")));
    }

    [Fact]
    public void ImportingIntoAStoreAReaderHoldsOpenSucceedsAndTheReaderKeepsItsVersion()
    {
        var declarations = Lean4Export.Lean4Export.ReadFile(Bundle).Declarations;
        var part = Export("part.ndjson", declarations.Take(100));
        Assert.Equal(0, Import(part, "--store", Store).Code);
        using var reader = StoreReader.Open(Store);
        var count = reader.ConstantCount;

        var (code, _, error) = Import(Bundle, "--store", Store);

        Assert.True(code == 0, error);
        Assert.Equal(count, reader.ConstantCount);
        Assert.Equal(declarations.Take(100), reader.ReadAll());
        using var fresh = StoreReader.Open(Store);
        Assert.Equal(4175, fresh.ConstantCount);
    }

    [Fact]
    public void SampleStoreLooksUpTheRequestedNumberOfConstantsAndReportsTheMemoryAfterwards()
    {
        const int Count = 50, QuotientCheckRecords = 4;
        Assert.Equal(0, Import(Bundle, "--store", Store).Code);

        var (code, output, error) = Run(SampleStoreCommand.Run, [Store, "--count", $"{Count}", "--seed", "7"]);

        Assert.True(code == 0, error);
        var lines = output.Split('\n');
        Assert.Matches(@"^opened store .+ \(v1-[0-9a-f]{12}, 4,175 constants\) in \d+\.\d ms$", lines[0]);
        var looked = Regex.Match(lines[1], $@"^looked up {Count} random constants \(seed 7\) in \d+\.\d ms, decoding (\d+) records$");
        Assert.True(looked.Success, lines[1]);
        Assert.InRange(int.Parse(looked.Groups[1].Value, CultureInfo.InvariantCulture), 1, Count + QuotientCheckRecords);
        Assert.Matches(@"^GC heap \d+\.\d MB, working set \d+\.\d MB$", lines[2]);
        Assert.Equal("", lines[3]);
    }

    [Theory]
    [InlineData("import")]
    [InlineData("import", "x.ndjson")]
    [InlineData("import", "--store", "s")]
    [InlineData("import", "x.ndjson", "--store", "s", "--fuel", "lots")]
    [InlineData("check-store")]
    [InlineData("check-store", "a", "b")]
    [InlineData("check-store", "a", "--slow")]
    [InlineData("sample-store")]
    [InlineData("sample-store", "a", "--count", "many")]
    public void BadArgumentsExitTwoWithTheUsage(params string[] args)
    {
        var (code, _, error) = args[0] switch
        {
            "import" => Import(args[1..]),
            "check-store" => CheckStore(args[1..]),
            _ => Run(SampleStoreCommand.Run, args[1..]),
        };

        Assert.Equal(2, code);
        Assert.Contains("usage: warrant " + args[0], error, StringComparison.Ordinal);
    }

    /// <summary>
    /// M5b's exit criterion for the store (R14): Lean 4.35.0's full Init and then the bundle, verified, and the store
    /// re-checked. Export Init with <c>scripts/export-lean-library.sh</c> and point <c>WARRANT_INIT_EXPORT</c> at it.
    /// </summary>
    [FactRequiringEnv("WARRANT_INIT_EXPORT")]
    public void AStoreOfInitAndTheBundlePassesCheckStore()
    {
        var init = Environment.GetEnvironmentVariable("WARRANT_INIT_EXPORT")!;

        var (code, output, error) = Import(init, Bundle, "--store", Store, "--verified");

        Assert.True(code == 0, output + error);
        Assert.Contains($"  {SemanticsBundle.FileName}: ", output, StringComparison.Ordinal);

        (code, output, error) = CheckStore(Store, "--quiet");

        Assert.True(code == 0, output + error);
        Assert.Matches(@"\naccepted [\d,]+, rejected 0, declined 0; [\d,]+ constants in", output);
    }
}
