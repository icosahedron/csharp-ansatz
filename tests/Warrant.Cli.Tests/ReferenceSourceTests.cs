using System.Security.Cryptography;
using Basic.Reference.Assemblies;
using Warrant.Frontend;

namespace Warrant.Cli.Tests;

/// <summary>
/// <c>warrant verify --reference-source</c> (#32, #52): a <c>[Closed]</c> class from a referenced project is checked from the
/// source record that project's build wrote. The library here is compiled from its own argument file, as its build would
/// compile it, its assembly is what the app references, and its record hashes every file under it.
/// </summary>
public sealed class ReferenceSourceTests : IDisposable
{
    private const string Shapes = """
        namespace Shapes
        {
            [Warrant.Closed]
            public sealed class Color
            {
                public static Color Red { get; } = new();
                public static Color Blue { get; } = new();
                private Color() { }
            }
        }
        """;

    private const string UsesColor = """
        public static class Painter
        {
            [Verified]
            public static bool Same(Shapes.Color a, Shapes.Color b) => a == b;
        }
        """;

    private const string UsesNothing = """
        public static class Painter
        {
            [Verified]
            public static int Twice(int x) => unchecked(x + x);
        }
        """;

    private readonly string _root = Path.Combine(Path.GetTempPath(), "warrant-refsrc-" + Guid.NewGuid().ToString("N")[..12]);

    public ReferenceSourceTests()
    {
        Project(Library, "Shapes", Shapes, extraArgs: []);
        var compilation = CompilationFactory.FromCscArgs(Path.Combine(Library, "shapes.csc.args"), Library);
        Assert.Null(CompilationFactory.Failure(compilation));
        Directory.CreateDirectory(Path.Combine(App, "refs"));
        using var dll = File.Create(Path.Combine(App, "refs", "Shapes.dll"));
        Assert.True(compilation.Emit(dll).Success);
    }

    public void Dispose() => Directory.Delete(_root, recursive: true);

    private string Library => Path.Combine(_root, "Shapes");

    private string App => Path.Combine(_root, "Painter");

    /// <summary>
    /// A project as its build leaves it: the sample's arguments, compiling <c>src/C.cs</c> (holding
    /// <paramref name="source"/>) into <paramref name="name"/>.dll, and the reference pack and Warrant under <c>refs/</c>.
    /// </summary>
    private static void Project(string directory, string name, string source, string[] extraArgs)
    {
        var fixture = Path.Combine(AppContext.BaseDirectory, "cscargs");
        foreach (var file in Directory.EnumerateFiles(fixture, "*", SearchOption.AllDirectories))
        {
            var target = Path.Combine(directory, Path.GetRelativePath(fixture, file));
            Directory.CreateDirectory(Path.GetDirectoryName(target)!);
            File.Copy(file, target);
        }
        var refs = Directory.CreateDirectory(Path.Combine(directory, "refs")).FullName;
        foreach (var info in Net100.ReferenceInfos.All)
        {
            File.WriteAllBytes(Path.Combine(refs, info.FileName), info.ImageBytes);
        }
        using (var image = typeof(CompilationFactory).Assembly.GetManifestResourceStream("Warrant.dll")!)
        using (var dll = File.Create(Path.Combine(refs, "Warrant.dll")))
        {
            image.CopyTo(dll);
        }
        Directory.CreateDirectory(Path.Combine(directory, "src"));
        File.WriteAllText(Path.Combine(directory, "src", "C.cs"), "using Warrant;\n" + source);
        var sample = Path.Combine(directory, "sample.csc.args");
        var args = File.ReadAllLines(sample)
            .Select(l => l.Replace("bin/Sample.dll", $"bin/{name}.dll", StringComparison.Ordinal).Replace("bin/ref/Sample.dll", $"bin/ref/{name}.dll", StringComparison.Ordinal))
            .Concat(extraArgs);
        File.Delete(sample);
        File.WriteAllLines(Path.Combine(directory, $"{name.ToLowerInvariant()}.csc.args"), args);
    }

    /// <summary>The library's source record, as Warrant.Build writes it: every file under the library, hashed now.</summary>
    private string Record(string? path = null, string header = "warrant-source 2")
    {
        var lines = new List<string> { header, "assembly=Shapes", $"args={Path.Combine(Library, "shapes.csc.args")}", $"project={Library}" };
        foreach (var file in Directory.EnumerateFiles(Library, "*", SearchOption.AllDirectories).Order(StringComparer.Ordinal))
        {
            lines.Add($"file={Convert.ToHexString(SHA256.HashData(File.ReadAllBytes(file)))}|{file}");
        }
        path ??= Path.Combine(_root, "shapes.warrant.source");
        File.WriteAllLines(path, lines);
        return path;
    }

    private (int Code, string Output) Verify(string appSource, params string[] options)
    {
        if (!Directory.Exists(Path.Combine(App, "src")))
        {
            Project(App, "Painter", appSource, extraArgs: ["/reference:refs/Shapes.dll"]);
        }
        using var output = new StringWriter { NewLine = "\n" };
        var code = VerifyCommand.Run(
            ["--csc-args", Path.Combine(App, "painter.csc.args"), "--project-dir", App, "--server", "off", .. options], output, output);
        return (code, output.ToString());
    }

    private void EditLibrary() => File.AppendAllText(Path.Combine(Library, "src", "C.cs"), "// edited\n");

    [Fact]
    public void AClosedClassFromARecordedProjectVerifiesAndWithoutTheRecordIsWrt0002()
    {
        var record = Record();

        var (code, output) = Verify(UsesColor, "--reference-source", record);
        var (without, withoutOutput) = Verify(UsesColor);

        Assert.True(code == 0, output);
        Assert.Contains("Warrant: 2 verified units", output, StringComparison.Ordinal);
        Assert.Equal(1, without);
        Assert.Matches(@"error WRT0002: .*Shapes\.Color.*no recorded source for Shapes", withoutOutput);
    }

    [Fact]
    public void AStaleRecordIsWrt0012AndExitsOne()
    {
        var record = Record();
        EditLibrary();

        var (code, output) = Verify(UsesColor, "--reference-source", record);

        Assert.Equal(1, code);
        Assert.Contains("error WRT0012: Warrant cannot read a referenced project's source:", output, StringComparison.Ordinal);
        Assert.Contains("C.cs changed since Shapes was compiled; build Shapes again", output, StringComparison.Ordinal);
    }

    [Fact]
    public void AMissingRecordOrAFileThatNamesNoAssemblyIsNoRecord()
    {
        // The build passes a record path for every referenced project that imports Warrant.Build, including one whose
        // record was deleted because a file was saved during its compile; such a project's closed classes are unchecked.
        var junk = Path.Combine(_root, "junk.txt");
        File.WriteAllText(junk, "not a record\n");

        var (missing, missingOutput) = Verify(UsesColor, "--reference-source", Path.Combine(_root, "nowhere.warrant.source"));
        var (notARecord, notARecordOutput) = Verify(UsesColor, "--reference-source", junk);

        Assert.Equal(1, missing);
        Assert.Contains("no recorded source for Shapes", missingOutput, StringComparison.Ordinal);
        Assert.Equal(1, notARecord);
        Assert.Contains("no recorded source for Shapes", notARecordOutput, StringComparison.Ordinal);
    }

    [Fact]
    public void ARecordInAFormatWarrantCannotReadIsWrt0012OnlyWhenItsClassIsUsed()
    {
        // #120: an unreadable record naming Shapes fails the run when Color is used, and costs nothing otherwise.
        var record = Record(header: "warrant-source 9");

        var (used, usedOutput) = Verify(UsesColor, "--reference-source", record);

        Assert.Equal(1, used);
        Assert.Contains("error WRT0012:", usedOutput, StringComparison.Ordinal);
        Assert.Contains("not a Warrant source record this Warrant can read", usedOutput, StringComparison.Ordinal);
    }

    [Fact]
    public void ARecordWhoseAssemblyNoUnitUsesIsNotLoaded()
    {
        // Loading is lazy: a stale record for a project whose closed classes are not used does not fail the run.
        var record = Record();
        EditLibrary();

        var (code, output) = Verify(UsesNothing, "--reference-source", record);

        Assert.True(code == 0, output);
        Assert.DoesNotContain("WRT0012", output, StringComparison.Ordinal);
    }

    [Fact]
    public void OfTwoRecordsNamingOneAssemblyTheFirstIsUsed()
    {
        var good = Record(Path.Combine(_root, "good.warrant.source"));
        var stale = Record(Path.Combine(_root, "stale.warrant.source"));
        File.AppendAllText(stale, "file=00|" + Path.Combine(Library, "src", "C.cs") + "\n");

        var (goodFirst, goodFirstOutput) = Verify(UsesColor, "--reference-source", good, "--reference-source", stale);
        var (staleFirst, staleFirstOutput) = Verify(UsesColor, "--reference-source", stale, "--reference-source", good);

        Assert.True(goodFirst == 0, goodFirstOutput);
        Assert.Equal(1, staleFirst);
        Assert.Contains("C.cs changed since Shapes was compiled", staleFirstOutput, StringComparison.Ordinal);
    }

    [Fact]
    public void AMultiTargetedRunDoesNotUseRecords()
    {
        // A multi-targeted project ships with every framework's build of the referenced project, and a record is one
        // framework's, so with --keep-conditional-check a referenced closed class is WRT0002.
        var record = Record();

        var (code, output) = Verify(UsesColor, "--reference-source", record, "--keep-conditional-check");

        Assert.Equal(1, code);
        Assert.Matches(@"error WRT0002: .*Shapes\.Color.*a multi-targeted project cannot use it", output);
    }
}
