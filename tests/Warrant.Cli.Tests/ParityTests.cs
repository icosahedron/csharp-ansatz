using Basic.Reference.Assemblies;
using Warrant.Engine;
using Warrant.Engine.Service;
using Warrant.Frontend;

namespace Warrant.Cli.Tests;

/// <summary>
/// The regression guard for M5b R3 and KTD1 (KTD28): <c>warrant verify --format msbuild</c> prints the same bytes through
/// the server as in-process, on the M5a exit corpus, the M4 corpus and a Csc argument file project, ten times over.
/// Three things differ by design and are left out: an outcome decided by a wall-clock limit, the summary's cached count
/// and path tag, and a fallback message record (whose absence on the server path is checked, so the comparison is real).
/// </summary>
[Collection(ServerProcesses.Name)]
public sealed class ParityTests : IDisposable
{
    private const int Runs = 10;

    private static readonly string Corpora = Path.Combine(AppContext.BaseDirectory, "corpus");

    private readonly TestServer server = new();
    private readonly CscArgsProject project = new("""
        public static class Increments
        {
            [Verified] public static int Increment(int x) => unchecked(x + 1);
            [Theorem] static Proof AlwaysLarger(int x) => Prove.That(Increment(x) > x);
            [Theorem] static Proof Mismatch(int a) => Prove.That(a == a).By(Tactic.Exact(Lean.Const("Nat.zero")));
            [Theorem] static Proof Two() => Prove.That(Increment(1) == 2);
        }
        """);

    // One in-process service for every in-process run, as the server keeps one: each run otherwise loads the bundle.
    private readonly VerificationService inProcess = new(TestServer.BundlePath, TestServer.SidecarPath);

    public void Dispose()
    {
        inProcess.Dispose();
        project.Dispose();
        server.DisposeAsync().AsTask().GetAwaiter().GetResult();
    }

    private static readonly string[] Inputs = ["m5a/accepted", "m5a/refuted", "m5a/rejected", "m4/accepted", "m4/refuted", "m4/rejected", "cscargs"];

    [Fact]
    public void TheServerAndTheInProcessPathPrintTheSameRecordsTenTimesOver()
    {
        for (int run = 0; run < Runs; run++)
        {
            foreach (var input in Inputs)
            {
                string[] args = input == "cscargs"
                    ? ["--csc-args", project.ArgsFile, "--project-dir", project.Directory, "--format", "msbuild"]
                    : [Path.Combine(Corpora, input), "--format", "msbuild"];
                var (serverCode, serverOutput) = server.Verify([.. args, "--server", "auto"]);
                var (localCode, localOutput) = server.Verify([.. args, "--server", "off"], inProcess: inProcess);

                Assert.DoesNotContain("verification server unavailable", serverOutput, StringComparison.Ordinal);
                Assert.Contains("not proved. [server]", serverOutput, StringComparison.Ordinal);
                Assert.Equal(localCode, serverCode);
                Assert.True(Comparable(localOutput) == Comparable(serverOutput), $"run {run}, {input}:\n--- in-process\n{localOutput}\n--- server\n{serverOutput}");
            }
        }
    }

    /// <summary>The records the paths must agree on: KTD28's three exclusions removed.</summary>
    private static string Comparable(string output) => string.Join("\n", output.Split('\n')
        .Where(line => !(line.StartsWith("WRT1\tdiag\tinfo\t", StringComparison.Ordinal) && line.Contains("verification server unavailable", StringComparison.Ordinal)))
        .Where(line => !(line.StartsWith("WRT1\tdiag\terror\tWRT0006\t", StringComparison.Ordinal) && line.Contains("the time limit of", StringComparison.Ordinal)))
        .Select(line => line.StartsWith("WRT1\tsummary\t", StringComparison.Ordinal) ? Summary(line) : line));

    /// <summary>The summary record without its cached count and path tag; the unit and theorem counts stay.</summary>
    private static string Summary(string line)
    {
        var text = line.Replace(" [server]", "", StringComparison.Ordinal).Replace(" [in-process]", "", StringComparison.Ordinal);
        int open = text.IndexOf(" (", StringComparison.Ordinal);
        int close = text.IndexOf(" from cache", StringComparison.Ordinal);
        return open >= 0 && close > open ? text[..open] + text[(text.IndexOf(')', close) + 1)..] : text;
    }
}

/// <summary>
/// The Csc argument file project of <see cref="VerifyTests"/>: <c>cscargs/</c> copied to a temporary directory with the
/// reference pack and the Warrant package's assembly beside it, and one source file.
/// </summary>
internal sealed class CscArgsProject : IDisposable
{
    public CscArgsProject(string source)
    {
        var fixture = Path.Combine(AppContext.BaseDirectory, "cscargs");
        foreach (var file in System.IO.Directory.EnumerateFiles(fixture, "*", SearchOption.AllDirectories))
        {
            var target = Path.Combine(Directory, Path.GetRelativePath(fixture, file));
            System.IO.Directory.CreateDirectory(Path.GetDirectoryName(target)!);
            File.Copy(file, target);
        }
        var refs = System.IO.Directory.CreateDirectory(Path.Combine(Directory, "refs")).FullName;
        foreach (var info in Net100.ReferenceInfos.All)
        {
            File.WriteAllBytes(Path.Combine(refs, info.FileName), info.ImageBytes);
        }
        using (var image = typeof(CompilationFactory).Assembly.GetManifestResourceStream("Warrant.dll")!)
        using (var dll = File.Create(Path.Combine(refs, "Warrant.dll")))
        {
            image.CopyTo(dll);
        }
        System.IO.Directory.CreateDirectory(Path.Combine(Directory, "src"));
        File.WriteAllText(Path.Combine(Directory, "src", "C.cs"), "using Warrant;\n" + source);
    }

    public string Directory { get; } = Path.Combine(Path.GetTempPath(), "warrant-parity-" + Guid.NewGuid().ToString("N")[..12]);

    public string ArgsFile => Path.Combine(Directory, "sample.csc.args");

    public void Dispose() => System.IO.Directory.Delete(Directory, recursive: true);
}
