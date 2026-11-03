using System.Diagnostics;
using Warrant.Cic;

namespace Warrant.Semantics.Tests;

/// <summary>The committed semantics bundle (docs/m4/01, plan U2).</summary>
public sealed class BundleTests(SemanticsBundleFixture bundle) : IClassFixture<SemanticsBundleFixture>
{
    /// <summary>The roots listed in <c>lean/bundle-roots.txt</c>, without comments or blank lines.</summary>
    internal static IReadOnlyList<string> Roots() =>
        File.ReadAllLines(TestData.Path("bundle-roots.txt"))
            .Select(l => l.Trim())
            .Where(l => l.Length > 0 && !l.StartsWith('#'))
            .ToList();

    [Fact]
    public void EveryDeclarationIsAccepted() =>
        Assert.All(bundle.Results, r => Assert.True(r.Accepted, $"{r.Name}: {r.Error}"));

    [Fact]
    public void EveryRootIsInTheBundle()
    {
        var roots = Roots();
        Assert.NotEmpty(roots);
        Assert.All(roots, root => Assert.True(bundle.Env.Find(Name.Parse(root)) is not null, $"{root} is not in the bundle"));
    }

    [Fact]
    public void TheClrTheoremsAreAdmitted()
    {
        var theorems = Roots().Where(r => r.StartsWith("Warrant.Clr.", StringComparison.Ordinal)).ToList();
        Assert.Equal(11, theorems.Count);
        Assert.All(theorems, t => Assert.IsType<TheoremInfo>(bundle.Env.Find(Name.Parse(t))));
    }

    [Fact]
    public void NothingDependsOnSorry() =>
        Assert.Null(bundle.Env.Find(Name.From("sorryAx")));

    /// <summary>
    /// lean4export prints PANIC and exits 0 when a root does not exist; the export script must fail
    /// instead (plan KTD2). Needs Lean: set LEAN_TOOLCHAIN_BIN to the 4.35.0 toolchain's bin directory.
    /// </summary>
    [FactRequiringEnv("LEAN_TOOLCHAIN_BIN")]
    public void TheExportScriptFailsOnAMissingRoot()
    {
        var repo = RepositoryRoot();
        var roots = Path.Combine(repo, "lean", "bundle-roots.txt");
        var original = File.ReadAllText(roots);
        var output = Path.Combine(Path.GetTempPath(), $"warrant-bad-{Guid.NewGuid():N}.ndjson.gz");
        try
        {
            File.AppendAllText(roots, "Int32.noSuchConstant\n");
            using var script = Process.Start(new ProcessStartInfo("bash", ["scripts/export-semantics.sh", output])
            {
                WorkingDirectory = repo,
                RedirectStandardError = true,
                RedirectStandardOutput = true,
            })!;
            string stderr = script.StandardError.ReadToEnd();
            script.WaitForExit();
            Assert.NotEqual(0, script.ExitCode);
            Assert.Contains("PANIC", stderr, StringComparison.Ordinal);
        }
        finally
        {
            File.WriteAllText(roots, original);
            File.Delete(output);
        }
    }

    private static string RepositoryRoot()
    {
        var dir = new DirectoryInfo(AppContext.BaseDirectory);
        while (dir is not null && !File.Exists(Path.Combine(dir.FullName, "Warrant.slnx")))
        {
            dir = dir.Parent;
        }
        return dir?.FullName ?? throw new InvalidOperationException("repository root not found");
    }
}
