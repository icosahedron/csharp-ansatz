using Warrant.Cic;
using Warrant.Lean4Export;

namespace Warrant.Kernel.Tests;

internal static class Corpus
{
    public static IReadOnlyList<Declaration> Read(string relative) => Lean4Export.Lean4Export.ReadFile(TestData.Path(relative)).Declarations;

    /// <summary>Checks <paramref name="declarations"/> into a fresh environment.</summary>
    public static (KernelEnvironment Env, IReadOnlyList<CheckResult> Results) CheckAll(IEnumerable<Declaration> declarations, KernelLimits? limits = null)
    {
        var env = new KernelEnvironment();
        var results = new ExportChecker(env, limits).CheckAll(declarations);
        return (env, results);
    }
}

/// <summary>
/// init-medium, checked once and shared by the tests that need a realistic environment. The
/// environment is frozen: tests that admit declarations do so into a fork of it.
/// </summary>
public sealed class InitMediumFixture
{
    public InitMediumFixture()
    {
        Declarations = Corpus.Read("init-medium.ndjson.gz");
        (Env, Results) = Corpus.CheckAll(Declarations);
        Env.Freeze();
    }

    public IReadOnlyList<Declaration> Declarations { get; }

    public KernelEnvironment Env { get; }

    public IReadOnlyList<CheckResult> Results { get; }

    /// <summary>An environment containing exactly the declarations before the one introducing <paramref name="name"/>.</summary>
    public KernelEnvironment EnvBefore(Name name)
    {
        var prefix = Declarations.TakeWhile(d => d.Constants.All(c => c.Name != name)).ToList();
        Assert.True(prefix.Count < Declarations.Count, $"'{name}' is not in init-medium");
        var (env, results) = Corpus.CheckAll(prefix);
        Assert.All(results, r => Assert.True(r.Accepted, r.Error));
        return env;
    }

    public Declaration DeclarationOf(Name name) => Declarations.First(d => d.Constants.Any(c => c.Name == name));
}
