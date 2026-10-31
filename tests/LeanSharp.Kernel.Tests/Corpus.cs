using LeanSharp.Cic;
using LeanSharp.Lean4Export;

namespace LeanSharp.Kernel.Tests;

internal static class Corpus
{
    public static string Path(string relative) => System.IO.Path.Combine(AppContext.BaseDirectory, "data", relative);

    public static IReadOnlyList<Declaration> Read(string relative) => Lean4Export.Lean4Export.ReadFile(Path(relative)).Declarations;

    /// <summary>Checks <paramref name="declarations"/> into a fresh environment.</summary>
    public static (KernelEnvironment Env, IReadOnlyList<CheckResult> Results) CheckAll(IEnumerable<Declaration> declarations, KernelLimits? limits = null)
    {
        var env = new KernelEnvironment();
        var results = new ExportChecker(env, limits).CheckAll(declarations);
        return (env, results);
    }
}

/// <summary>init-medium, checked once and shared by the tests that need a realistic environment.</summary>
public sealed class InitMediumFixture
{
    public InitMediumFixture()
    {
        Declarations = Corpus.Read("init-medium.ndjson.gz");
        (Env, Results) = Corpus.CheckAll(Declarations);
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

/// <summary>A fact that is skipped unless the named environment variable is set.</summary>
public sealed class FactRequiringEnvAttribute : FactAttribute
{
    public FactRequiringEnvAttribute(string variable)
    {
        if (string.IsNullOrEmpty(Environment.GetEnvironmentVariable(variable)))
        {
            Skip = $"set {variable} to run";
        }
    }
}
