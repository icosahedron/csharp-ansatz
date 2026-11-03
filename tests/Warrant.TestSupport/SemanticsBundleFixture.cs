using Warrant.Cic;
using Warrant.Kernel;

namespace Warrant.TestSupport;

/// <summary>
/// The semantics bundle (<c>tests/data/warrant-semantics.ndjson.gz</c>, docs/m4/01), checked once per
/// test process declaration by declaration and then frozen; every instance shares it. Tests admit into a
/// <see cref="Fork"/> of it, so they cannot see each other's declarations and can run in parallel.
/// </summary>
public sealed class SemanticsBundleFixture
{
    /// <summary>The bundle's file name under the copied test data.</summary>
    public const string FileName = "warrant-semantics.ndjson.gz";

    private static readonly Lazy<Checked> Shared = new(Check);

    private readonly Checked _bundle = Shared.Value;

    /// <summary>The bundle's declarations, in file order.</summary>
    public IReadOnlyList<Declaration> Declarations => _bundle.Declarations;

    /// <summary>The checked, frozen environment.</summary>
    public KernelEnvironment Env => _bundle.Env;

    /// <summary>The kernel's verdict on each declaration.</summary>
    public IReadOnlyList<CheckResult> Results => _bundle.Results;

    /// <summary>A fresh overlay on the bundle.</summary>
    public KernelEnvironment Fork() => Env.Fork();

    /// <summary>Reads, checks and freezes the bundle.</summary>
    private static Checked Check()
    {
        var declarations = Lean4Export.Lean4Export.ReadFile(TestData.Path(FileName)).Declarations;
        var env = new KernelEnvironment();
        var results = new ExportChecker(env).CheckAll(declarations);
        env.Freeze();
        return new Checked(declarations, env, results);
    }

    private sealed record Checked(IReadOnlyList<Declaration> Declarations, KernelEnvironment Env, IReadOnlyList<CheckResult> Results);
}
