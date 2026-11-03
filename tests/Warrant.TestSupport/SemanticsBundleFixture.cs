using Warrant.Cic;
using Warrant.Kernel;

namespace Warrant.TestSupport;

/// <summary>
/// The semantics bundle (<c>tests/data/warrant-semantics.ndjson.gz</c>, docs/m4/01), checked once
/// declaration by declaration and then frozen. Tests admit into a <see cref="Fork"/> of it, so they
/// cannot see each other's declarations and can run in parallel.
/// </summary>
public sealed class SemanticsBundleFixture
{
    /// <summary>The bundle's file name under the copied test data.</summary>
    public const string FileName = "warrant-semantics.ndjson.gz";

    /// <summary>Reads, checks and freezes the bundle.</summary>
    public SemanticsBundleFixture()
    {
        Declarations = Lean4Export.Lean4Export.ReadFile(TestData.Path(FileName)).Declarations;
        Env = new KernelEnvironment();
        Results = new ExportChecker(Env).CheckAll(Declarations);
        Env.Freeze();
    }

    /// <summary>The bundle's declarations, in file order.</summary>
    public IReadOnlyList<Declaration> Declarations { get; }

    /// <summary>The checked, frozen environment.</summary>
    public KernelEnvironment Env { get; }

    /// <summary>The kernel's verdict on each declaration.</summary>
    public IReadOnlyList<CheckResult> Results { get; }

    /// <summary>A fresh overlay on the bundle.</summary>
    public KernelEnvironment Fork() => Env.Fork();
}
