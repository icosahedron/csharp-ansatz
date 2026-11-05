using System.Security.Cryptography;
using Warrant.Kernel;
using Warrant.Meta;

namespace Warrant.TestSupport;

/// <summary>
/// The attribute sidecar (<c>tests/data/warrant-attributes.ndjson.gz</c>, plan KTD9, docs/m5a/05),
/// loaded once per test process against the semantics bundle's SHA-256, next to the checked bundle.
/// <see cref="NewMeta"/> gives each test a fork of both, so additions never leak between tests.
/// </summary>
public sealed class AttributeSidecarFixture
{
    /// <summary>The sidecar's file name under the copied test data.</summary>
    public const string FileName = "warrant-attributes.ndjson.gz";

    /// <summary>The SHA-256 (lower-case hex) of the committed bundle file.</summary>
    public static string BundleSha256 { get; } = ComputeBundleSha256();

    private static readonly Lazy<Sidecar> Shared = new(() => Sidecar.Load(TestData.Path(FileName), BundleSha256));

    /// <summary>The checked semantics bundle the sidecar describes.</summary>
    public SemanticsBundleFixture Bundle { get; } = new();

    /// <summary>The loaded, frozen sidecar.</summary>
    public Sidecar Sidecar { get; } = Shared.Value;

    /// <summary>The checked, frozen environment.</summary>
    public KernelEnvironment Env => Bundle.Env;

    /// <summary>A Meta computation over fresh forks of the bundle and the sidecar.</summary>
    public MetaM NewMeta(MetaLimits? limits = null) => new(Bundle.Fork(), limits) { Attributes = Sidecar.Fork() };

    private static string ComputeBundleSha256()
    {
        using var stream = File.OpenRead(TestData.Path(SemanticsBundleFixture.FileName));
        return Convert.ToHexStringLower(SHA256.HashData(stream));
    }
}
