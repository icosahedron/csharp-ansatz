using System.Collections.Immutable;
using System.Reflection;
using System.Security.Cryptography;
using Warrant.Cic;
using Warrant.Kernel;
using Warrant.Lean4Export;
using Warrant.Meta;
using Warrant.Semantics;
using Warrant.Vir;

namespace Warrant.Engine.Service;

/// <summary>
/// The toolchain identity (M5b KTD9, docs/m5b/04): a SHA-256 over the module version IDs of the assemblies that decide an
/// outcome. Builds are deterministic, so a module version ID changes exactly when its assembly's code does. The identity
/// keys the result cache, names the server's endpoint and appears in <c>status</c>.
/// </summary>
public static class Toolchain
{
    private static readonly Lazy<string> LazyIdentity = new(() => IdentityOf(Assemblies));

    /// <summary>
    /// The assemblies the identity covers, in hashing order: <c>Warrant.Cic</c>, <c>Warrant.Kernel</c>,
    /// <c>Warrant.Semantics</c>, <c>Warrant.Meta</c>, <c>Warrant.Engine</c>, <c>Warrant.Vir</c> and <c>Warrant.Lean4Export</c>.
    /// </summary>
    public static ImmutableArray<Assembly> Assemblies { get; } =
    [
        typeof(Name).Assembly,
        typeof(KernelEnvironment).Assembly,
        typeof(Translator).Assembly,
        typeof(MetaM).Assembly,
        typeof(Pipeline).Assembly,
        typeof(VirUnit).Assembly,
        typeof(Lean4ExportWriter).Assembly,
    ];

    /// <summary>The identity of this process's toolchain, as 64 lowercase hex digits; computed once.</summary>
    public static string Identity => LazyIdentity.Value;

    /// <summary>The SHA-256, as 64 lowercase hex digits, of the given assemblies' module version IDs in order.</summary>
    /// <param name="assemblies">The assemblies.</param>
    /// <returns>The identity.</returns>
    public static string IdentityOf(IEnumerable<Assembly> assemblies)
    {
        ArgumentNullException.ThrowIfNull(assemblies);
        using var hash = IncrementalHash.CreateHash(HashAlgorithmName.SHA256);
        foreach (var assembly in assemblies)
        {
            hash.AppendData(assembly.ManifestModule.ModuleVersionId.ToByteArray());
        }
        return Convert.ToHexStringLower(hash.GetHashAndReset());
    }
}
