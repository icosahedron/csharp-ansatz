using Warrant.Cic;
using Warrant.Kernel;
using Warrant.Lean4Export;

namespace Warrant.Engine;

/// <summary>
/// The semantics bundle (docs/m4/01): Init's constants and the library, checked by the kernel declaration by declaration
/// and frozen, so every run admits into its own fork of it (KTD17).
/// </summary>
public sealed class SemanticsBundle
{
    /// <summary>The bundle's file name as the repository commits it (<c>tests/data/warrant-semantics.ndjson.gz</c>).</summary>
    public const string FileName = "warrant-semantics.ndjson.gz";

    /// <summary>Wraps a bundle that has already been checked and frozen.</summary>
    /// <param name="declarations">The bundle's declarations, in file order; NDJSON export writes them first.</param>
    /// <param name="env">The environment the declarations were checked into; must be frozen.</param>
    /// <param name="metadata">The file's metadata, whose Lean version export carries over; null if unknown.</param>
    /// <exception cref="ArgumentException"><paramref name="env"/> is not frozen.</exception>
    public SemanticsBundle(IReadOnlyList<Declaration> declarations, KernelEnvironment env, ExportMetadata? metadata = null)
    {
        ArgumentNullException.ThrowIfNull(declarations);
        ArgumentNullException.ThrowIfNull(env);
        if (!env.IsFrozen)
        {
            throw new ArgumentException("The bundle's environment must be frozen.", nameof(env));
        }
        Declarations = declarations;
        Env = env;
        Metadata = metadata;
    }

    /// <summary>The bundle's declarations, in file order.</summary>
    public IReadOnlyList<Declaration> Declarations { get; }

    /// <summary>The checked, frozen environment.</summary>
    public KernelEnvironment Env { get; }

    /// <summary>The metadata of the file the bundle was read from, or null.</summary>
    public ExportMetadata? Metadata { get; }

    /// <summary>
    /// Reads a bundle file (gzip or plain NDJSON), checks every declaration with <see cref="ExportChecker"/> into a new
    /// environment, and freezes it.
    /// </summary>
    /// <param name="path">The bundle file.</param>
    /// <returns>The checked bundle.</returns>
    /// <exception cref="InvalidDataException">The kernel rejects a declaration of the bundle.</exception>
    /// <exception cref="Lean4ExportFormatException">The file is malformed.</exception>
    public static SemanticsBundle Load(string path)
    {
        var file = Lean4Export.Lean4Export.ReadFile(path);
        var env = new KernelEnvironment();
        var results = new ExportChecker(env).CheckAll(file.Declarations);
        if (results.FirstOrDefault(r => !r.Accepted) is { } rejected)
        {
            throw new InvalidDataException($"The semantics bundle {path} does not check: {rejected.Name}: {rejected.Error}");
        }
        env.Freeze();
        return new SemanticsBundle(file.Declarations, env, file.Metadata);
    }
}
