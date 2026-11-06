using System.Collections.Immutable;
using Warrant.Cic;
using Warrant.Kernel;
using Warrant.Lean4Export;

namespace Warrant.Engine;

/// <summary>
/// A unit's certificate (M5b KTD14, docs/m5b/04): the lean4export NDJSON of exactly the declarations the unit admitted
/// (<see cref="UnitOutcome.Declarations"/>), as the kernel admitted them. It names the bundle's constants and the unit's
/// callees' without including them, so it checks only in an environment that already holds the bundle and the callees.
/// </summary>
public static class Certificates
{
    /// <summary>Writes a unit's declarations as lean4export NDJSON, in the order given.</summary>
    /// <param name="stream">The output; left open.</param>
    /// <param name="environment">The environment the declarations were admitted into (a run's <see cref="EngineResult.Environment"/>).</param>
    /// <param name="declarations">The unit's admitted declarations, in admission order.</param>
    /// <param name="metadata">The bundle's metadata, whose Lean version the file carries over; null if unknown.</param>
    /// <exception cref="KernelException">A declaration is not in <paramref name="environment"/>.</exception>
    public static void Write(Stream stream, KernelEnvironment environment, IEnumerable<KernelDeclaration> declarations, ExportMetadata? metadata = null)
    {
        ArgumentNullException.ThrowIfNull(stream);
        ArgumentNullException.ThrowIfNull(environment);
        ArgumentNullException.ThrowIfNull(declarations);
        using var writer = new Lean4ExportWriter(stream, metadata, leaveOpen: true);
        foreach (var declaration in declarations)
        {
            writer.Write(AdmittedDeclarations.Of(environment, declaration));
        }
        writer.Flush();
    }

    /// <summary>
    /// Reads a certificate's declarations, in file order. Nothing is checked here: the declarations are for an
    /// environment holding the bundle and the unit's callees, where <see cref="ExportChecker"/> admits them or a recheck
    /// takes only their proof values (KTD16).
    /// </summary>
    /// <param name="stream">The NDJSON; left open.</param>
    /// <returns>The declarations.</returns>
    /// <exception cref="Lean4ExportFormatException">The certificate is malformed.</exception>
    public static ImmutableArray<Declaration> Read(Stream stream)
    {
        ArgumentNullException.ThrowIfNull(stream);
        using var reader = new Lean4ExportReader(stream, leaveOpen: true);
        return [.. reader.ReadDeclarations()];
    }
}
