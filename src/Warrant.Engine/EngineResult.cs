using System.Collections.Immutable;
using Warrant.Kernel;
using Warrant.Lean4Export;

namespace Warrant.Engine;

/// <summary>What one engine run produced.</summary>
public sealed class EngineResult
{
    internal EngineResult(SemanticsBundle bundle, KernelEnvironment environment, ImmutableArray<UnitOutcome> units, ImmutableArray<KernelDeclaration> admitted)
    {
        Bundle = bundle;
        Environment = environment;
        Units = units;
        Admitted = admitted;
    }

    /// <summary>The bundle the run admitted into a fork of.</summary>
    public SemanticsBundle Bundle { get; }

    /// <summary>
    /// The run's fork of the bundle, holding every admitted declaration: the fork its last level of theorems was admitted
    /// into (M5b KTD8), frozen.
    /// </summary>
    public KernelEnvironment Environment { get; }

    /// <summary>One outcome per unit, in the order the units were given.</summary>
    public ImmutableArray<UnitOutcome> Units { get; }

    /// <summary>
    /// Every declaration the kernel admitted, in admission order: the translated definitions and types in dependency order,
    /// then each level's proved theorems in input order (M5b KTD8).
    /// </summary>
    public ImmutableArray<KernelDeclaration> Admitted { get; }

    /// <summary>Finds a unit's outcome by key.</summary>
    /// <param name="key">The documentation-comment ID.</param>
    /// <returns>The outcome, or null if no such unit was given.</returns>
    public UnitOutcome? Find(string key) => Units.FirstOrDefault(u => string.Equals(u.Key, key, StringComparison.Ordinal));

    /// <summary>
    /// Writes lean4export NDJSON (docs/m4/07): the bundle's declarations in file order, then every admitted declaration in
    /// admission order, as the kernel admitted it. The file loads into an empty environment.
    /// </summary>
    /// <param name="stream">The output; left open.</param>
    public void WriteNdjson(Stream stream)
    {
        ArgumentNullException.ThrowIfNull(stream);
        using var writer = new Lean4ExportWriter(stream, Bundle.Metadata, leaveOpen: true);
        writer.WriteAll(Bundle.Declarations);
        foreach (var declaration in Admitted)
        {
            writer.Write(AdmittedDeclarations.Of(Environment, declaration));
        }
        writer.Flush();
    }
}
