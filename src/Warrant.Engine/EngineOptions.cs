using Warrant.Cic;
using Warrant.Kernel;
using Warrant.Meta;

namespace Warrant.Engine;

/// <summary>
/// How the engine runs (M5a R13, Key Decisions): the project's budgets for each theorem, which <c>[Theorem(...)]</c>
/// overrides per theorem, and the attribute sidecar the tactics consult.
/// </summary>
public sealed record EngineOptions
{
    /// <summary>
    /// The default tactic fuel: ten times the most any M5a corpus theorem uses, 17,197 steps for ZeroIsNeutral's intro and
    /// omega (measured in U18, docs/m5a/07, "Budgets"). Each unit that adds a tactic measures again.
    /// </summary>
    public const long DefaultTacticFuel = 171_970;

    /// <summary>The defaults for a build: 20M kernel steps, <see cref="DefaultTacticFuel"/>, 30 seconds per theorem.</summary>
    public static EngineOptions Default { get; } = new();

    /// <summary>The kernel's limits for every declaration; its fuel is a theorem's kernel fuel (default 20M steps).</summary>
    public KernelLimits Kernel { get; init; } = KernelLimits.Interactive;

    /// <summary>The fuel Meta and the tactics may use per theorem.</summary>
    public long TacticFuel { get; init; } = DefaultTacticFuel;

    /// <summary>The wall-clock limit per theorem, covering Meta and the kernel.</summary>
    public TimeSpan Timeout { get; init; } = TimeSpan.FromSeconds(30);

    /// <summary>
    /// Cancels the run (M5b KTD12): the kernel and Meta poll it, a unit it interrupts ends as <see cref="CancelledOutcome"/>,
    /// and no unit starts once it is cancelled. Units that finished before keep their outcomes.
    /// </summary>
    public CancellationToken CancellationToken { get; init; }

    /// <summary>The attribute sidecar (KTD9) the tactics read reducibility, instances and simp lemmas from.</summary>
    public Sidecar Attributes { get; init; } = Sidecar.Empty;

    /// <summary>
    /// Test only: replaces the term a script built before the kernel checks it, to show that a wrong term Warrant builds is
    /// reported as an internal error (WRT0010), never as a proof.
    /// </summary>
    internal Func<Expr, Expr>? TamperWithProof { get; init; }

    /// <summary>
    /// When set, each theorem with a proof script records its steps (M5b KTD24) and gives them here, with its key, once the
    /// script has run, from whichever worker ran it. For <c>warrant explain</c>; null records nothing.
    /// </summary>
    public Action<string, System.Collections.Immutable.ImmutableArray<TacticStep>>? TacticTrace { get; init; }
}
