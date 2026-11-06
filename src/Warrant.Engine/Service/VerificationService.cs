using System.Collections.Immutable;
using System.Diagnostics;
using Warrant.Engine.Reports;
using Warrant.Kernel;
using Warrant.Meta;
using Warrant.Semantics;
using Warrant.Vir;

namespace Warrant.Engine.Service;

/// <summary>
/// Verifies requests (M5b KTD1, KTD8, KTD10; docs/m5b/03): the one implementation behind the server and the CLI's
/// in-process path. It loads the semantics bundle, verified, and the attribute sidecar once, builds the default simp set
/// and omega's preparation set over the bundle once, and runs every request's theorems on one shared
/// <see cref="WorkerPool"/>.
/// </summary>
/// <remarks>
/// It never sees Roslyn: a request carries each unit's canonical VIR, and the response names positions by VIR node ID,
/// which the client renders through its own extraction. The service is safe to call from several threads at once.
/// </remarks>
public sealed class VerificationService : IDisposable
{
    /// <summary>The protocol version of <see cref="VerifyRequest"/> and <see cref="VerifyResponse"/>.</summary>
    public const int ProtocolVersion = 1;

    private readonly WorkerPool _pool;

    /// <summary>
    /// Loads the sidecar, which names the bundle it was made for, so a mismatched pair is refused before the slow load, then
    /// the bundle, checking every declaration with the kernel as <see cref="SemanticsBundle.Load"/> does.
    /// </summary>
    /// <param name="bundlePath">The semantics bundle file.</param>
    /// <param name="sidecarPath">The attribute sidecar file made for that bundle.</param>
    /// <param name="workers">The number of workers; <see cref="WorkerPool.DefaultSize"/> when 0.</param>
    /// <exception cref="SidecarFormatException">The sidecar is malformed or was made for another bundle.</exception>
    /// <exception cref="InvalidDataException">The kernel rejects a declaration of the bundle.</exception>
    public VerificationService(string bundlePath, string sidecarPath, int workers = 0)
        : this(LoadSidecarFirst(bundlePath, sidecarPath, out var sidecar), sidecar, workers)
    {
    }

    /// <summary>Serves requests over a bundle and a sidecar already loaded.</summary>
    /// <param name="bundle">The checked, frozen bundle.</param>
    /// <param name="sidecar">The frozen attribute sidecar made for it.</param>
    /// <param name="workers">The number of workers; <see cref="WorkerPool.DefaultSize"/> when 0.</param>
    /// <exception cref="ArgumentException">The sidecar is not frozen.</exception>
    public VerificationService(SemanticsBundle bundle, Sidecar sidecar, int workers = 0)
    {
        ArgumentNullException.ThrowIfNull(bundle);
        ArgumentNullException.ThrowIfNull(sidecar);
        if (!sidecar.IsFrozen)
        {
            throw new ArgumentException("The sidecar must be frozen.", nameof(sidecar));
        }
        ArgumentOutOfRangeException.ThrowIfNegative(workers);
        Bundle = bundle;
        Attributes = sidecar;
        // KTD10: over the frozen bundle, keyed on the base sidecar every run forks, so no theorem's fork reaches them.
        SimpSet = DefaultSimpSet.Theorems(bundle.Env, sidecar);
        OmegaPrep = OmegaPrepSet.Theorems(bundle.Env, sidecar);
        _pool = new WorkerPool(workers == 0 ? WorkerPool.DefaultSize : workers);
    }

    /// <summary>The checked, frozen semantics bundle.</summary>
    public SemanticsBundle Bundle { get; }

    /// <summary>The frozen attribute sidecar; every run admits into a fork of it.</summary>
    public Sidecar Attributes { get; }

    /// <summary>The default simp set, built once over the bundle (KTD10).</summary>
    public SimpTheorems SimpSet { get; }

    /// <summary>Omega's preparation set, built once over the bundle (KTD10).</summary>
    public SimpTheorems OmegaPrep { get; }

    /// <summary>The number of workers theorems run on.</summary>
    public int Workers => _pool.Size;

    /// <summary>Verifies a request.</summary>
    /// <param name="request">The request.</param>
    /// <param name="cancellationToken">Stops the request (KTD12): units that finished keep their outcomes, the rest are cancelled.</param>
    /// <returns>The response, with the units in the request's order.</returns>
    /// <exception cref="ArgumentException">The request's protocol version is not <see cref="ProtocolVersion"/>, or two units have the same key.</exception>
    public VerifyResponse Verify(VerifyRequest request, CancellationToken cancellationToken = default) => Run(request, cancellationToken).Response;

    /// <summary>
    /// Verifies a request and also returns the engine's result, whose environment holds every admitted declaration, for an
    /// in-process caller that writes NDJSON or an assumption report.
    /// </summary>
    /// <param name="request">The request.</param>
    /// <param name="cancellationToken">Stops the request (KTD12).</param>
    /// <returns>The response and the result.</returns>
    /// <exception cref="ArgumentException">The request's protocol version is not <see cref="ProtocolVersion"/>, or two units have the same key.</exception>
    public ServiceRun Run(VerifyRequest request, CancellationToken cancellationToken = default)
    {
        ArgumentNullException.ThrowIfNull(request);
        if (request.ProtocolVersion != ProtocolVersion)
        {
            throw new ArgumentException($"The request speaks protocol {request.ProtocolVersion}; this service speaks {ProtocolVersion}.", nameof(request));
        }
        var stopwatch = Stopwatch.StartNew();
        var inputs = new List<EngineUnit>();
        var decided = new List<UnitOutcome>();
        foreach (var unit in request.Units)
        {
            if (Read(unit, out var problem) is { } vir)
            {
                inputs.Add(new EngineUnit(vir, unit.DisplayName));
            }
            else
            {
                decided.Add(Unreadable(unit, problem));
            }
        }
        var budgets = request.Budgets;
        var options = EngineOptions.Default with
        {
            Kernel = new KernelLimits(budgets.KernelFuel, budgets.KernelMaxNatBytes),
            TacticFuel = budgets.TacticFuel,
            Timeout = budgets.Timeout,
            Attributes = Attributes,
            CancellationToken = cancellationToken,
        };
        var run = Pipeline.Execute(inputs, decided, [.. request.Units.Select(u => u.Key)], Bundle, options, _pool);
        ImmutableArray<UnitResult> units =
        [
            .. run.Result.Units.Select(o => new UnitResult(OutcomeDto.From(o), FromCache: false, Rechecked: false, run.Elapsed.GetValueOrDefault(o.Key))),
        ];
        var response = new VerifyResponse(
            ProtocolVersion, request.RequestId, units, new VerifyCounters(Hits: 0, Misses: units.Length, TacticRuns: run.SearchRuns), stopwatch.Elapsed);
        return new ServiceRun(response, run.Result);
    }

    /// <summary>Stops the workers once the work they hold is done.</summary>
    public void Dispose() => _pool.Dispose();

    private static SemanticsBundle LoadSidecarFirst(string bundlePath, string sidecarPath, out Sidecar sidecar)
    {
        ArgumentNullException.ThrowIfNull(bundlePath);
        ArgumentNullException.ThrowIfNull(sidecarPath);
        sidecar = Sidecar.Load(sidecarPath, OutcomeText.FileSha256(bundlePath));
        return SemanticsBundle.Load(bundlePath);
    }

    /// <summary>A request unit's VIR, or null with the problem when it is not a VIR unit with the key the request gives it.</summary>
    private static VirUnit? Read(RequestUnit unit, out string problem)
    {
        try
        {
            var vir = VirReader.Read(unit.Vir);
            problem = $"its VIR is for {vir.Key}";
            return string.Equals(vir.Key, unit.Key, StringComparison.Ordinal) ? vir : null;
        }
        catch (FormatException ex)
        {
            problem = ex.Message;
            return null;
        }
    }

    /// <summary>A unit whose VIR could not be read: Warrant's fault (WRT0010), since its own extraction wrote it.</summary>
    private static FailedOutcome Unreadable(RequestUnit unit, string problem) =>
        new(unit.Key, unit.Kind, unit.DisplayName ?? LeanNames.FallbackDisplay(unit.Key), [], $"the unit's VIR could not be read: {problem}");
}

/// <summary>What <see cref="VerificationService.Run"/> produced.</summary>
/// <param name="Response">The response.</param>
/// <param name="Result">The engine's result, for NDJSON export and the assumption report.</param>
public sealed record ServiceRun(VerifyResponse Response, EngineResult Result);
