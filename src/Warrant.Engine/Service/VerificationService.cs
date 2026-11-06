using System.Collections.Immutable;
using System.Diagnostics;
using Warrant.Engine.Reports;
using Warrant.Engine.Service.Cache;
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
/// A request with a cache directory reads and writes the result cache (KTD13, KTD14; docs/m5b/04), and the service runs
/// at most one computation of a key at a time.
/// </remarks>
public sealed partial class VerificationService : IDisposable
{
    /// <summary>The protocol version of <see cref="VerifyRequest"/> and <see cref="VerifyResponse"/>.</summary>
    public const int ProtocolVersion = 1;

    private readonly WorkerPool _pool;
    private readonly Dictionary<(string Directory, string Key), TaskCompletionSource> _computing = [];
    private readonly Lock _computingLock = new();
    private int _hits;
    private int _misses;
    private int _tacticRuns;
    private int _rechecked;

    /// <summary>
    /// Loads the sidecar, which names the bundle it was made for, so a mismatched pair is refused before the slow load, then
    /// the bundle, checking every declaration with the kernel as <see cref="SemanticsBundle.Load"/> does.
    /// </summary>
    /// <param name="bundlePath">The semantics bundle file.</param>
    /// <param name="sidecarPath">The attribute sidecar file made for that bundle.</param>
    /// <param name="workers">The number of workers; <see cref="WorkerPool.DefaultSize"/> when 0.</param>
    /// <param name="cache">The result cache; a <see cref="FileResultCache"/> of its own when null.</param>
    /// <exception cref="SidecarFormatException">The sidecar is malformed or was made for another bundle.</exception>
    /// <exception cref="InvalidDataException">The kernel rejects a declaration of the bundle.</exception>
    public VerificationService(string bundlePath, string sidecarPath, int workers = 0, IResultCache? cache = null)
        : this(LoadSidecarFirst(bundlePath, sidecarPath, out var sidecar, out var hashes), sidecar, workers, hashes, cache)
    {
    }

    /// <summary>Serves requests over a bundle and a sidecar already loaded.</summary>
    /// <param name="bundle">The checked, frozen bundle.</param>
    /// <param name="sidecar">The frozen attribute sidecar made for it.</param>
    /// <param name="workers">The number of workers; <see cref="WorkerPool.DefaultSize"/> when 0.</param>
    /// <param name="hashes">
    /// The SHA-256 of the files the bundle and the sidecar were loaded from, which every cache key covers (KTD13); null
    /// when unknown, and then a request with a cache directory is refused.
    /// </param>
    /// <param name="cache">The result cache; a <see cref="FileResultCache"/> of its own when null.</param>
    /// <exception cref="ArgumentException">The sidecar is not frozen.</exception>
    public VerificationService(SemanticsBundle bundle, Sidecar sidecar, int workers = 0, BundleHashes? hashes = null, IResultCache? cache = null)
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
        Hashes = hashes;
        Cache = cache ?? new FileResultCache();
    }

    /// <summary>The SHA-256 of the bundle's and the sidecar's files; null when the service was not told them.</summary>
    public BundleHashes? Hashes { get; }

    /// <summary>The result cache requests with a cache directory read and write.</summary>
    public IResultCache Cache { get; }

    /// <summary>The counters of every request this service has answered, for <c>status</c> (KTD26).</summary>
    public VerifyCounters Totals => new(Volatile.Read(ref _hits), Volatile.Read(ref _misses), Volatile.Read(ref _tacticRuns), Volatile.Read(ref _rechecked));

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
    /// <exception cref="InvalidOperationException">The request has a cache directory and the service was not given <see cref="Hashes"/>.</exception>
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
        Pipeline.PipelineRun run;
        using (var session = request.CacheDirectory is { } directory ? new CacheSession(this, directory, inputs, options, request.Recheck) : null)
        {
            var hits = session?.Hits ?? new Dictionary<string, UnitOutcome>(StringComparer.Ordinal);
            run = Pipeline.Execute(
                inputs, decided, [.. request.Units.Select(u => u.Key)], Bundle, options, _pool, hits, session is null ? null : session.Finished, request.Recheck);
            // KTD16: an entry whose certificate the kernel rejected is removed.
            foreach (var unitKey in run.Rejected)
            {
                session?.Delete(unitKey);
            }
        }
        // A cached unit whose translation now fails reports that, not its entry.
        ImmutableArray<UnitResult> units =
        [
            .. run.Result.Units.Select(o => new UnitResult(
                OutcomeDto.From(o), run.FromCache.Contains(o.Key), run.Rechecked.Contains(o.Key), run.Elapsed.GetValueOrDefault(o.Key))),
        ];
        var counters = new VerifyCounters(units.Count(u => u.FromCache), units.Count(u => !u.FromCache), run.SearchRuns, units.Count(u => u.Rechecked));
        Interlocked.Add(ref _hits, counters.Hits);
        Interlocked.Add(ref _misses, counters.Misses);
        Interlocked.Add(ref _tacticRuns, counters.TacticRuns);
        Interlocked.Add(ref _rechecked, counters.Rechecked);
        var response = new VerifyResponse(ProtocolVersion, request.RequestId, units, counters, stopwatch.Elapsed);
        return new ServiceRun(response, run.Result);
    }

    /// <summary>Stops the workers once the work they hold is done.</summary>
    public void Dispose() => _pool.Dispose();

    private static SemanticsBundle LoadSidecarFirst(string bundlePath, string sidecarPath, out Sidecar sidecar, out BundleHashes hashes)
    {
        ArgumentNullException.ThrowIfNull(bundlePath);
        ArgumentNullException.ThrowIfNull(sidecarPath);
        var bundleSha256 = OutcomeText.FileSha256(bundlePath);
        sidecar = Sidecar.Load(sidecarPath, bundleSha256);
        hashes = new BundleHashes(bundleSha256, OutcomeText.FileSha256(sidecarPath));
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
