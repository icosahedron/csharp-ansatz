using System.Text;
using Warrant.Engine.Service.Cache;
using Warrant.Kernel;
using Warrant.Semantics;
using Warrant.Vir;

namespace Warrant.Engine.Service;

/// <summary>The SHA-256 of the files a service's bundle and sidecar were loaded from (M5b KTD13).</summary>
/// <param name="Bundle">The semantics bundle file's SHA-256, as 64 lowercase hex digits.</param>
/// <param name="Sidecar">The attribute sidecar file's SHA-256, as 64 lowercase hex digits.</param>
public sealed record BundleHashes(string Bundle, string Sidecar);

public sealed partial class VerificationService
{
    /// <summary>Test only: told about each unit that ran, before the service decides whether to store it.</summary>
    internal Action<UnitOutcome>? UnitFinished { get; set; }

    /// <summary>
    /// One request's use of the result cache (KTD13, KTD14): it keys every unit, claims each key so the service computes it
    /// at most once at a time, reads the entries, and stores each cacheable outcome as soon as its unit finishes. Disposing
    /// it releases every claim still held.
    /// </summary>
    /// <remarks>
    /// The run admits a hit that a miss depends on from the hit's certificate (KTD15), so a miss never runs its hits again.
    /// Under recheck every entry is read from disk (KTD16).
    /// </remarks>
    private sealed class CacheSession : IDisposable
    {
        private readonly VerificationService _service;
        private readonly string _directory;
        private readonly CancellationToken _cancellationToken;
        private readonly bool _recheck;
        private readonly Dictionary<string, EngineUnit> _units = new(StringComparer.Ordinal);
        private readonly Dictionary<string, (CacheKeyInputs Inputs, string Key, VerifyBudgets Budgets)> _keys = new(StringComparer.Ordinal);
        private readonly Dictionary<string, string> _claimed = new(StringComparer.Ordinal);
        private readonly Lock _lock = new();

        public CacheSession(VerificationService service, string directory, IReadOnlyList<EngineUnit> inputs, EngineOptions options, bool recheck)
        {
            var hashes = service.Hashes ?? throw new InvalidOperationException(
                "The request has a cache directory, but the service was not told the SHA-256 of its bundle and sidecar files.");
            _service = service;
            _directory = Path.GetFullPath(directory);
            _cancellationToken = options.CancellationToken;
            _recheck = recheck;
            foreach (var unit in inputs)
            {
                _units.TryAdd(unit.Unit.Key, unit);
            }
            foreach (var (unitKey, keyInputs) in CacheKeyInputs.ForUnits(inputs, hashes.Bundle, hashes.Sidecar))
            {
                var unit = _units[unitKey].Unit;
                var budgets = Pipeline.Effective(options, unit.Kind == VirUnitKind.Theorem ? unit.Budget : null);
                _keys.Add(unitKey, (keyInputs, keyInputs.Key(Toolchain.Identity), budgets));
            }
            try
            {
                Hits = Lookup();
            }
            catch
            {
                // A claim left held would make every later request for its key wait forever.
                Dispose();
                throw;
            }
        }

        /// <summary>The outcomes the run reports from the cache, by unit key.</summary>
        public IReadOnlyDictionary<string, UnitOutcome> Hits { get; }

        /// <summary>
        /// Stores a finished unit's outcome when it is cacheable and was computed undisturbed: not after the request was
        /// cancelled and not after the unit's deadline passed (KTD14); then releases its key. A unit that ran although it
        /// hit, because the kernel rejected a cached proof it was admitted with (KTD15), replaces its entry.
        /// </summary>
        public void Finished(Pipeline.UnitFinish finish)
        {
            var unitKey = finish.Outcome.Key;
            if (!_keys.ContainsKey(unitKey))
            {
                return;
            }
            try
            {
                _service.UnitFinished?.Invoke(finish.Outcome);
                if (!_cancellationToken.IsCancellationRequested && !finish.DeadlinePassed && Entry(finish) is { } entry)
                {
                    _service.Cache.Write(_directory, entry);
                }
            }
            finally
            {
                Release(unitKey);
            }
        }

        /// <summary>Removes a unit's entry, whose certificate the kernel rejected (KTD16).</summary>
        public void Delete(string unitKey) => _service.Cache.Delete(_directory, _keys[unitKey].Key);

        public void Dispose()
        {
            List<string> held;
            lock (_lock)
            {
                held = [.. _claimed.Keys];
            }
            foreach (var unitKey in held)
            {
                Release(unitKey);
            }
        }

        /// <summary>
        /// Claims and reads every key in key order, so two requests waiting for each other's keys cannot deadlock; under
        /// recheck every entry is read from disk.
        /// </summary>
        private Dictionary<string, UnitOutcome> Lookup()
        {
            var found = new Dictionary<string, UnitOutcome>(StringComparer.Ordinal);
            foreach (var (unitKey, (_, key, budgets)) in _keys.OrderBy(p => p.Value.Key, StringComparer.Ordinal))
            {
                if (!Claim(unitKey, key))
                {
                    // Cancelled while another request computed the key: the run cancels what is left.
                    break;
                }
                if (_service.Cache.Read(_directory, key, fromDisk: _recheck) is { } cached)
                {
                    if (!string.Equals(cached.Outcome.Key, unitKey, StringComparison.Ordinal))
                    {
                        _service.Cache.Delete(_directory, key);
                    }
                    else if (cached.Entry.Admits(budgets))
                    {
                        found.Add(unitKey, cached.Outcome);
                        Release(unitKey);
                    }
                }
            }
            return found;
        }

        /// <summary>Waits until no other request of the service is computing a key, then claims it; false if cancelled while waiting.</summary>
        private bool Claim(string unitKey, string key)
        {
            var id = (_directory, key);
            while (true)
            {
                TaskCompletionSource? other;
                lock (_service._computingLock)
                {
                    if (!_service._computing.TryGetValue(id, out other))
                    {
                        _service._computing.Add(id, new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously));
                        lock (_lock)
                        {
                            _claimed.Add(unitKey, key);
                        }
                        return true;
                    }
                }
                try
                {
                    other.Task.Wait(_cancellationToken);
                }
                catch (OperationCanceledException)
                {
                    return false;
                }
            }
        }

        private void Release(string unitKey)
        {
            string? key;
            lock (_lock)
            {
                if (!_claimed.Remove(unitKey, out key))
                {
                    return;
                }
            }
            TaskCompletionSource? done;
            lock (_service._computingLock)
            {
                _service._computing.Remove((_directory, key), out done);
            }
            done?.SetResult();
        }

        /// <summary>
        /// The entry for a finished unit, or null when its outcome is not cached: only theorems, recursive definitions and
        /// definitions with a contract obligation (M6 U10) are, and of their outcomes only proofs, false claims, unproved
        /// ones and fuel exhaustion (KTD14).
        /// </summary>
        /// <summary>
        /// Whether a definition's outcome came from a proof search of its contract obligation: its proof admitted with
        /// it, or the obligation not proved or undecided.
        /// </summary>
        private static bool HasObligation(UnitOutcome outcome) =>
            outcome.UnitKind == VirUnitKind.Function
            && (outcome is NotProvedOutcome or UndecidedOutcome || outcome.Declarations.Any(d => d is TheoremDecl));

        private CacheEntry? Entry(Pipeline.UnitFinish finish)
        {
            var outcome = finish.Outcome;
            var unit = _units[outcome.Key].Unit;
            if (unit.Kind != VirUnitKind.Theorem && !Translator.IsRecursive(unit) && !HasObligation(outcome))
            {
                return null;
            }
            var (inputs, key, budgets) = _keys[outcome.Key];
            (BudgetMatch Match, VerifyBudgets Budgets)? stored = outcome switch
            {
                ProvedOutcome or TranslatedOutcome when finish.BudgetExact => (BudgetMatch.Exact, budgets),
                // A proof holds under any budgets at least those it needed: the kernel's it ran with, the tactic fuel it
                // used and the time it took (KTD13).
                ProvedOutcome or TranslatedOutcome => (BudgetMatch.AtLeast, budgets with { TacticFuel = finish.TacticFuelUsed, Timeout = finish.Elapsed }),
                FalseOutcome or NotProvedOutcome => (BudgetMatch.Exact, budgets),
                UndecidedOutcome { Exhausted: ExhaustedBudget.KernelFuel or ExhaustedBudget.TacticFuel } => (BudgetMatch.Exact, budgets),
                _ => null,
            };
            if (stored is not { } how)
            {
                return null;
            }
            var certificate = "";
            if (outcome.Declarations.Length > 0)
            {
                using var stream = new MemoryStream();
                Certificates.Write(stream, finish.Environment, outcome.Declarations, _service.Bundle.Metadata);
                certificate = Encoding.UTF8.GetString(stream.ToArray());
            }
            return new CacheEntry(CacheEntry.FormatVersion, Toolchain.Identity, key, inputs, how.Match, how.Budgets, OutcomeDto.From(outcome), certificate);
        }
    }
}
