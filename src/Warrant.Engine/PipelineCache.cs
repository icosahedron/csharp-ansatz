using System.Collections.Immutable;
using System.Diagnostics;
using Warrant.Cic;
using Warrant.Kernel;
using Warrant.Semantics;
using Warrant.Vir;

namespace Warrant.Engine;

public static partial class Pipeline
{
    /// <summary>
    /// The outcome of a unit whose cached certificate the kernel rejected under recheck (M5b KTD16): WRT0010 naming the
    /// unit. The unit is not proved again in that run.
    /// </summary>
    /// <param name="key">The unit's key.</param>
    /// <param name="kind">What the unit is.</param>
    /// <param name="display">The unit's display name.</param>
    /// <param name="assumptions">The unit's assumptions.</param>
    /// <param name="reason">The kernel's message.</param>
    /// <returns>The outcome.</returns>
    internal static FailedOutcome CertificateRejected(string key, VirUnitKind kind, string display, ImmutableArray<UnitAssumption> assumptions, string reason) =>
        new(key, kind, display, assumptions, $"cached certificate for '{display}' was rejected by the kernel: {reason}") { Code = InternalErrorOutcome.Code };

    /// <summary>Where a theorem's outcome came from.</summary>
    private enum Source
    {
        /// <summary>The theorem ran.</summary>
        Ran,

        /// <summary>
        /// Its cached proof was admitted, checked by the kernel, because a unit that runs names it (KTD15) or under recheck
        /// (KTD16).
        /// </summary>
        Cache,

        /// <summary>Its cached proof was rejected under recheck (KTD16).</summary>
        Rejected,
    }

    /// <summary>A unit that ran, as it finished (M5b KTD14): what the result cache needs to store it.</summary>
    /// <param name="Outcome">The unit's outcome.</param>
    /// <param name="Environment">The environment its declarations were admitted into, which its certificate is written from.</param>
    /// <param name="TacticFuelUsed">The most tactic fuel one proof search of the unit used, if it succeeded; 0 when none ran.</param>
    /// <param name="BudgetExact">
    /// Whether the outcome depends on the exact budgets even though it is a proof: a fixed proof was tried and ran out
    /// of a kernel resource before the one that was accepted, so more fuel could have accepted the first.
    /// </param>
    /// <param name="Elapsed">The time from the unit's start to its outcome.</param>
    /// <param name="DeadlinePassed">Whether the unit's wall-clock deadline had passed when it finished.</param>
    internal sealed record UnitFinish(
        UnitOutcome Outcome, KernelEnvironment Environment, long TacticFuelUsed, bool BudgetExact, TimeSpan Elapsed, bool DeadlinePassed);

    private sealed partial class TheoremBudget
    {
        /// <summary>
        /// Whether running out while the kernel checks a cached proof ends the unit as undecided (KTD15, KTD16): under
        /// recheck, when the deadline passed, or when the run is cancelled; otherwise the proof is built again.
        /// </summary>
        public bool StopsCachedCheck(bool recheck, Exception ex, CancellationToken token) =>
            recheck || Which(ex) == ExhaustedBudget.Time || token.IsCancellationRequested;
    }

    private sealed partial class RunState
    {
        /// <summary>
        /// The outcomes the result cache holds, by key (KTD15): translated, and admitted from their certificates only when
        /// a unit that runs depends on them, or under recheck.
        /// </summary>
        public required IReadOnlyDictionary<string, UnitOutcome> Cached { get; init; }

        /// <summary>Told about each unit that ran as soon as it has its outcome.</summary>
        public required Action<UnitFinish>? Finished { get; init; }

        /// <summary>Whether every cached proof is checked again (KTD16).</summary>
        public required bool Recheck { get; init; }

        /// <summary>The units whose outcome is their cached one.</summary>
        public HashSet<string> FromCache { get; } = new(StringComparer.Ordinal);

        /// <summary>The units whose cached certificate the kernel checked again under recheck.</summary>
        public HashSet<string> Rechecked { get; } = new(StringComparer.Ordinal);

        /// <summary>
        /// The units whose entries are to be removed: their cached certificate the kernel rejected under recheck, or their
        /// proof it rejected when admitting it again.
        /// </summary>
        public HashSet<string> Rejected { get; } = new(StringComparer.Ordinal);

        /// <summary>The cached units reported as they are, with nothing admitted: no unit that runs depends on them.</summary>
        private readonly HashSet<string> _unadmitted = new(StringComparer.Ordinal);

        /// <summary>The units some unit that runs depends on, transitively (KTD15).</summary>
        private HashSet<string> _needed = new(StringComparer.Ordinal);

        /// <summary>
        /// The units some translated unit that has no cached outcome depends on, transitively (KTD15): the cached ones among
        /// them are admitted from their certificates so that unit can run.
        /// </summary>
        private HashSet<string> NeededBy(Translation translation)
        {
            var needed = new HashSet<string>(StringComparer.Ordinal);
            foreach (var unit in translation.Units.Where(u => !Cached.ContainsKey(u.Key)))
            {
                needed.UnionWith(Closure(units[unit.Key]));
            }
            return needed;
        }

        /// <summary>
        /// Whether a cached unit with a proof is admitted from its certificate (KTD15, KTD16): under recheck always, else
        /// when a unit that runs depends on it.
        /// </summary>
        private bool Admits(string key) => Recheck || _needed.Contains(key);

        /// <summary>
        /// A cached recursive definition, or a function with a contract obligation (M6 U10), translated afresh and admitted
        /// with the decrease proofs and equation lemma, or the contract's proofs, of its certificate, each checked by the
        /// kernel (KTD15, KTD16). One the kernel rejects is proved again, or under recheck fails the unit; a unit that ran
        /// is stored again.
        /// </summary>
        private void AdmitFromCertificate(TranslatedUnit unit, UnitOutcome hit)
        {
            var stopwatch = Stopwatch.StartNew();
            var engineUnit = units[unit.Key];
            Scope? scope = null;
            var proofs = hit.Declarations.OfType<TheoremDecl>().ToDictionary(d => d.Value.Name, d => d.Value.Proof);
            var outcome = Cancelled(engineUnit) ?? Skip(engineUnit) ?? (scope = new Scope(this, Env, Attributes) { CachedProofs = proofs }).Admit(unit);
            if (scope is { FellBack: false } && outcome is TranslatedOutcome translated)
            {
                // The assumptions the default procedure found (M6 U11, KTD20) come from its walk, which a cached proof skips.
                var found = hit.Assumptions.Where(a => a.Assumption.Kind is VirAssumptionKind.MayThrow or VirAssumptionKind.CalleeContract && !translated.Assumptions.Contains(a));
                outcome = translated with { Assumptions = [.. translated.Assumptions, .. found] };
            }
            outcome = SettleCancel(engineUnit, outcome);
            Outcomes.Add(unit.Key, outcome);
            Elapsed.Add(unit.Key, stopwatch.Elapsed);
            if (scope is null)
            {
                return;
            }
            if (scope.Rejected)
            {
                Rejected.Add(unit.Key);
            }
            else if (!scope.FellBack && outcome is TranslatedOutcome)
            {
                MarkReused(unit.Key);
            }
            else
            {
                Finish(scope, outcome, stopwatch.Elapsed);
            }
        }

        /// <summary>A cached unit reported as it is, with nothing admitted: no unit that runs depends on it.</summary>
        private void UseCached(string key, UnitOutcome hit)
        {
            Outcomes.Add(key, hit);
            Elapsed.Add(key, TimeSpan.Zero);
            FromCache.Add(key);
            _unadmitted.Add(key);
        }

        /// <summary>A cached unit admitted from its certificate, checked by the kernel; under recheck, checked again (KTD16).</summary>
        private void MarkReused(string key)
        {
            FromCache.Add(key);
            if (Recheck)
            {
                Rechecked.Add(key);
            }
        }

        private static (UnitOutcome, TimeSpan, Source) Ran((UnitOutcome Outcome, TimeSpan Elapsed) result) => (result.Outcome, result.Elapsed, Source.Ran);

        /// <summary>
        /// A cached proved theorem that a unit that runs names, or any under recheck (KTD15, KTD16): its cached proof term,
        /// as the proof of the theorem translated from the current unit, admitted by the kernel into its own fork of the
        /// level's environment, and the admitted constant checked to be that theorem. A proof the kernel rejects is
        /// WRT0010 under recheck, and otherwise the theorem runs as if it had no entry.
        /// </summary>
        private (UnitOutcome, TimeSpan, Source) Reuse(TranslatedUnit theorem, KernelEnvironment levelEnv, ProvedOutcome cached)
        {
            var stopwatch = Stopwatch.StartNew();
            var unit = units[theorem.Key];
            if (Cancelled(unit) is { } cancelled)
            {
                return (cancelled, stopwatch.Elapsed, Source.Ran);
            }
            var shell = theorem.Theorem!;
            var budget = new TheoremBudget(options, shell.Budget);
            var env = levelEnv.Fork();
            var declaration = shell.WithProof(cached.Certificate.Value.Proof);
            string reason;
            try
            {
                Kernel.Kernel.Add(env, declaration, budget.Kernel);
                if (ProofTerms.IsAdmittedAs(env, shell))
                {
                    return (cached with { Certificate = declaration }, stopwatch.Elapsed, Source.Cache);
                }
                reason = $"the kernel admitted {shell.Name} with a type other than its statement";
            }
            catch (KernelResourceException ex) when (budget.StopsCachedCheck(Recheck, ex, options.CancellationToken))
            {
                var undecided = budget.Undecided(
                    unit.Unit.Key, unit.Unit.Kind, theorem.DisplayName, Assumptions(unit), ex, "the kernel checked the cached proof");
                return (SettleCancel(unit, undecided), stopwatch.Elapsed, Source.Ran);
            }
            catch (KernelException ex)
            {
                reason = ex.Message;
            }
            return Recheck
                ? (CertificateRejected(unit.Unit.Key, unit.Unit.Kind, theorem.DisplayName, Assumptions(unit), reason), stopwatch.Elapsed, Source.Rejected)
                : Ran(Prove(theorem, levelEnv));
        }

        /// <summary>
        /// Records a cached unit as the owner of the constants it would have admitted (KTD33), so a script naming one
        /// without depending on it is WRT0004 whether or not the unit came from the cache.
        /// </summary>
        private void OwnCached(TranslatedUnit unit)
        {
            foreach (var declaration in unit.Declarations)
            {
                Own(unit.Key, declaration);
            }
            if (unit.Recursion is { } recursion)
            {
                foreach (var decrease in recursion.Decreases)
                {
                    _owners.TryAdd(decrease.Theorem.Name, unit.Key);
                }
                _owners.TryAdd(recursion.Equation.Name, unit.Key);
            }
            if (unit.Contract is { } contract)
            {
                foreach (var wd in contract.WellDefinedness)
                {
                    _owners.TryAdd(wd.Theorem.Name, unit.Key);
                }
                _owners.TryAdd(contract.Theorem.Name, unit.Key);
                if (contract.Spec is { } spec)
                {
                    _owners.TryAdd(spec.Name, unit.Key);
                }
            }
        }
    }

    private sealed partial class Scope
    {
        /// <summary>
        /// A cached recursive definition's proofs, by the name of the decrease theorem or equation lemma they prove (KTD15,
        /// KTD16); null to prove the definition's decrease obligations with tactics.
        /// </summary>
        public Dictionary<Name, Expr>? CachedProofs { get; init; }

        /// <summary>Whether a cached proof was missing or rejected, so the unit ran rather than being admitted from its certificate.</summary>
        public bool FellBack { get; private set; }

        /// <summary>Whether, under recheck, the kernel rejected a cached proof, which failed the unit (KTD16).</summary>
        public bool Rejected { get; private set; }

        /// <summary>
        /// One theorem of a cached recursive definition, a decrease theorem or the equation lemma (KTD15, KTD16): the
        /// translated statement with the proof from the definition's certificate, admitted by the kernel. A proof that is
        /// missing or that the kernel rejects fails the unit under recheck, and otherwise falls back to
        /// <paramref name="fallback"/>, which builds it as a run with no entry does. Null when it was admitted, else the
        /// unit's outcome.
        /// </summary>
        private UnitOutcome? AdmitCached(
            EngineUnit unit,
            TheoremShell shell,
            string display,
            ImmutableArray<UnitAssumption> assumptions,
            List<KernelDeclaration> admitted,
            TheoremBudget budget,
            Func<UnitOutcome?> fallback)
        {
            string reason;
            if (CachedProofs!.TryGetValue(shell.Name, out var proof))
            {
                try
                {
                    AddDeclaration(unit.Unit.Key, shell.WithProof(proof), admitted, budget);
                    return null;
                }
                catch (KernelResourceException ex) when (budget.StopsCachedCheck(run.Recheck, ex, options.CancellationToken))
                {
                    return budget.Undecided(unit.Unit.Key, unit.Unit.Kind, display, assumptions, ex, $"the kernel checked the cached proof of {shell.Name}");
                }
                catch (KernelException ex)
                {
                    reason = ex.Message;
                }
            }
            else
            {
                reason = $"it holds no proof of {shell.Name}";
            }
            if (run.Recheck)
            {
                Rejected = true;
                return CertificateRejected(unit.Unit.Key, unit.Unit.Kind, display, assumptions, reason);
            }
            FellBack = true;
            return fallback();
        }
    }
}
