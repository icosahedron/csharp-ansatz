using System.Collections.Immutable;
using System.Diagnostics;
using System.Globalization;
using Warrant.Cic;
using Warrant.Engine.Reports;
using Warrant.Engine.Service;
using Warrant.Kernel;
using Warrant.Meta;
using Warrant.Semantics;
using Warrant.Vir;

namespace Warrant.Engine;

/// <summary>
/// The engine's pipeline (docs/m4/07, "The engine"; docs/m5a/04, "The loop"; docs/m5b/03, "Stages and levels"):
/// translates VIR units, admits the definitions in dependency order into one fork of the bundle, then proves the theorems
/// level by level, each in its own fork, and classifies every unit's outcome independently of the others.
/// </summary>
public static partial class Pipeline
{
    /// <summary>Runs the engine over a set of units, with the default options except for the kernel's limits.</summary>
    /// <param name="units">
    /// The units, typically in extraction order. A unit whose dependency is missing, cannot be translated or is rejected by
    /// the kernel fails, and the units depending on it are skipped; the others proceed.
    /// </param>
    /// <param name="bundle">The checked, frozen semantics bundle.</param>
    /// <param name="limits">The fuel for every kernel call; <see cref="KernelLimits.Corpus"/> when null.</param>
    /// <returns>One outcome per unit, in input order, and the environment the run admitted into.</returns>
    /// <exception cref="ArgumentException">Two units have the same key.</exception>
    public static EngineResult Run(IEnumerable<EngineUnit> units, SemanticsBundle bundle, KernelLimits? limits = null) =>
        Run(units, bundle, EngineOptions.Default with { Kernel = limits ?? KernelLimits.Corpus });

    /// <summary>
    /// Runs the engine over a set of units on one thread: the theorems of a level one after another, in input order. The
    /// outcomes are those of a run on a <see cref="WorkerPool"/> (M5b R7).
    /// </summary>
    /// <param name="units">
    /// The units, typically in extraction order. A unit whose dependency is missing, cannot be translated or is rejected by
    /// the kernel fails, and the units depending on it are skipped; the others proceed.
    /// </param>
    /// <param name="bundle">The checked, frozen semantics bundle.</param>
    /// <param name="options">The budgets and the attribute sidecar.</param>
    /// <returns>One outcome per unit, in input order, and the environment the run admitted into.</returns>
    /// <exception cref="ArgumentException">Two units have the same key.</exception>
    public static EngineResult Run(IEnumerable<EngineUnit> units, SemanticsBundle bundle, EngineOptions options)
    {
        ArgumentNullException.ThrowIfNull(units);
        var inputs = units.ToList();
        return Execute(inputs, [], [.. inputs.Select(u => u.Unit.Key)], bundle, options, pool: null).Result;
    }

    /// <summary>
    /// The engine's stages (M5b KTD8): translates every unit, admits the units that are not theorems in dependency order on
    /// one large-stack thread, freezes the run's fork, then runs the theorems level by level, on <paramref name="pool"/>
    /// or, when it is null, one after another on that thread.
    /// </summary>
    /// <param name="inputs">The units to run.</param>
    /// <param name="decided">Outcomes decided before the run, such as a unit whose VIR could not be read; their dependents are skipped.</param>
    /// <param name="order">Every unit's key, of <paramref name="inputs"/> and <paramref name="decided"/>, in the order the result lists them.</param>
    /// <param name="bundle">The checked, frozen semantics bundle.</param>
    /// <param name="options">The budgets, the attribute sidecar and the cancellation token.</param>
    /// <param name="pool">The workers theorems run on; null to run them on the run's own thread.</param>
    /// <param name="cached">
    /// Outcomes the result cache already holds, by key (M5b KTD14, KTD15): those units are translated, so their names
    /// still collide and own their constants, and their outcomes are reported without running them. One that a unit that
    /// runs depends on is admitted first without tactics: a recursive definition translated afresh with the decrease
    /// proofs and equation lemma of its certificate, a proved theorem with its cached proof, each checked by the kernel.
    /// A cached proof the kernel rejects makes its unit run as if it had no entry.
    /// </param>
    /// <param name="finished">
    /// Called as soon as each unit that ran has its outcome, on the thread it ran on, before the next unit of that thread
    /// starts; not called for units that were cached, decided, skipped or cancelled before they started.
    /// </param>
    /// <param name="recheck">
    /// Whether every cached proof is checked again (M5b KTD16): each cached recursive definition and proved theorem is
    /// admitted from its certificate, checked by the kernel against the declarations translated from the current units;
    /// one the kernel rejects fails as <see cref="CertificateRejected"/> and does not run.
    /// </param>
    /// <returns>The result, with each unit's time, the number of units whose proof search ran, and which outcomes came from <paramref name="cached"/>.</returns>
    /// <exception cref="ArgumentException">Two units have the same key.</exception>
    internal static PipelineRun Execute(
        IReadOnlyList<EngineUnit> inputs,
        IReadOnlyList<UnitOutcome> decided,
        IReadOnlyList<string> order,
        SemanticsBundle bundle,
        EngineOptions options,
        WorkerPool? pool,
        IReadOnlyDictionary<string, UnitOutcome>? cached = null,
        Action<UnitFinish>? finished = null,
        bool recheck = false)
    {
        ArgumentNullException.ThrowIfNull(bundle);
        ArgumentNullException.ThrowIfNull(options);
        var byKey = new Dictionary<string, EngineUnit>(StringComparer.Ordinal);
        var decidedKeys = decided.Select(d => d.Key).ToHashSet(StringComparer.Ordinal);
        foreach (var input in inputs)
        {
            if (!byKey.TryAdd(input.Unit.Key, input) || decidedKeys.Contains(input.Unit.Key))
            {
                throw new ArgumentException($"The unit {input.Unit.Key} is given twice.", nameof(inputs));
            }
        }
        WarmSimpSets(bundle, options.Attributes);

        var run = new RunState(bundle, byKey, options, decided, pool)
        {
            Cached = cached ?? new Dictionary<string, UnitOutcome>(StringComparer.Ordinal),
            Finished = finished,
            Recheck = recheck,
        };
        KernelThread.Run(run.Execute);
        return new PipelineRun(
            new EngineResult(bundle, run.Env, [.. order.Select(k => run.Outcomes[k])], [.. run.Admitted]),
            run.Elapsed,
            run.SearchRuns)
        {
            FromCache = run.FromCache,
            Rechecked = run.Rechecked,
            Rejected = run.Rejected,
        };
    }

    /// <summary>Builds the shared simp sets over the frozen bundle alone, before any fork exists to leak into them (KTD10).</summary>
    private static void WarmSimpSets(SemanticsBundle bundle, Sidecar sidecar)
    {
        DefaultSimpSet.Theorems(bundle.Env, sidecar);
        OmegaPrepSet.Theorems(bundle.Env, sidecar);
    }

    /// <summary>The keys of every unit a unit depends on, transitively, through the given units.</summary>
    /// <param name="unit">The unit.</param>
    /// <param name="units">The units, by key; a dependency not among them is in the closure, and its own are not.</param>
    /// <returns>The keys.</returns>
    internal static HashSet<string> ClosureOf(EngineUnit unit, IReadOnlyDictionary<string, EngineUnit> units)
    {
        var seen = new HashSet<string>(StringComparer.Ordinal);
        var work = new Stack<string>(unit.Unit.Deps);
        while (work.Count > 0)
        {
            var key = work.Pop();
            if (seen.Add(key) && units.TryGetValue(key, out var dep))
            {
                foreach (var next in dep.Unit.Deps)
                {
                    work.Push(next);
                }
            }
        }
        return seen;
    }

    /// <summary>A unit's display name: the C# one, or the fallback derived from its key.</summary>
    /// <param name="unit">The unit.</param>
    /// <returns>The name.</returns>
    internal static string Display(EngineUnit unit) => RunState.Display(unit);

    /// <summary>What <see cref="Execute"/> produced.</summary>
    /// <param name="Result">The outcomes and the final environment.</param>
    /// <param name="Elapsed">Each unit's time from the moment it started to its outcome; absent for units decided before the run.</param>
    /// <param name="SearchRuns">The number of units whose proof search ran: theorems, and recursive definitions' decrease proofs.</param>
    internal sealed record PipelineRun(EngineResult Result, IReadOnlyDictionary<string, TimeSpan> Elapsed, int SearchRuns)
    {
        /// <summary>The units whose outcome is their cached one: reported as cached, or admitted from their certificate.</summary>
        public IReadOnlySet<string> FromCache { get; init; } = new HashSet<string>();

        /// <summary>The units among <see cref="FromCache"/> whose certificate the kernel checked again under recheck (KTD16).</summary>
        public IReadOnlySet<string> Rechecked { get; init; } = new HashSet<string>();

        /// <summary>
        /// The units whose entries are to be removed: their cached certificate the kernel rejected under recheck (KTD16), or
        /// their proof it rejected when admitting it again into the next level.
        /// </summary>
        public IReadOnlySet<string> Rejected { get; init; } = new HashSet<string>();
    }

    /// <summary>
    /// A unit's effective budgets (M5a R13, M5b KTD11): the project's, overridden by a theorem's <c>[Theorem(...)]</c>
    /// arguments where they are not zero. A definition has the project's budgets.
    /// </summary>
    /// <param name="options">The project's budgets.</param>
    /// <param name="overrides">A theorem's overrides; null for a definition.</param>
    /// <returns>The budgets the unit runs with.</returns>
    internal static VerifyBudgets Effective(EngineOptions options, VirBudget? overrides) => new(
        overrides is { KernelFuel: > 0 } ? overrides.KernelFuel : options.Kernel.Fuel,
        options.Kernel.MaxNatBytes,
        overrides is { TacticFuel: > 0 } ? overrides.TacticFuel : options.TacticFuel,
        overrides is { TimeoutSeconds: > 0 } ? TimeSpan.FromSeconds(overrides.TimeoutSeconds) : options.Timeout);

    /// <summary>
    /// One unit's budgets (M5a R13, M5b KTD11): the project's, overridden by a theorem's <c>[Theorem(...)]</c> arguments
    /// where they are not zero, with one deadline for Meta and the kernel, which starts when the unit does. A definition,
    /// with its decrease proofs and equation lemma, has the project's budgets and no overrides.
    /// </summary>
    private sealed partial class TheoremBudget
    {
        public TheoremBudget(EngineOptions options, VirBudget? overrides)
        {
            var effective = Effective(options, overrides);
            Timeout = effective.Timeout;
            var deadline = DateTimeOffset.UtcNow + Timeout;
            Kernel = options.Kernel with
            {
                Fuel = effective.KernelFuel,
                Deadline = deadline,
                CancellationToken = options.CancellationToken,
            };
            Meta = new MetaLimits(effective.TacticFuel)
            {
                Deadline = deadline,
                CancellationToken = options.CancellationToken,
            };
        }

        public TimeSpan Timeout { get; }

        public KernelLimits Kernel { get; }

        public MetaLimits Meta { get; }

        public bool DeadlinePassed => DateTimeOffset.UtcNow >= Kernel.Deadline;

        /// <summary>Which budget a resource exception exhausted, for WRT0006's message.</summary>
        public string Exhausted(Exception ex) => Which(ex) switch
        {
            ExhaustedBudget.Time => string.Create(CultureInfo.InvariantCulture, $"the time limit of {Timeout.TotalSeconds:0.###} s was reached"),
            ExhaustedBudget.TacticFuel => string.Create(CultureInfo.InvariantCulture, $"tactic fuel ran out ({Meta.Fuel:N0} steps)"),
            ExhaustedBudget.KernelFuel => string.Create(CultureInfo.InvariantCulture, $"kernel fuel ran out ({Kernel.Fuel:N0} steps)"),
            _ => $"the kernel ran out of resources: {Inner(ex).Message}",
        };

        /// <summary>Which budget a resource exception exhausted; null for another kernel resource, such as a numeral's size.</summary>
        public ExhaustedBudget? Which(Exception ex)
        {
            ex = Inner(ex);
            if (ex.Message.Contains("deadline", StringComparison.Ordinal) || DeadlinePassed)
            {
                return ExhaustedBudget.Time;
            }
            return ex switch
            {
                MetaResourceException => ExhaustedBudget.TacticFuel,
                KernelResourceException when ex.Message.StartsWith("kernel fuel", StringComparison.Ordinal) => ExhaustedBudget.KernelFuel,
                _ => null,
            };
        }

        /// <summary>
        /// WRT0006 for a unit that ran out of a budget: "<see cref="Exhausted"/> while <paramref name="activity"/>.", with
        /// the budget it exhausted.
        /// </summary>
        public UndecidedOutcome Undecided(
            string key, VirUnitKind kind, string display, ImmutableArray<UnitAssumption> assumptions, Exception ex, string activity) =>
            new(key, kind, display, assumptions, $"{Exhausted(ex)} while {activity}.") { Exhausted = Which(ex) };

        /// <summary>The kernel's exception when the kernel ran out inside Meta's Check (KTD12): its budget, not Meta's.</summary>
        private static Exception Inner(Exception ex) => ex is MetaResourceException { InnerException: KernelResourceException kernel } ? kernel : ex;
    }

    /// <summary>
    /// A run's shared state (KTD8, KTD10): the units, the outcomes and admitted declarations merged so far, and the run's
    /// fork of the bundle and the sidecar, which the definitions are admitted into and which is frozen before any theorem
    /// runs. Each theorem works in a <see cref="Scope"/> of its own; its outcome is merged when its level ends.
    /// </summary>
    private sealed partial class RunState(
        SemanticsBundle bundle, Dictionary<string, EngineUnit> units, EngineOptions options, IReadOnlyList<UnitOutcome> decided, WorkerPool? pool)
    {
        private readonly Dictionary<Name, string> _owners = [];
        private int _searchRuns;

        public SemanticsBundle Bundle => bundle;

        public Dictionary<string, EngineUnit> Units => units;

        public EngineOptions Options => options;

        public NotationNames Names { get; private set; } = new();

        /// <summary>The definitions of the run's type units, by key.</summary>
        public Dictionary<string, VirDefinition> Definitions { get; } =
            units.Values.Where(u => u.Unit.Definition is not null).ToDictionary(u => u.Unit.Key, u => u.Unit.Definition!, StringComparer.Ordinal);

        /// <summary>The environment holding every admitted declaration: the run's fork, then each level's fork of it.</summary>
        public KernelEnvironment Env { get; private set; } = bundle.Env.Fork();

        /// <summary>The attribute sidecar with this run's entries for the declarations it generates (KTD8, KTD9).</summary>
        public Sidecar Attributes { get; } = options.Attributes.Fork();

        public Dictionary<string, UnitOutcome> Outcomes { get; } = decided.ToDictionary(o => o.Key, StringComparer.Ordinal);

        public List<KernelDeclaration> Admitted { get; } = [];

        public Dictionary<string, TimeSpan> Elapsed { get; } = new(StringComparer.Ordinal);

        public int SearchRuns => _searchRuns;

        public void CountSearch() => Interlocked.Increment(ref _searchRuns);

        public void Execute()
        {
            var translation = Translate();
            Names = NamesOf(translation);
            if (Cached.Count > 0)
            {
                _needed = NeededBy(translation);
            }
            var theorems = new List<TranslatedUnit>();
            foreach (var unit in translation.Units)
            {
                if (unit.Theorem is not null)
                {
                    theorems.Add(unit);
                    continue;
                }
                if (Cached.TryGetValue(unit.Key, out var hit))
                {
                    // A hit is the outcome of a run that started: one a cold run cancels or skips is cancelled or skipped.
                    if (Early(units[unit.Key]) is { } early)
                    {
                        Outcomes.Add(unit.Key, early);
                        Elapsed.Add(unit.Key, TimeSpan.Zero);
                        continue;
                    }
                    if (hit is TranslatedOutcome && unit.Recursion is not null && Admits(unit.Key))
                    {
                        AdmitFromCertificate(unit, hit);
                        continue;
                    }
                    UseCached(unit.Key, hit);
                    OwnCached(unit);
                    continue;
                }
                var stopwatch = Stopwatch.StartNew();
                Scope? scope = null;
                var outcome = Cancelled(units[unit.Key]) ?? Skip(units[unit.Key]) ?? (scope = new Scope(this, Env, Attributes)).Admit(unit);
                outcome = SettleCancel(units[unit.Key], outcome);
                Outcomes.Add(unit.Key, outcome);
                Elapsed.Add(unit.Key, stopwatch.Elapsed);
                Finish(scope, outcome, stopwatch.Elapsed);
            }
            Env.Freeze();
            Attributes.Freeze();
            RecordOwners(translation);
            RunLevels(theorems);
        }

        /// <summary>
        /// The theorems, level by level (KTD8): a theorem's level is one more than the deepest theorem it names with
        /// <c>nameof</c>. Each runs in its own fork of the level's frozen environment; when the level ends, its proved
        /// theorems are admitted into a new fork, which is frozen and becomes the next level's base.
        /// </summary>
        private void RunLevels(List<TranslatedUnit> theorems)
        {
            var index = units.Keys.Select((k, i) => (k, i)).ToDictionary(p => p.k, p => p.i, StringComparer.Ordinal);
            var levels = LevelsOf(theorems);
            foreach (var level in theorems.GroupBy(t => levels[t.Key]).OrderBy(g => g.Key))
            {
                var ordered = level.OrderBy(t => index[t.Key]).ToList();
                var levelEnv = Env;
                var jobs = new List<(TranslatedUnit Unit, Func<(UnitOutcome, TimeSpan, Source)> Work)>();
                foreach (var theorem in ordered)
                {
                    var unit = units[theorem.Key];
                    // A hit is the outcome of a run that started: one a cold run cancels or skips is cancelled or skipped.
                    if (Early(unit) is { } early)
                    {
                        Outcomes.Add(theorem.Key, early);
                        Elapsed.Add(theorem.Key, TimeSpan.Zero);
                        continue;
                    }
                    var hit = Cached.GetValueOrDefault(theorem.Key);
                    if (hit is not null && theorem.Theorem!.Script is { } script && ConstOutsideDependencies(unit, script) is not null)
                    {
                        // KTD33: who owns a constant depends on units outside the key, so the theorem runs and is WRT0004.
                        hit = null;
                    }
                    if (hit is not null && !(hit is ProvedOutcome && Admits(theorem.Key)))
                    {
                        UseCached(theorem.Key, hit);
                        continue;
                    }
                    jobs.Add((theorem, hit is ProvedOutcome proved ? () => Reuse(theorem, levelEnv, proved) : () => Ran(Prove(theorem, levelEnv))));
                }
                (UnitOutcome, TimeSpan, Source)[] results = pool is null
                    ? [.. jobs.Select(j => j.Work())]
                    : pool.RunAll(jobs.Select(j => j.Work));
                for (int i = 0; i < jobs.Count; i++)
                {
                    var (outcome, elapsed, source) = results[i];
                    var key = jobs[i].Unit.Key;
                    Outcomes.Add(key, outcome);
                    Elapsed.Add(key, elapsed);
                    switch (source)
                    {
                        case Source.Cache:
                            MarkReused(key);
                            break;
                        case Source.Rejected:
                            Rejected.Add(key);
                            break;
                    }
                }
                AdmitProved(ordered);
            }
        }

        /// <summary>One theorem in its own fork of the level's environment and the run's sidecar; the deadline starts here.</summary>
        private (UnitOutcome, TimeSpan) Prove(TranslatedUnit theorem, KernelEnvironment levelEnv)
        {
            var stopwatch = Stopwatch.StartNew();
            var unit = units[theorem.Key];
            UnitOutcome outcome;
            Scope? scope = null;
            try
            {
                outcome = Cancelled(unit) ?? (scope = new Scope(this, levelEnv.Fork(), Attributes.Fork())).Admit(theorem);
            }
            catch (OperationCanceledException)
            {
                // KTD32: a cancel during the counterexample search ends the unit as cancelled, not as a failure.
                outcome = Cancelled(unit) ?? throw new InvalidOperationException("A unit was cancelled although the run was not.");
            }
            outcome = SettleCancel(unit, outcome);
            var elapsed = stopwatch.Elapsed;
            Finish(scope, outcome, elapsed);
            return (outcome, elapsed);
        }

        /// <summary>Tells <see cref="Finished"/> about a unit that ran in <paramref name="scope"/>; nothing for one that did not run.</summary>
        private void Finish(Scope? scope, UnitOutcome outcome, TimeSpan elapsed)
        {
            if (scope is not null && Finished is { } finished)
            {
                finished(new UnitFinish(outcome, scope.Environment, scope.TacticFuelUsed, scope.BudgetExact, elapsed, scope.DeadlinePassed));
            }
        }

        /// <summary>
        /// Admits a level's proved theorems, in input order, into a new fork of the run's environment and freezes it, so
        /// the next level's theorems can use them. The kernel checks each proof again, as it does every term admitted
        /// into an environment; one it now rejects is Warrant's bug, and the theorem's users are skipped. A cached theorem
        /// reported as it is, is not admitted: no unit that runs depends on it.
        /// </summary>
        private void AdmitProved(List<TranslatedUnit> level)
        {
            var proved = level.Where(t => Outcomes[t.Key] is ProvedOutcome && !_unadmitted.Contains(t.Key)).ToList();
            if (proved.Count == 0)
            {
                return;
            }
            var next = Env.Fork();
            foreach (var theorem in proved)
            {
                var outcome = (ProvedOutcome)Outcomes[theorem.Key];
                var limits = new TheoremBudget(options, theorem.Theorem!.Budget).Kernel with { Deadline = null, CancellationToken = default };
                try
                {
                    Kernel.Kernel.Add(next, outcome.Certificate, limits);
                    Admitted.Add(outcome.Certificate);
                }
                catch (KernelException ex)
                {
                    FromCache.Remove(theorem.Key);
                    Rechecked.Remove(theorem.Key);
                    // The entry stored when the theorem finished, or the one its proof came from, holds a proof the kernel now rejects.
                    Rejected.Add(theorem.Key);
                    Outcomes[theorem.Key] = new InternalErrorOutcome(
                        outcome.Key, outcome.UnitKind, outcome.DisplayName, outcome.Assumptions, $"the kernel rejected the proof it had accepted when admitting it again: {ex.Message}");
                }
            }
            next.Freeze();
            Env = next;
        }

        /// <summary>Each theorem's level: 1, or one more than the deepest translated theorem among its dependencies.</summary>
        private Dictionary<string, int> LevelsOf(List<TranslatedUnit> theorems)
        {
            var keys = theorems.Select(t => t.Key).ToHashSet(StringComparer.Ordinal);
            var levels = new Dictionary<string, int>(StringComparer.Ordinal);
            var visiting = new HashSet<string>(StringComparer.Ordinal);

            int Level(string key)
            {
                if (levels.TryGetValue(key, out var known))
                {
                    return known;
                }
                if (!visiting.Add(key))
                {
                    throw new InvalidOperationException($"The theorems that {key} names form a cycle.");
                }
                var level = 1 + units[key].Unit.Deps.Where(keys.Contains).Select(Level).DefaultIfEmpty(0).Max();
                visiting.Remove(key);
                levels.Add(key, level);
                return level;
            }

            foreach (var key in keys)
            {
                Level(key);
            }
            return levels;
        }

        /// <summary>
        /// Records every theorem's name as its unit's (KTD33). The declarations definitions and types admitted were recorded
        /// by <see cref="Own"/> as they were admitted.
        /// </summary>
        private void RecordOwners(Translation translation)
        {
            foreach (var unit in translation.Units)
            {
                if (unit.Theorem is { } shell)
                {
                    _owners.TryAdd(shell.Name, unit.Key);
                }
            }
        }

        /// <summary>
        /// Records a unit as the owner of a declaration it admitted into the run's fork (KTD33), with an inductive type's
        /// constructors and recursors, whatever the unit's outcome: a unit that fails or runs out after admitting it leaves
        /// it in the fork. Called only before the fork is frozen, on the run's own thread.
        /// </summary>
        public void Own(string key, KernelDeclaration declaration)
        {
            foreach (var name in NamesOf(declaration))
            {
                _owners.TryAdd(name, key);
            }
        }

        private static IEnumerable<Name> NamesOf(KernelDeclaration declaration) => declaration switch
        {
            DefinitionDecl d => [d.Value.Name],
            TheoremDecl t => [t.Value.Name],
            AxiomDecl a => [a.Value.Name],
            OpaqueDecl o => [o.Value.Name],
            InductiveDecl i => i.Types.SelectMany(t => t.Constructors.Select(c => c.Name).Append(t.Name).Append(KernelNames.RecName(t.Name))),
            _ => [],
        };

        /// <summary>
        /// The first <c>Lean.Const</c> in a theorem's script that names a constant another translated unit owns when that
        /// unit is not among the theorem's dependencies (KTD33), with the tactic that names it; null if there is none.
        /// </summary>
        public (TacticNode Node, string Constant, string Owner)? ConstOutsideDependencies(EngineUnit unit, VirList<TacticNode> script)
        {
            HashSet<string>? closure = null;
            foreach (var (node, name) in script.SelectMany(LeanConsts))
            {
                // A name that does not parse names no unit's constant; the tactic that reads it reports it for this unit alone.
                if (TryParseName(name) is not { } parsed
                    || !_owners.TryGetValue(parsed, out var owner)
                    || string.Equals(owner, unit.Unit.Key, StringComparison.Ordinal))
                {
                    continue;
                }
                closure ??= Closure(unit);
                if (!closure.Contains(owner))
                {
                    return (node, name, owner);
                }
            }
            return null;

            static IEnumerable<(TacticNode, string)> LeanConsts(TacticNode node) => node.Args.SelectMany(arg => arg switch
            {
                LeanRefArg l => [(node, l.Name)],
                TacticArg { Tactic: var nested } => LeanConsts(nested),
                _ => [],
            });
        }

        /// <summary>A <c>Lean.Const</c> string as a name; null if it is not a well-formed one.</summary>
        private static Name? TryParseName(string text)
        {
            try
            {
                return Name.Parse(text);
            }
            catch (Exception ex) when (ex is FormatException or OverflowException)
            {
                return null;
            }
        }

        /// <summary>The keys of every unit a unit depends on, transitively.</summary>
        private HashSet<string> Closure(EngineUnit unit) => ClosureOf(unit, units);

        /// <summary>
        /// The outcome a unit has without starting: cancelled when the run is, skipped when a unit it depends on was not
        /// admitted; null when it starts, or, if it has an entry, is reported from the cache.
        /// </summary>
        private UnitOutcome? Early(EngineUnit unit) => (UnitOutcome?)Cancelled(unit) ?? Skip(unit);

        /// <summary>The cancelled outcome of a unit if the run is cancelled; null if it is not.</summary>
        public CancelledOutcome? Cancelled(EngineUnit unit) =>
            options.CancellationToken.IsCancellationRequested
                ? new CancelledOutcome(unit.Unit.Key, unit.Unit.Kind, Display(unit), Assumptions(unit))
                : null;

        /// <summary>
        /// KTD12: once the run is cancelled no unit starts, and a unit it interrupted ran out of a budget it was given,
        /// which is no verdict: an undecided outcome becomes the cancelled one while the run is cancelled.
        /// </summary>
        private UnitOutcome SettleCancel(EngineUnit unit, UnitOutcome outcome) =>
            outcome is UndecidedOutcome ? Cancelled(unit) ?? outcome : outcome;

        /// <summary>
        /// Translates every unit that translates: a unit whose dependency was decided before the run without being admitted
        /// is skipped, a unit translation rejects fails, the units depending on either are skipped, and translation runs
        /// again without them.
        /// </summary>
        private Translation Translate()
        {
            SkipDependents();
            var remaining = units.Values.Where(u => !Outcomes.ContainsKey(u.Unit.Key)).ToList();
            while (true)
            {
                try
                {
                    return Translator.Translate(
                        remaining.Select(u => u.Unit),
                        bundle.Env,
                        remaining.Where(u => u.DisplayName is not null).ToDictionary(u => u.Unit.Key, u => u.DisplayName!, StringComparer.Ordinal));
                }
                catch (TranslationException ex) when (ex.Key is { } key && units.TryGetValue(key, out var failed) && !Outcomes.ContainsKey(key))
                {
                    Outcomes.Add(key, new FailedOutcome(key, failed.Unit.Kind, Display(failed), Assumptions(failed), ex.Message));
                    SkipDependents();
                    remaining = [.. remaining.Where(u => !Outcomes.ContainsKey(u.Unit.Key))];
                }
            }
        }

        /// <summary>Skips every unit, transitively, that depends on a unit with an outcome other than admitted.</summary>
        private void SkipDependents()
        {
            bool changed = true;
            while (changed)
            {
                changed = false;
                foreach (var unit in units.Values.Where(u => !Outcomes.ContainsKey(u.Unit.Key)))
                {
                    if (Skip(unit) is { } skipped)
                    {
                        Outcomes.Add(unit.Unit.Key, skipped);
                        changed = true;
                    }
                }
            }
        }

        /// <summary>
        /// How goals and messages name translated constants and record fields (KTD7): a unit by its C# short name
        /// (<c>Increment</c>), a member of a type under the type's short name (<c>PaymentResult.Valid</c>), a field by its C#
        /// name.
        /// </summary>
        private NotationNames NamesOf(Translation translation)
        {
            var byName = translation.Units.ToDictionary(u => u.Name, u => u);
            var fields = translation.Units
                .Where(u => units[u.Key].Unit.Definition is RecordDefinition)
                .ToDictionary(u => u.Name, u => ((RecordDefinition)units[u.Key].Unit.Definition!).Fields.Select(f => f.Name).ToArray());
            return new NotationNames(
                name =>
                {
                    if (byName.TryGetValue(name, out var unit))
                    {
                        return OutcomeText.ShortName(unit.DisplayName);
                    }
                    if (!translation.DisplayNames.TryGetValue(name, out var display))
                    {
                        return null;
                    }
                    return name.Prefix is { } prefix && byName.TryGetValue(prefix, out var owner)
                        ? display.Replace(owner.DisplayName, OutcomeText.ShortName(owner.DisplayName), StringComparison.Ordinal)
                        : display;
                },
                (type, i) => fields.TryGetValue(type, out var names) && i < names.Length ? names[i] : null);
        }

        /// <summary>
        /// The skip outcome of a unit that depends on a unit that was not admitted (it failed or was skipped, or it is a
        /// theorem that was not proved); null if it has none.
        /// </summary>
        private SkippedOutcome? Skip(EngineUnit unit)
        {
            foreach (var dep in unit.Unit.Deps)
            {
                if (Outcomes.GetValueOrDefault(dep) is { } outcome and not (TranslatedOutcome or ProvedOutcome))
                {
                    var name = units.TryGetValue(dep, out var depUnit) ? Display(depUnit) : outcome.DisplayName;
                    return new SkippedOutcome(
                        unit.Unit.Key, unit.Unit.Kind, Display(unit), Assumptions(unit), dep, $"it depends on {name}, which was not admitted.");
                }
            }
            return null;
        }

        /// <summary>A unit's own assumptions; a theorem's also include those of every unit it depends on, transitively.</summary>
        public ImmutableArray<UnitAssumption> Assumptions(EngineUnit unit)
        {
            var result = unit.Unit.Assumptions.Select(a => new UnitAssumption(unit.Unit.Key, a)).ToList();
            if (unit.Unit.Kind != VirUnitKind.Theorem)
            {
                return [.. result];
            }
            // Passing through the unit itself reaches only its own dependencies again, so its closure without it is the
            // same set the walk from those dependencies reaches.
            foreach (var key in Closure(unit).Where(k => !string.Equals(k, unit.Unit.Key, StringComparison.Ordinal)).Order(StringComparer.Ordinal))
            {
                if (units.TryGetValue(key, out var dep))
                {
                    result.AddRange(dep.Unit.Assumptions.Select(a => new UnitAssumption(key, a)));
                }
            }
            return [.. result];
        }

        public static string Display(EngineUnit unit) => unit.DisplayName ?? LeanNames.FallbackDisplay(unit.Unit.Key);
    }
}
