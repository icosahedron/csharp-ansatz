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
public static class Pipeline
{
    private static readonly Name BoolFalse = Name.Parse("Bool.false");
    private static readonly Name EqName = Name.Parse("Eq");
    private static readonly Name LtName = Name.Parse("LT.lt");
    private static readonly Name LeName = Name.Parse("LE.le");

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
    /// <returns>The result, with each unit's time and the number of units whose proof search ran.</returns>
    /// <exception cref="ArgumentException">Two units have the same key.</exception>
    internal static PipelineRun Execute(
        IReadOnlyList<EngineUnit> inputs,
        IReadOnlyList<UnitOutcome> decided,
        IReadOnlyList<string> order,
        SemanticsBundle bundle,
        EngineOptions options,
        WorkerPool? pool)
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

        var run = new RunState(bundle, byKey, options, decided, pool);
        KernelThread.Run(run.Execute);
        return new PipelineRun(
            new EngineResult(bundle, run.Env, [.. order.Select(k => run.Outcomes[k])], [.. run.Admitted]),
            run.Elapsed,
            run.SearchRuns);
    }

    /// <summary>Builds the shared simp sets over the frozen bundle alone, before any fork exists to leak into them (KTD10).</summary>
    private static void WarmSimpSets(SemanticsBundle bundle, Sidecar sidecar)
    {
        DefaultSimpSet.Theorems(bundle.Env, sidecar);
        OmegaPrepSet.Theorems(bundle.Env, sidecar);
    }

    /// <summary>What <see cref="Execute"/> produced.</summary>
    /// <param name="Result">The outcomes and the final environment.</param>
    /// <param name="Elapsed">Each unit's time from the moment it started to its outcome; absent for units decided before the run.</param>
    /// <param name="SearchRuns">The number of units whose proof search ran: theorems, and recursive definitions' decrease proofs.</param>
    internal sealed record PipelineRun(EngineResult Result, IReadOnlyDictionary<string, TimeSpan> Elapsed, int SearchRuns);

    /// <summary>
    /// One unit's budgets (M5a R13, M5b KTD11): the project's, overridden by a theorem's <c>[Theorem(...)]</c> arguments
    /// where they are not zero, with one deadline for Meta and the kernel, which starts when the unit does. A definition,
    /// with its decrease proofs and equation lemma, has the project's budgets and no overrides.
    /// </summary>
    private sealed class TheoremBudget
    {
        public TheoremBudget(EngineOptions options, VirBudget? overrides)
        {
            Timeout = overrides is { TimeoutSeconds: > 0 } ? TimeSpan.FromSeconds(overrides.TimeoutSeconds) : options.Timeout;
            var deadline = DateTimeOffset.UtcNow + Timeout;
            Kernel = options.Kernel with
            {
                Fuel = overrides is { KernelFuel: > 0 } ? overrides.KernelFuel : options.Kernel.Fuel,
                Deadline = deadline,
                CancellationToken = options.CancellationToken,
            };
            Meta = new MetaLimits(overrides is { TacticFuel: > 0 } ? overrides.TacticFuel : options.TacticFuel)
            {
                Deadline = deadline,
                CancellationToken = options.CancellationToken,
            };
        }

        public TimeSpan Timeout { get; }

        public KernelLimits Kernel { get; }

        public MetaLimits Meta { get; }

        /// <summary>Which budget a resource exception exhausted, for WRT0006's message.</summary>
        public string Exhausted(Exception ex)
        {
            if (ex is MetaResourceException { InnerException: KernelResourceException kernel })
            {
                // The kernel ran out inside Meta's Check (KTD12): its budget, not Meta's.
                ex = kernel;
            }
            if (ex.Message.Contains("deadline", StringComparison.Ordinal) || DateTimeOffset.UtcNow >= Kernel.Deadline)
            {
                return string.Create(CultureInfo.InvariantCulture, $"the time limit of {Timeout.TotalSeconds:0.###} s was reached");
            }
            return ex switch
            {
                MetaResourceException => string.Create(CultureInfo.InvariantCulture, $"tactic fuel ran out ({Meta.Fuel:N0} steps)"),
                KernelResourceException when ex.Message.StartsWith("kernel fuel", StringComparison.Ordinal) =>
                    string.Create(CultureInfo.InvariantCulture, $"kernel fuel ran out ({Kernel.Fuel:N0} steps)"),
                _ => $"the kernel ran out of resources: {ex.Message}",
            };
        }
    }

    /// <summary>
    /// A run's shared state (KTD8, KTD10): the units, the outcomes and admitted declarations merged so far, and the run's
    /// fork of the bundle and the sidecar, which the definitions are admitted into and which is frozen before any theorem
    /// runs. Each theorem works in a <see cref="Scope"/> of its own; its outcome is merged when its level ends.
    /// </summary>
    private sealed class RunState(
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
            var theorems = new List<TranslatedUnit>();
            foreach (var unit in translation.Units)
            {
                if (unit.Theorem is not null)
                {
                    theorems.Add(unit);
                    continue;
                }
                var stopwatch = Stopwatch.StartNew();
                var outcome = Cancelled(units[unit.Key]) ?? Skip(units[unit.Key]) ?? new Scope(this, Env, Attributes).Admit(unit);
                Outcomes.Add(unit.Key, SettleCancel(units[unit.Key], outcome));
                Elapsed.Add(unit.Key, stopwatch.Elapsed);
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
                var jobs = new List<(TranslatedUnit Unit, Func<(UnitOutcome, TimeSpan)> Work)>();
                foreach (var theorem in ordered)
                {
                    var unit = units[theorem.Key];
                    if (((UnitOutcome?)Cancelled(unit) ?? Skip(unit)) is { } early)
                    {
                        Outcomes.Add(theorem.Key, early);
                        Elapsed.Add(theorem.Key, TimeSpan.Zero);
                        continue;
                    }
                    jobs.Add((theorem, () => Prove(theorem, levelEnv)));
                }
                (UnitOutcome, TimeSpan)[] results = pool is null
                    ? [.. jobs.Select(j => j.Work())]
                    : pool.RunAll(jobs.Select(j => j.Work));
                for (int i = 0; i < jobs.Count; i++)
                {
                    Outcomes.Add(jobs[i].Unit.Key, results[i].Item1);
                    Elapsed.Add(jobs[i].Unit.Key, results[i].Item2);
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
            try
            {
                outcome = Cancelled(unit) ?? new Scope(this, levelEnv.Fork(), Attributes.Fork()).Admit(theorem);
            }
            catch (OperationCanceledException)
            {
                // KTD32: a cancel during the counterexample search ends the unit as cancelled, not as a failure.
                outcome = Cancelled(unit) ?? throw new InvalidOperationException("A unit was cancelled although the run was not.");
            }
            return (SettleCancel(unit, outcome), stopwatch.Elapsed);
        }

        /// <summary>
        /// Admits a level's proved theorems, in input order, into a new fork of the run's environment and freezes it, so
        /// the next level's theorems can use them. The kernel checks each proof again, as it does every term admitted
        /// into an environment; one it now rejects is Warrant's bug, and the theorem's users are skipped.
        /// </summary>
        private void AdmitProved(List<TranslatedUnit> level)
        {
            var proved = level.Where(t => Outcomes[t.Key] is ProvedOutcome).ToList();
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
        /// Which unit each constant the run translated belongs to (KTD33): every declaration a definition or type admitted,
        /// with an inductive type's constructors and recursors, and every theorem's name.
        /// </summary>
        private void RecordOwners(Translation translation)
        {
            foreach (var unit in translation.Units)
            {
                if (unit.Theorem is { } shell)
                {
                    _owners.TryAdd(shell.Name, unit.Key);
                    continue;
                }
                foreach (var declaration in Outcomes[unit.Key].Declarations)
                {
                    foreach (var name in NamesOf(declaration))
                    {
                        _owners.TryAdd(name, unit.Key);
                    }
                }
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
                if (!_owners.TryGetValue(Name.Parse(name), out var owner) || string.Equals(owner, unit.Unit.Key, StringComparison.Ordinal))
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

        /// <summary>The keys of every unit a unit depends on, transitively.</summary>
        private HashSet<string> Closure(EngineUnit unit)
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

    /// <summary>
    /// Where one unit is admitted (KTD8): the run's fork for a definition or type, a theorem's own fork of its level's
    /// environment for a theorem. What the unit admits is recorded here and merged into the run by the caller.
    /// </summary>
    private sealed class Scope(RunState run, KernelEnvironment env, Sidecar attributes)
    {
        private readonly EngineOptions options = run.Options;

        private KernelEnvironment Env => env;

        private Sidecar Attributes => attributes;

        public UnitOutcome Admit(TranslatedUnit translated)
        {
            var unit = run.Units[translated.Key];
            var display = translated.DisplayName;
            var assumptions = run.Assumptions(unit);
            if (translated.Theorem is { } shell)
            {
                run.CountSearch();
                if (shell.Script is { } script && run.ConstOutsideDependencies(unit, script) is { } outside)
                {
                    var owner = RunState.Display(run.Units[outside.Owner]);
                    return new FailedOutcome(
                        unit.Unit.Key, unit.Unit.Kind, display, assumptions,
                        $"Malformed proof script: Lean.Const(\"{outside.Constant}\") names a constant of '{OutcomeText.ShortName(owner)}', which this theorem does not depend on; name it with nameof({OutcomeText.ShortName(owner)}) instead.")
                    {
                        Code = FailedOutcome.MalformedScriptCode,
                        Node = VirTree.IdOf(unit.Unit, outside.Node),
                    };
                }
                var budget = new TheoremBudget(options, shell.Budget);
                return shell.Script is null && shell.Statement.Instance is not null
                    ? Compute(unit, shell, display, assumptions, budget)
                    : RunScript(unit, shell, display, assumptions, budget);
            }
            var admitted = new List<KernelDeclaration>();
            var definitionBudget = new TheoremBudget(options, null);
            if (translated.Recursion is { } recursion)
            {
                if (recursion.Decreases.Length > 0)
                {
                    run.CountSearch();
                }
                return AdmitRecursive(unit, translated, recursion, assumptions, admitted, definitionBudget);
            }
            foreach (var declaration in translated.Declarations)
            {
                try
                {
                    AddDeclaration(declaration, admitted, definitionBudget);
                    if (declaration is DefinitionDecl { Value: { Hints.Kind: ReducibilityHintsKind.Abbrev } abbrev })
                    {
                        // KTD9: an open enum and its members are `abbrev`s (docs/m4/05), reducible as Lean's are, so simp
                        // and instance resolution see through them (docs/m5a/05).
                        Attributes.SetReducibilityStatus(abbrev.Name, ReducibilityStatus.Reducible);
                    }
                    if (declaration is InductiveDecl inductive)
                    {
                        // KTD8: casesOn and ctorIdx, which Lean's elaborator would have made, each built after the last is admitted.
                        foreach (var construction in Constructions.For(Env, inductive))
                        {
                            AddDeclaration(construction, admitted, definitionBudget);
                            Constructions.Register(Attributes, construction.Value);
                        }
                    }
                }
                catch (KernelResourceException ex)
                {
                    return new UndecidedOutcome(unit.Unit.Key, unit.Unit.Kind, display, assumptions, $"{definitionBudget.Exhausted(ex)} while the kernel checked the definition.");
                }
                catch (KernelException ex)
                {
                    return new FailedOutcome(unit.Unit.Key, unit.Unit.Kind, display, assumptions, ex.Message);
                }
            }
            return new TranslatedOutcome(unit.Unit.Key, unit.Unit.Kind, display, assumptions, [.. admitted]);
        }

        /// <summary>
        /// A recursive method (M5a KTD14, KTD15): each decrease theorem proved by the omega pipeline and admitted, then the
        /// definition, which refers to them, marked irreducible for Meta as Lean marks its well-founded definitions, then
        /// the equation lemma with its bare <c>Nat.fix_eq</c> proof. A decrease theorem that is not proved is WRT0001 at
        /// its call, with its goal; an equation lemma the kernel rejects fails the unit. All of it runs in the unit's one
        /// budget, and running out of it anywhere is WRT0006 (M5b KTD11).
        /// </summary>
        private UnitOutcome AdmitRecursive(
            EngineUnit unit,
            TranslatedUnit translated,
            RecursiveDefinition recursion,
            ImmutableArray<UnitAssumption> assumptions,
            List<KernelDeclaration> admitted,
            TheoremBudget budget)
        {
            var key = unit.Unit.Key;
            var kind = unit.Unit.Kind;
            var display = translated.DisplayName;
            foreach (var decrease in recursion.Decreases)
            {
                if (ProveDecrease(unit, decrease, display, assumptions, admitted, budget) is { } failure)
                {
                    return failure;
                }
            }
            try
            {
                foreach (var declaration in translated.Declarations)
                {
                    AddDeclaration(declaration, admitted, budget);
                }
                Attributes.SetReducibilityStatus(translated.Name, ReducibilityStatus.Irreducible);
            }
            catch (KernelResourceException ex)
            {
                return new UndecidedOutcome(key, kind, display, assumptions, $"{budget.Exhausted(ex)} while the kernel checked the definition.");
            }
            catch (KernelException ex)
            {
                return new FailedOutcome(key, kind, display, assumptions, ex.Message);
            }
            try
            {
                AddDeclaration(recursion.Equation.WithProof(recursion.EquationProof), admitted, budget);
            }
            catch (KernelResourceException ex)
            {
                return new UndecidedOutcome(key, kind, display, assumptions, $"{budget.Exhausted(ex)} while the kernel checked the equation lemma {recursion.Equation.Name}.");
            }
            catch (KernelException ex)
            {
                return new FailedOutcome(key, kind, display, assumptions, $"the kernel rejected the equation lemma {recursion.Equation.Name}: {ex.Message}");
            }
            return new TranslatedOutcome(key, kind, display, assumptions, [.. admitted]);
        }

        /// <summary>
        /// One decrease theorem (KTD15): its binders introduced under their own names, then <c>Tactic.Omega()</c>'s
        /// pipeline; the proof the kernel admits. Null when it was admitted, else the unit's outcome.
        /// </summary>
        private UnitOutcome? ProveDecrease(
            EngineUnit unit,
            DecreaseObligation decrease,
            string display,
            ImmutableArray<UnitAssumption> assumptions,
            List<KernelDeclaration> admitted,
            TheoremBudget budget)
        {
            var key = unit.Unit.Key;
            var kind = unit.Unit.Kind;
            var shell = decrease.Theorem;
            var meta = new MetaM(Env, budget.Meta) { KernelLimits = budget.Kernel, Attributes = Attributes, DisplayNames = run.Names };
            var goal = meta.MkFreshExprSyntheticOpaqueMVar(shell.Type);
            MVarId? current = null;
            Expr proof;
            try
            {
                var introduced = meta.IntroN(goal.Id, decrease.Binders).Goal;
                current = introduced;
                meta.OmegaTactic(introduced);
                proof = meta.InstantiateMVars(goal);
            }
            catch (Exception ex) when (ex is MetaResourceException or KernelResourceException)
            {
                return new UndecidedOutcome(key, kind, display, assumptions, $"{budget.Exhausted(ex)} while proving the decrease of {Describe(unit, decrease)}.");
            }
            catch (InsufficientExecutionStackException)
            {
                return new UndecidedOutcome(key, kind, display, assumptions, "proving a decrease obligation ran out of stack.");
            }
            catch (MetaException ex)
            {
                var failed = ex is TacticException { Goal: { } g } && meta.MCtx.FindDecl(g) is not null ? g : current ?? goal.Id;
                var printer = new GoalPrinter(Env, run.Names);
                return new NotProvedOutcome(key, kind, display, assumptions, ex.Message, printer.PpGoals(meta.MCtx, [failed]), VirTree.IdOf(unit.Unit, decrease.Call), [])
                {
                    Decrease = new DecreaseFailure(decrease.Index, VirTree.IdOf(unit.Unit, decrease.Call), VirTree.IdOf(unit.Unit, decrease.Measure)),
                };
            }
#pragma warning disable CA1031 // KTD19: an unexpected failure in Meta ends this unit as Warrant's bug, not the whole run.
            catch (Exception ex)
#pragma warning restore CA1031
            {
                return new InternalErrorOutcome(key, kind, display, assumptions, $"Meta failed unexpectedly: {ex.GetType().Name}: {ex.Message}");
            }
            if (proof.HasExprMVar || proof.HasLevelMVar || proof.HasFVar)
            {
                return new InternalErrorOutcome(key, kind, display, assumptions, $"omega closed the decrease obligation {shell.Name}, but the proof term still has a hole.");
            }
            try
            {
                AddDeclaration(shell.WithProof(proof), admitted, budget);
            }
            catch (KernelResourceException ex)
            {
                return new UndecidedOutcome(key, kind, display, assumptions, $"{budget.Exhausted(ex)} while the kernel checked a decrease proof.");
            }
            catch (KernelException ex)
            {
                return new InternalErrorOutcome(key, kind, display, assumptions, $"the kernel rejected the decrease proof Warrant built for {shell.Name}: {ex.Message}");
            }
            return null;
        }

        private static string Describe(EngineUnit unit, DecreaseObligation decrease) => $"recursive call {decrease.Index} of {RunState.Display(unit)}";

        private void AddDeclaration(KernelDeclaration declaration, List<KernelDeclaration> admitted, TheoremBudget budget)
        {
            Kernel.Kernel.Add(Env, declaration, budget.Kernel);
            run.Admitted.Add(declaration);
            admitted.Add(declaration);
        }

        /// <summary>
        /// A closed theorem with no script (M4, KTD12): tries <c>rfl</c>, then <c>decide</c>; if neither is admitted, reduces
        /// <c>decide P D</c> to tell false from undecided.
        /// </summary>
        private UnitOutcome Compute(EngineUnit unit, TheoremShell shell, string display, ImmutableArray<UnitAssumption> assumptions, TheoremBudget budget)
        {
            var key = unit.Unit.Key;
            foreach (var (kind, proof) in new[] { (ProofKind.Rfl, ProofTerms.Rfl(shell.Statement)), (ProofKind.Decide, ProofTerms.Decide(shell.Statement)) })
            {
                if (proof is null)
                {
                    continue;
                }
                var declaration = shell.WithProof(proof);
                try
                {
                    Kernel.Kernel.Add(Env, declaration, budget.Kernel);
                }
                catch (KernelResourceException ex) when (budget.Kernel.CancellationToken.IsCancellationRequested || DateTimeOffset.UtcNow >= budget.Kernel.Deadline)
                {
                    // KTD12: a cancellation or a passed deadline is shared by every method, so the next one cannot
                    // succeed. Running out of fuel falls through to the next method, which gets its own fuel, as in M5a.
                    return new UndecidedOutcome(
                        key, unit.Unit.Kind, display, assumptions, $"{budget.Exhausted(ex)} while the kernel checked the {kind.ToString().ToLowerInvariant()} proof.");
                }
                catch (KernelException)
                {
                    continue;
                }
                if (!ProofTerms.IsAdmittedAs(Env, shell))
                {
                    return new FailedOutcome(key, unit.Unit.Kind, display, assumptions, $"the kernel admitted {shell.Name} with a type other than its statement.");
                }
                return new ProvedOutcome(key, unit.Unit.Kind, display, assumptions, kind, declaration);
            }

            Expr decided;
            try
            {
                decided = new TypeChecker(Env, limits: budget.Kernel).Whnf(Operators.Decide(shell.Statement));
            }
            catch (KernelResourceException ex)
            {
                return new UndecidedOutcome(key, unit.Unit.Kind, display, assumptions, $"the kernel ran out of resources deciding the claim: {budget.Exhausted(ex)}.");
            }
            catch (KernelException ex)
            {
                return new UndecidedOutcome(key, unit.Unit.Kind, display, assumptions, $"the kernel could not decide the claim: {ex.Message}");
            }
            catch (InsufficientExecutionStackException ex)
            {
                return new UndecidedOutcome(key, unit.Unit.Kind, display, assumptions, $"the kernel ran out of stack deciding the claim: {ex.Message}");
            }
            if (decided is ConstExpr { Name: var b } && b == BoolFalse)
            {
                return new FalseOutcome(key, unit.Unit.Kind, display, assumptions, Sides(unit, shell));
            }
            return new UndecidedOutcome(key, unit.Unit.Kind, display, assumptions, "the claim does not compute to false, and neither proof was accepted.");
        }

        /// <summary>
        /// A theorem with a script, or with parameters (docs/m5a/04, "The loop"; KTD19): the goal <c>?g : statement</c>, the
        /// theorem's own parameters introduced under their C# names, then the script; with no goals left, the instantiated
        /// <c>?g</c> goes to the kernel. Each way it can fail is caught as what it is.
        /// </summary>
        /// <exception cref="OperationCanceledException">The run was cancelled during the counterexample search (KTD32).</exception>
        private UnitOutcome RunScript(EngineUnit unit, TheoremShell shell, string display, ImmutableArray<UnitAssumption> assumptions, TheoremBudget budget)
        {
            var key = unit.Unit.Key;
            var kind = unit.Unit.Kind;
            var meta = new MetaM(Env, budget.Meta) { KernelLimits = budget.Kernel, Attributes = Attributes, DisplayNames = run.Names };
            var printer = new GoalPrinter(Env, run.Names);
            var tactics = new TacticM(meta, []);
            var runner = new TacticRunner(tactics);

            UnitOutcome NotProved(string message, IEnumerable<MVarId> goals, TacticNode? at) => new NotProvedOutcome(
                key, kind, display, assumptions, message, printer.PpGoals(meta.MCtx, goals), at is null ? null : VirTree.IdOf(unit.Unit, at),
                Counterexample.Search(Env, unit.Unit, shell, run.Definitions, options.CancellationToken));

            Expr proof;
            try
            {
                var goal = meta.MkFreshExprSyntheticOpaqueMVar(shell.Type);
                tactics.Goals = [goal.Id];
                var parameters = unit.Unit.Params ?? VirList<VirParam>.Empty;
                if (parameters.Count > 0)
                {
                    tactics.LiftMetaTactic1(g => meta.IntroN(g, parameters.Count, [.. parameters.Select(p => Name.From(p.Name))]).Goal);
                }
                foreach (var node in shell.Script ?? VirList<TacticNode>.Empty)
                {
                    runner.Run(node);
                }
                if (tactics.GetUnsolvedGoals() is { IsEmpty: false } unsolved)
                {
                    return NotProved("unsolved goals", unsolved, null);
                }
                proof = meta.InstantiateMVars(goal);
            }
            catch (TacticUnavailableException ex)
            {
                return NotProved(ex.Message, tactics.GetUnsolvedGoals(), runner.FailedAt);
            }
            catch (Exception ex) when (ex is MetaResourceException or KernelResourceException)
            {
                return new UndecidedOutcome(key, kind, display, assumptions, $"{budget.Exhausted(ex)} while running the proof script.");
            }
            catch (InsufficientExecutionStackException)
            {
                return new UndecidedOutcome(key, kind, display, assumptions, "the proof script ran out of stack.");
            }
            catch (MetaException ex) when (runner.FailedAt is { } failedAt)
            {
                var goals = ex is TacticException { Goal: { } g } && meta.MCtx.FindDecl(g) is not null ? [g] : tactics.GetUnsolvedGoals();
                return NotProved(ex.Message, goals, failedAt);
            }
#pragma warning disable CA1031 // KTD19: an unexpected failure in Meta ends this theorem as Warrant's bug, not the whole run.
            catch (Exception ex) when (ex is not OperationCanceledException)
#pragma warning restore CA1031
            {
                return new InternalErrorOutcome(key, kind, display, assumptions, $"Meta failed unexpectedly: {ex.GetType().Name}: {ex.Message}");
            }

            if (options.TamperWithProof is { } tamper)
            {
                proof = tamper(proof);
            }
            if (proof.HasExprMVar || proof.HasLevelMVar || proof.HasFVar)
            {
                return new InternalErrorOutcome(key, kind, display, assumptions, "the proof script closed every goal, but the proof term still has a hole or a free variable.");
            }
            var declaration = shell.WithProof(proof);
            try
            {
                Kernel.Kernel.Add(Env, declaration, budget.Kernel);
            }
            catch (KernelResourceException ex)
            {
                return new UndecidedOutcome(key, kind, display, assumptions, $"{budget.Exhausted(ex)} while the kernel checked the proof.");
            }
            catch (KernelException ex)
            {
                return new InternalErrorOutcome(key, kind, display, assumptions, $"the kernel rejected the proof Warrant built: {ex.Message}");
            }
            if (!ProofTerms.IsAdmittedAs(Env, shell))
            {
                return new FailedOutcome(key, kind, display, assumptions, $"the kernel admitted {shell.Name} with a type other than its statement.");
            }
            return new ProvedOutcome(key, kind, display, assumptions, ProofKind.Script, declaration);
        }

        /// <summary>
        /// The two sides of a false claim that is one comparison, in source order, with their values read back. The
        /// statement's proposition has them as <c>@Eq T a b</c>, <c>@LT.lt T i a b</c> or <c>@LE.le T i a b</c>, with
        /// <c>&gt;</c> and <c>&gt;=</c> swapped; record and closed-type equality are not on their operands, so their values
        /// are unknown.
        /// </summary>
        private ImmutableArray<ReadBackSide> Sides(EngineUnit unit, TheoremShell shell)
        {
            if (unit.Unit.Statement is not CompareExpr { Op: not CompareOp.Ne } compare)
            {
                return [];
            }
            int Id(VirNode node) =>
                VirTree.IdOf(unit.Unit, node) ?? throw new InvalidOperationException("a statement operand is not among the unit's nodes");

            (Expr Type, Expr Left, Expr Right)? operands = null;
            if (compare.Kind is not (CompareKind.Record or CompareKind.Closed) && shell.Type.GetAppFn() is ConstExpr head)
            {
                var args = shell.Type.GetAppArgs();
                var swapped = compare.Op is CompareOp.Gt or CompareOp.Ge;
                if (head.Name == EqName && compare.Op == CompareOp.Eq && args.Length == 3)
                {
                    operands = (args[0], args[1], args[2]);
                }
                else if ((head.Name == LtName && compare.Op is CompareOp.Lt or CompareOp.Gt
                    || head.Name == LeName && compare.Op is CompareOp.Le or CompareOp.Ge) && args.Length == 4)
                {
                    operands = swapped ? (args[0], args[3], args[2]) : (args[0], args[2], args[3]);
                }
            }

            ReadBackSide Side(VirExpr node, Expr? term)
            {
                var id = Id(node);
                var value = term is null || operands is not { } o
                    ? new UnknownValue("the comparison's operands are not read back")
                    : ReadBack.Core(Env, term, o.Type, options.Kernel);
                return new ReadBackSide(id, value);
            }

            return [Side(compare.L, operands?.Left), Side(compare.R, operands?.Right)];
        }
    }
}
