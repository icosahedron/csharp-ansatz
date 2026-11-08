using System.Collections.Immutable;
using System.Globalization;
using Warrant.Kernel;
using Warrant.Semantics;
using Warrant.Vir;

namespace Warrant.Engine.Reports;

/// <summary>A unit's status in the assumption report (docs/m4/07).</summary>
public enum ReportStatus
{
    /// <summary>A function or type unit the kernel admitted.</summary>
    Translated,

    /// <summary>A theorem the kernel admitted with its proof.</summary>
    Verified,

    /// <summary>Anything else: a false, unproved, undecided, failed, skipped or cancelled unit, or an internal error.</summary>
    Failed,
}

/// <summary>
/// The assumption report of one engine run (design §8.4, docs/m4/07): per unit, what it was checked against and what its
/// outcome assumes. Every name is a C# display name, never a Lean name.
/// </summary>
/// <param name="Kernel">The kernel that checked the units, e.g. <c>Warrant 1.0</c>.</param>
/// <param name="Bundle">The semantics bundle the units were admitted into.</param>
/// <param name="Global">The assumptions every unit makes: the overflow setting and what the bundle models.</param>
/// <param name="Units">One report per unit, in the engine's unit order.</param>
public sealed record AssumptionReport(string Kernel, string Bundle, ImmutableArray<string> Global, ImmutableArray<UnitReport> Units)
{
    /// <summary>Finds a unit's report by key.</summary>
    /// <param name="key">The documentation-comment ID.</param>
    /// <returns>The report, or null.</returns>
    public UnitReport? Find(string key) => Units.FirstOrDefault(u => string.Equals(u.Key, key, StringComparison.Ordinal));
}

/// <summary>One unit's entry in the assumption report.</summary>
/// <param name="Key">The documentation-comment ID.</param>
/// <param name="Kind">What the unit is.</param>
/// <param name="DisplayName">The C# display name.</param>
/// <param name="Status">The status.</param>
/// <param name="Outcome">
/// The engine outcome: <c>translated</c>, <c>proved</c>, <c>false</c>, <c>unproved</c>, <c>undecided</c>,
/// <c>internal</c>, <c>failed</c> or <c>skipped</c>.
/// </param>
/// <param name="By">For a verified theorem, the proof the kernel accepted (<c>rfl</c>, <c>decide</c> or <c>script</c>); otherwise null.</param>
/// <param name="Claim">For a theorem, the claim's source text when it is known; otherwise null.</param>
/// <param name="Detail">For a failed unit, why; otherwise null.</param>
/// <param name="Assumptions">The unit's own assumptions, then those it inherits from the units it depends on.</param>
public sealed record UnitReport(
    string Key,
    VirUnitKind Kind,
    string DisplayName,
    ReportStatus Status,
    string Outcome,
    string? By,
    string? Claim,
    string? Detail,
    ImmutableArray<ReportAssumption> Assumptions)
{
    /// <summary>
    /// What the unit's model leaves out besides the report's <see cref="AssumptionReport.Global"/> assumptions: for a
    /// recursive method, and a theorem about one, that each recursive call returns (M5a KTD31). Empty for other units.
    /// </summary>
    public ImmutableArray<string> Global { get; init; } = [];
}

/// <summary>One assumption, rendered for people.</summary>
/// <param name="Kind">What is assumed.</param>
/// <param name="Subject">A parameter path for a non-null assumption, the type's display name otherwise.</param>
/// <param name="From">The display name of the unit whose VIR records it.</param>
/// <param name="Inherited">Whether it comes from a unit this one depends on rather than from the unit itself.</param>
/// <param name="Text">The sentence the report prints, e.g. <c>p is not null</c>.</param>
public sealed record ReportAssumption(VirAssumptionKind Kind, string Subject, string From, bool Inherited, string Text);

/// <summary>What the report says about the run as a whole.</summary>
/// <param name="CheckOverflow">Whether the project checks arithmetic overflow.</param>
/// <param name="Bundle">The bundle's name, e.g. <c>warrant-semantics sha256:0123456789ab</c>.</param>
/// <param name="Kernel">The kernel's name; <see cref="AssumptionReports.DefaultKernel"/> when null.</param>
public sealed record ReportSettings(bool CheckOverflow, string Bundle, string? Kernel = null);

/// <summary>Builds <see cref="AssumptionReport"/>s from engine results.</summary>
public static class AssumptionReports
{
    /// <summary>What the bundle models, a global assumption of every unit.</summary>
    public const string BundleModels = "The semantics bundle models C# 14 int, long and bool";

    /// <summary>
    /// The axioms every proof may rest on, a global assumption of every unit: the bundle loads only if these are its only
    /// axioms (#26), and translation adds none.
    /// </summary>
    public static readonly string Axioms = "The only axioms are Lean's standard ones: " + string.Join(", ", SemanticsBundle.StandardAxioms);

    /// <summary>The overflow assumption when overflow checking is off.</summary>
    public const string Wraps = "Arithmetic wraps on overflow (overflow checking is off)";

    /// <summary>The overflow assumption when overflow checking is on.</summary>
    public const string Throws = "Arithmetic throws on overflow (overflow checking is on)";

    /// <summary>
    /// The model has no stack (M5a KTD31): a recursive method's proofs are about the calls that return, and a call that
    /// would exhaust the CLR's stack, which .NET cannot catch, is outside them.
    /// </summary>
    public const string Stack = "Each recursive call returns without exhausting the stack";

    /// <summary>The kernel's name and version, from the kernel assembly.</summary>
    public static string DefaultKernel { get; } = KernelName();

    /// <summary>Builds the report of an engine result (M4 R16, docs/m4/06).</summary>
    /// <param name="result">The result.</param>
    /// <param name="units">The engine's input units, for their spans and their dependencies.</param>
    /// <param name="settings">The overflow setting and the bundle's name.</param>
    /// <param name="sourceText">Reads a span's source text, for theorems' claims; null to leave claims out.</param>
    /// <returns>The report.</returns>
    public static AssumptionReport Build(
        EngineResult result, IEnumerable<EngineUnit> units, ReportSettings settings, Func<VirSpan, string?>? sourceText = null)
    {
        ArgumentNullException.ThrowIfNull(result);
        return Build([.. result.Units.Select(Service.OutcomeDto.From)], units, settings, sourceText);
    }

    /// <summary>
    /// Builds the report of outcomes as the wire carries them (M5b KTD25), which is what the CLI renders on either path
    /// and what the server keeps for <c>report(project)</c>, so the two are the same report.
    /// </summary>
    /// <param name="outcomes">The outcomes, in the request's order.</param>
    /// <param name="units">The engine's input units, for their spans and their dependencies.</param>
    /// <param name="settings">The overflow setting and the bundle's name.</param>
    /// <param name="sourceText">Reads a span's source text, for theorems' claims; null to leave claims out.</param>
    /// <returns>The report.</returns>
    public static AssumptionReport Build(
        IReadOnlyList<Service.OutcomeDto> outcomes, IEnumerable<EngineUnit> units, ReportSettings settings, Func<VirSpan, string?>? sourceText = null)
    {
        ArgumentNullException.ThrowIfNull(units);
        var byKey = units.GroupBy(u => u.Unit.Key, StringComparer.Ordinal).ToDictionary(g => g.Key, g => g.First(), StringComparer.Ordinal);
        return Build(outcomes, byKey, settings, key =>
            sourceText is not null && byKey.TryGetValue(key, out var unit) && ClaimSpan(unit) is { } span ? sourceText(span) : null);
    }

    /// <summary>
    /// Builds the report of wire outcomes with the theorems' claims given by key, for the server, which has no source text:
    /// the client sends each theorem's claim with the request.
    /// </summary>
    /// <param name="outcomes">The outcomes, in the request's order.</param>
    /// <param name="units">The engine's input units, by key, for their dependencies.</param>
    /// <param name="settings">The overflow setting and the bundle's name.</param>
    /// <param name="claim">A theorem's claim text by its key, or null.</param>
    /// <returns>The report.</returns>
    public static AssumptionReport Build(
        IReadOnlyList<Service.OutcomeDto> outcomes, IReadOnlyDictionary<string, EngineUnit> units, ReportSettings settings, Func<string, string?> claim)
    {
        ArgumentNullException.ThrowIfNull(outcomes);
        ArgumentNullException.ThrowIfNull(units);
        ArgumentNullException.ThrowIfNull(settings);
        ArgumentNullException.ThrowIfNull(claim);
        var names = outcomes.ToDictionary(u => u.Key, u => u.DisplayName, StringComparer.Ordinal);
        string Name(string key) => names.TryGetValue(key, out var n) ? n : LeanNames.FallbackDisplay(key);

        var reports = ImmutableArray.CreateBuilder<UnitReport>(outcomes.Count);
        foreach (var dto in outcomes)
        {
            var text = dto.UnitKind == VirUnitKind.Theorem ? claim(dto.Key) : null;
            // A proved theorem's wire form has no certificate, which the report does not need.
            var (status, by, detail, name) = dto.Kind == Service.OutcomeKind.Proved
                ? (ReportStatus.Verified, ProofName(dto.By ?? ProofKind.Script), (string?)null, "proved")
                : Describe(dto.ToOutcome([]));
            ImmutableArray<UnitAssumption> assumptions = [.. dto.Assumptions.Select(a => new UnitAssumption(a.UnitKey, new VirAssumption(a.Kind, a.Subject)))];
            var rendered = assumptions
                .Select(a => Render(a, dto.Key, Name))
                .OrderBy(a => a.Inherited)
                .ToImmutableArray();
            reports.Add(new UnitReport(dto.Key, dto.UnitKind, dto.DisplayName, status, name, by, text, detail, rendered)
            {
                Global = ReliesOnRecursion(dto.Key, units) ? [Stack] : [],
            });
        }

        var global = ImmutableArray.Create(settings.CheckOverflow ? Throws : Wraps, BundleModels, Axioms);
        return new AssumptionReport(settings.Kernel ?? DefaultKernel, settings.Bundle, global, reports.MoveToImmutable());
    }

    private static (ReportStatus Status, string? By, string? Detail, string Name) Describe(UnitOutcome outcome)
    {
        var (status, by, detail) = outcome switch
        {
            TranslatedOutcome => (ReportStatus.Translated, (string?)null, (string?)null),
            ProvedOutcome p => (ReportStatus.Verified, ProofName(p.By), null),
            FalseOutcome => (ReportStatus.Failed, null, OutcomeText.FalseDetail),
            NotProvedOutcome n => (ReportStatus.Failed, null, OutcomeText.NotProvedDetail(n)),
            UndecidedOutcome u => (ReportStatus.Failed, null, OutcomeText.UndecidedDetail(u.Reason)),
            InternalErrorOutcome i => (ReportStatus.Failed, null, OutcomeText.InternalErrorDetail(i.Reason)),
            FailedOutcome f => (ReportStatus.Failed, null, f.Reason),
            SkippedOutcome s => (ReportStatus.Failed, null, s.Reason),
            CancelledOutcome => (ReportStatus.Failed, null, "the run was cancelled before this unit finished."),
            _ => throw new InvalidOperationException($"Unknown outcome {outcome.GetType().Name}."),
        };
        return (status, by, detail, OutcomeName(outcome));
    }

    /// <summary>
    /// Whether a unit is a recursive method, or depends on one, transitively, through the units the engine was given
    /// (KTD31).
    /// </summary>
    private static bool ReliesOnRecursion(string key, IReadOnlyDictionary<string, EngineUnit> units)
    {
        var seen = new HashSet<string>(StringComparer.Ordinal);
        var work = new Stack<string>([key]);
        while (work.Count > 0)
        {
            var next = work.Pop();
            if (!seen.Add(next) || !units.TryGetValue(next, out var unit))
            {
                continue;
            }
            if (Translator.IsRecursive(unit.Unit))
            {
                return true;
            }
            foreach (var dep in unit.Unit.Deps)
            {
                work.Push(dep);
            }
        }
        return false;
    }

    /// <summary>The span of a theorem's claim: the statement's node, numbered in pre-order (docs/m4/04).</summary>
    /// <param name="unit">The unit.</param>
    /// <returns>The span, or null for a unit without a statement or without spans.</returns>
    public static VirSpan? ClaimSpan(EngineUnit unit)
    {
        ArgumentNullException.ThrowIfNull(unit);
        if (unit.Unit.Statement is not { } statement || unit.Spans is null)
        {
            return null;
        }
        return VirTree.IdOf(unit.Unit, statement) is { } id && unit.Spans.TryGetSpan(id, out var span) ? span : null;
    }

    /// <summary>The proof's name as reports and messages print it.</summary>
    /// <param name="kind">The proof.</param>
    /// <returns><c>rfl</c>, <c>decide</c> or <c>script</c>.</returns>
    public static string ProofName(ProofKind kind) => kind switch
    {
        ProofKind.Rfl => "rfl",
        ProofKind.Decide => "decide",
        _ => "script",
    };

    /// <summary>The outcome's name as reports and the CLI print it.</summary>
    /// <param name="outcome">The outcome.</param>
    /// <returns>
    /// <c>translated</c>, <c>proved</c>, <c>false</c>, <c>unproved</c>, <c>undecided</c>, <c>internal</c>, <c>failed</c>,
    /// <c>skipped</c> or <c>cancelled</c>.
    /// </returns>
    /// <exception cref="InvalidOperationException">The outcome is of an unknown kind.</exception>
    public static string OutcomeName(UnitOutcome outcome) => outcome switch
    {
        TranslatedOutcome => "translated",
        ProvedOutcome => "proved",
        FalseOutcome => "false",
        NotProvedOutcome => "unproved",
        UndecidedOutcome => "undecided",
        InternalErrorOutcome => "internal",
        FailedOutcome => "failed",
        SkippedOutcome => "skipped",
        CancelledOutcome => "cancelled",
        _ => throw new InvalidOperationException($"Unknown outcome {outcome?.GetType().Name}."),
    };

    private static ReportAssumption Render(UnitAssumption assumption, string unitKey, Func<string, string> name)
    {
        var (kind, subject) = (assumption.Assumption.Kind, assumption.Assumption.Subject);
        var shown = kind == VirAssumptionKind.NonNull ? subject : name(subject);
        var text = kind switch
        {
            VirAssumptionKind.NonNull => $"{shown} is not null",
            VirAssumptionKind.Closed => $"{shown} has only its named members",
            VirAssumptionKind.ClosedEquality => $"{shown}'s equality agrees with identity on its named members",
            _ => throw new InvalidOperationException($"Unknown assumption kind {kind}."),
        };
        var inherited = !string.Equals(assumption.UnitKey, unitKey, StringComparison.Ordinal);
        return new ReportAssumption(kind, shown, name(assumption.UnitKey), inherited, text);
    }

    private static string KernelName()
    {
        var version = typeof(KernelEnvironment).Assembly.GetName().Version ?? new Version(0, 0);
        return string.Create(CultureInfo.InvariantCulture, $"Warrant {version.Major}.{version.Minor}");
    }
}
