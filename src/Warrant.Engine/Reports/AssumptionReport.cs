using System.Collections.Immutable;
using System.Globalization;
using Warrant.Kernel;
using Warrant.Vir;

namespace Warrant.Engine.Reports;

/// <summary>A unit's status in the assumption report (docs/m4/07).</summary>
public enum ReportStatus
{
    /// <summary>A function or type unit the kernel admitted.</summary>
    Translated,

    /// <summary>A theorem the kernel admitted with its proof.</summary>
    Verified,

    /// <summary>Anything else: a false, undecided, failed or skipped unit.</summary>
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
/// <param name="Outcome">The engine outcome: <c>translated</c>, <c>proved</c>, <c>false</c>, <c>undecided</c>, <c>failed</c> or <c>skipped</c>.</param>
/// <param name="By">For a verified theorem, the proof the kernel accepted (<c>rfl</c> or <c>decide</c>); otherwise null.</param>
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
    ImmutableArray<ReportAssumption> Assumptions);

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

    /// <summary>The overflow assumption when overflow checking is off.</summary>
    public const string Wraps = "Arithmetic wraps on overflow (overflow checking is off)";

    /// <summary>The overflow assumption when overflow checking is on.</summary>
    public const string Throws = "Arithmetic throws on overflow (overflow checking is on)";

    /// <summary>The kernel's name and version, from the kernel assembly.</summary>
    public static string DefaultKernel { get; } = KernelName();

    /// <summary>Builds the report of a run.</summary>
    /// <param name="result">The engine's result.</param>
    /// <param name="units">The units the engine was given, for the theorems' claim spans; may be empty.</param>
    /// <param name="settings">What the report says about the run as a whole.</param>
    /// <param name="sourceText">The source text of a span, for claims; null to leave claims out.</param>
    /// <returns>The report.</returns>
    public static AssumptionReport Build(
        EngineResult result, IEnumerable<EngineUnit> units, ReportSettings settings, Func<VirSpan, string?>? sourceText = null)
    {
        ArgumentNullException.ThrowIfNull(result);
        ArgumentNullException.ThrowIfNull(units);
        ArgumentNullException.ThrowIfNull(settings);
        var byKey = units.GroupBy(u => u.Unit.Key, StringComparer.Ordinal).ToDictionary(g => g.Key, g => g.First(), StringComparer.Ordinal);
        var names = result.Units.ToDictionary(u => u.Key, u => u.DisplayName, StringComparer.Ordinal);
        string Name(string key) => names.TryGetValue(key, out var n) ? n : FallbackName(key);

        var reports = ImmutableArray.CreateBuilder<UnitReport>(result.Units.Length);
        foreach (var outcome in result.Units)
        {
            string? claim = null;
            if (outcome.UnitKind == VirUnitKind.Theorem && sourceText is not null && byKey.TryGetValue(outcome.Key, out var unit)
                && ClaimSpan(unit) is { } span)
            {
                claim = sourceText(span);
            }
            var (status, by, detail) = outcome switch
            {
                TranslatedOutcome => (ReportStatus.Translated, (string?)null, (string?)null),
                ProvedOutcome p => (ReportStatus.Verified, ProofName(p.By), null),
                FalseOutcome => (ReportStatus.Failed, null, $"the claim is false ({FalseOutcome.Code})"),
                UndecidedOutcome u => (ReportStatus.Failed, null, $"the claim was not decided ({UndecidedOutcome.Code}): {u.Reason}"),
                FailedOutcome f => (ReportStatus.Failed, null, f.Reason),
                SkippedOutcome s => (ReportStatus.Failed, null, s.Reason),
                _ => throw new InvalidOperationException($"Unknown outcome {outcome.GetType().Name}."),
            };
            var assumptions = outcome.Assumptions
                .Select(a => Render(a, outcome.Key, Name))
                .OrderBy(a => a.Inherited)
                .ToImmutableArray();
            reports.Add(new UnitReport(outcome.Key, outcome.UnitKind, outcome.DisplayName, status, OutcomeName(outcome), by, claim, detail, assumptions));
        }

        var global = ImmutableArray.Create(settings.CheckOverflow ? Throws : Wraps, BundleModels);
        return new AssumptionReport(settings.Kernel ?? DefaultKernel, settings.Bundle, global, reports.MoveToImmutable());
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
        var nodes = VirTree.PreOrder(unit.Unit);
        for (int id = 0; id < nodes.Count; id++)
        {
            if (ReferenceEquals(nodes[id], statement))
            {
                return unit.Spans.TryGetSpan(id, out var span) ? span : null;
            }
        }
        return null;
    }

    /// <summary>The proof's name as reports and messages print it.</summary>
    /// <param name="kind">The proof.</param>
    /// <returns><c>rfl</c> or <c>decide</c>.</returns>
    public static string ProofName(ProofKind kind) => kind == ProofKind.Rfl ? "rfl" : "decide";

    /// <summary>The outcome's name as reports and the CLI print it.</summary>
    /// <param name="outcome">The outcome.</param>
    /// <returns><c>translated</c>, <c>proved</c>, <c>false</c>, <c>undecided</c>, <c>failed</c> or <c>skipped</c>.</returns>
    /// <exception cref="InvalidOperationException">The outcome is of an unknown kind.</exception>
    public static string OutcomeName(UnitOutcome outcome) => outcome switch
    {
        TranslatedOutcome => "translated",
        ProvedOutcome => "proved",
        FalseOutcome => "false",
        UndecidedOutcome => "undecided",
        FailedOutcome => "failed",
        SkippedOutcome => "skipped",
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

    /// <summary>A display name for a key with no unit: the ID without its kind prefix.</summary>
    private static string FallbackName(string key) => key.Length > 2 && key[1] == ':' ? key[2..] : key;

    private static string KernelName()
    {
        var version = typeof(KernelEnvironment).Assembly.GetName().Version ?? new Version(0, 0);
        return string.Create(CultureInfo.InvariantCulture, $"Warrant {version.Major}.{version.Minor}");
    }
}
