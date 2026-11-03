using System.Globalization;
using System.Text.RegularExpressions;
using FsCheck;
using FsCheck.Fluent;
using Microsoft.FSharp.Core;
using Xunit.Sdk;

namespace Warrant.TestSupport;

/// <summary>
/// How property-based tests run (M5a KTD26, docs/m5a/08): a pinned seed, so every run tests the same inputs; a count
/// that the environment can raise; and a failure message that says how to replay the failure.
/// <list type="bullet">
/// <item><c>WARRANT_PBT_SEED</c>: unset, the pinned <see cref="DefaultSeed"/>; <c>seed,gamma</c> (as a failure prints
/// it), that seed; <c>random</c>, a seed from the clock. FsCheck requires <c>gamma</c> to be odd.</item>
/// <item><c>WARRANT_PBT_COUNT</c>: the number of cases per property, for every property.</item>
/// <item><c>WARRANT_PBT_LONG=1</c>: <see cref="LongCount"/> cases per property, unless <c>WARRANT_PBT_COUNT</c> is set.</item>
/// </list>
/// </summary>
public static partial class Pbt
{
    /// <summary>The variable that pins or replays the seed.</summary>
    public const string SeedVariable = "WARRANT_PBT_SEED";

    /// <summary>The variable that sets the number of cases.</summary>
    public const string CountVariable = "WARRANT_PBT_COUNT";

    /// <summary>The variable that selects the long run.</summary>
    public const string LongVariable = "WARRANT_PBT_LONG";

    /// <summary>The number of cases per property in the long run.</summary>
    public const int LongCount = 10_000;

    /// <summary>The seed used when <c>WARRANT_PBT_SEED</c> is unset.</summary>
    public static (ulong Seed, ulong Gamma) DefaultSeed { get; } = (20261103, 1);

    /// <summary>The configuration from the environment, with <paramref name="count"/> cases unless the environment says otherwise.</summary>
    public static Config Config(int count) => Config(count, Environment.GetEnvironmentVariable);

    /// <summary>The configuration from the variables <paramref name="variable"/> returns (null for unset).</summary>
    public static Config Config(int count, Func<string, string?> variable)
    {
        ArgumentNullException.ThrowIfNull(variable);
        var config = FsCheck.Config.QuickThrowOnFailure.WithMaxTest(Count(count, variable));
        return Seed(variable(SeedVariable)) is { } s
            ? config.WithReplay(FSharpOption<Replay>.Some(new Replay(new Rnd(s.Seed, s.Gamma), FSharpOption<int>.None)))
            : config;
    }

    /// <summary>The number of cases: <c>WARRANT_PBT_COUNT</c>, else <see cref="LongCount"/> in the long run, else <paramref name="count"/>.</summary>
    public static int Count(int count, Func<string, string?> variable)
    {
        ArgumentNullException.ThrowIfNull(variable);
        if (variable(CountVariable) is { Length: > 0 } text)
        {
            return int.TryParse(text, NumberStyles.None, CultureInfo.InvariantCulture, out var n) && n > 0
                ? n
                : throw new ArgumentException($"{CountVariable} must be a positive number, not '{text}'.", nameof(variable));
        }
        return variable(LongVariable) == "1" ? LongCount : count;
    }

    /// <summary>
    /// The seed a value of <c>WARRANT_PBT_SEED</c> selects: <see cref="DefaultSeed"/> when unset, none (a seed from the
    /// clock) for <c>random</c>, else the pair <c>seed,gamma</c>, with or without parentheses.
    /// </summary>
    public static (ulong Seed, ulong Gamma)? Seed(string? value)
    {
        if (string.IsNullOrWhiteSpace(value))
        {
            return DefaultSeed;
        }
        if (value.Trim() == "random")
        {
            return null;
        }
        var match = SeedPattern().Match(value);
        if (!match.Success
            || !ulong.TryParse(match.Groups[1].Value, NumberStyles.None, CultureInfo.InvariantCulture, out var seed)
            || !ulong.TryParse(match.Groups[2].Value, NumberStyles.None, CultureInfo.InvariantCulture, out var gamma))
        {
            throw new ArgumentException($"{SeedVariable} must be 'random' or 'seed,gamma', not '{value}'.", nameof(value));
        }
        return gamma % 2 == 1
            ? (seed, gamma)
            : throw new ArgumentException($"{SeedVariable}: FsCheck requires gamma to be odd, not {gamma}.", nameof(value));
    }

    /// <summary>Checks a property with <see cref="Config(int)"/>; a failure says how to replay it.</summary>
    public static void Check(Property property, int count) => Check(property, Config(count));

    /// <summary>
    /// Checks a property. A failure is FsCheck's report (the shrunk counterexample and the run's seed) followed by the
    /// line <c>Replay with WARRANT_PBT_SEED=seed,gamma</c>.
    /// </summary>
    public static void Check(Property property, Config config)
    {
        ArgumentNullException.ThrowIfNull(property);
        try
        {
            property.Check(config);
        }
#pragma warning disable CA1031 // Rethrown with the replay hint when it is a falsified property, else unchanged.
        catch (Exception ex) when (ReportedSeed().Match(ex.Message) is { Success: true } seed)
#pragma warning restore CA1031
        {
            throw new XunitException($"{ex.Message}\nReplay with {SeedVariable}={seed.Groups[1].Value},{seed.Groups[2].Value}", ex);
        }
    }

    [GeneratedRegex(@"^\s*\(?\s*(\d+)\s*,\s*(\d+)\s*\)?\s*$")]
    private static partial Regex SeedPattern();

    /// <summary>FsCheck's failure report: <c>Falsifiable, after 3 tests (2 shrinks) (seed,gamma):</c>.</summary>
    [GeneratedRegex(@"\(\d+ shrinks?\) \((\d+),(\d+)\)")]
    private static partial Regex ReportedSeed();
}
