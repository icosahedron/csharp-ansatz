using System.Diagnostics;
using System.Runtime.CompilerServices;

namespace Warrant.Meta;

/// <summary>Resource limits for Meta, separate from the kernel's (docs/m5a/02, "Budgets inside Meta").</summary>
/// <param name="Fuel">
/// The step budget: each step of Meta's recursive traversals costs one unit. Lean bounds the same
/// work with <c>maxHeartbeats</c>; running out fails the tactic, never succeeds it.
/// </param>
public sealed record MetaLimits(long Fuel)
{
    /// <summary>
    /// An optional wall-clock deadline, normally the theorem's, checked at the same points as fuel.
    /// <see langword="null"/> (the default) means no deadline.
    /// </summary>
    public DateTimeOffset? Deadline { get; init; }

    /// <summary>
    /// An optional cancellation token (M5b KTD12), polled where the deadline is; a cancelled token fails the tactic with
    /// a <see cref="MetaResourceException"/>. <see cref="CancellationToken.None"/> (the default) is never cancelled.
    /// </summary>
    public CancellationToken CancellationToken { get; init; }

    /// <summary>Defaults for one theorem: 20M steps, the kernel's interactive budget.</summary>
    public static MetaLimits Default { get; } = new(20_000_000);
}

/// <summary>
/// The fuel, deadline and cancellation token that one <see cref="MetaM"/> run charges as it works (Lean's
/// <c>checkSystem</c>/<c>checkMaxHeartbeats</c>).
/// </summary>
public sealed class MetaBudget
{
    // Reading the clock costs more than a step, so the deadline and the cancellation token are
    // checked on the first step and then once every ClockCheckInterval steps, as in the kernel.
    private const int ClockCheckInterval = 1024;

    private readonly long _deadlineTimestamp;
    private long _fuel;
    private int _ticksUntilClockCheck;

    /// <summary>Creates a budget with <paramref name="limits"/>.</summary>
    public MetaBudget(MetaLimits limits)
    {
        Limits = limits ?? throw new ArgumentNullException(nameof(limits));
        _fuel = limits.Fuel;
        _deadlineTimestamp = DeadlineTimestamp(limits.Deadline);
    }

    /// <summary>The limits this budget enforces.</summary>
    public MetaLimits Limits { get; }

    /// <summary>Fuel consumed so far.</summary>
    public long FuelUsed => Limits.Fuel - _fuel;

    /// <summary>
    /// Charges one step. Throws <see cref="MetaResourceException"/> when fuel runs out, the
    /// deadline has passed or the run is cancelled, and <see cref="InsufficientExecutionStackException"/> before the stack
    /// would overflow.
    /// </summary>
    public void Tick()
    {
        if (--_fuel < 0)
        {
            throw new MetaResourceException($"tactic fuel exhausted ({Limits.Fuel:N0} steps)");
        }
        if ((_deadlineTimestamp != long.MaxValue || Limits.CancellationToken.CanBeCanceled) && --_ticksUntilClockCheck < 0)
        {
            _ticksUntilClockCheck = ClockCheckInterval - 1;
            if (Limits.CancellationToken.IsCancellationRequested)
            {
                throw new MetaResourceException("tactic cancelled");
            }
            if (Stopwatch.GetTimestamp() >= _deadlineTimestamp)
            {
                throw new MetaResourceException($"tactic deadline passed ({Limits.Deadline:O})");
            }
        }
        RuntimeHelpers.EnsureSufficientExecutionStack();
    }

    private static long DeadlineTimestamp(DateTimeOffset? deadline)
    {
        if (deadline is not { } d)
        {
            return long.MaxValue;
        }
        long now = Stopwatch.GetTimestamp();
        double remainingTicks = (d - DateTimeOffset.UtcNow).TotalSeconds * Stopwatch.Frequency;
        return remainingTicks <= 0 ? now
            : remainingTicks >= long.MaxValue - now ? long.MaxValue - 1
            : now + (long)remainingTicks;
    }
}
