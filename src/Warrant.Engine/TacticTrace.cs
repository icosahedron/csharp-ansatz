using System.Collections.Immutable;
using Warrant.Cic;
using Warrant.Meta;
using Warrant.Vir;

namespace Warrant.Engine;

/// <summary>
/// One tactic of a proof script as it ran (M5b KTD24, docs/m5b/07): what <c>warrant explain</c> prints. Recorded by the
/// untrusted tactic layer and trusted for nothing; the kernel's check of the finished proof is unchanged.
/// </summary>
/// <param name="Depth">0 for a step of the script; one more for each <c>AllGoals</c> or <c>Try</c> it runs inside.</param>
/// <param name="Tactic">The tactic's name as VIR has it (Lean's: <c>unfold</c>, <c>omega</c>, …).</param>
/// <param name="Node">The tactic's VIR node ID, which the client maps to a source span; null when it has none.</param>
/// <param name="Before">The goals before the tactic, printed as a failed proof prints them; empty when there are none.</param>
/// <param name="After">The goals after it, when it succeeded; empty when it closed every goal.</param>
/// <param name="Failure">Why it failed, when it did. A failure inside a <c>Try</c> is recorded, and the script goes on.</param>
public sealed record TacticStep(int Depth, string Tactic, int? Node, string Before, string? After, string? Failure);

/// <summary>Records the steps a <see cref="TacticRunner"/> runs, in the order they start.</summary>
/// <param name="print">Prints goals as a failed proof's diagnostic does.</param>
/// <param name="nodeId">The VIR node ID of a tactic node.</param>
internal sealed class TacticRecorder(Func<IEnumerable<MVarId>, string> print, Func<TacticNode, int?> nodeId)
{
    private readonly List<TacticStep> _steps = [];
    private int _depth;

    /// <summary>The steps so far.</summary>
    public ImmutableArray<TacticStep> Steps => [.. _steps];

    /// <summary>A tactic starts on these goals; returns the step's slot for <see cref="Succeeded"/> or <see cref="Failed"/>.</summary>
    public int Started(TacticNode node, IEnumerable<MVarId> goals)
    {
        _steps.Add(new TacticStep(_depth, node.Name, nodeId(node), print(goals), null, null));
        _depth++;
        return _steps.Count - 1;
    }

    /// <summary>The tactic in <paramref name="slot"/> succeeded, leaving these goals.</summary>
    public void Succeeded(int slot, IEnumerable<MVarId> goals)
    {
        _depth--;
        _steps[slot] = _steps[slot] with { After = print(goals) };
    }

    /// <summary>The tactic in <paramref name="slot"/> failed.</summary>
    public void Failed(int slot, string reason)
    {
        _depth--;
        _steps[slot] = _steps[slot] with { Failure = reason };
    }
}
