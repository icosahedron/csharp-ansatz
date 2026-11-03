// A [Closed] closed-set class (design D13). C# cannot switch over its instances, which are not
// constants, so verified code compares them with ==. For a null argument the CLR returns 3 from
// Code, a value the model cannot produce; the non-null assumption excludes it (docs/m4/07).
using Warrant;

namespace Claims;

[Closed]
public sealed class Outcome
{
    public static Outcome Matched { get; } = new("Matched");

    public static readonly Outcome NoMatch = new("NoMatch");

    private Outcome(string name) => Name = name;

    public string Name { get; }
}

public static class Outcomes
{
    [Verified]
    public static int Code(Outcome o) => o == Outcome.Matched ? 1 : o == Outcome.NoMatch ? 2 : 3;

    [Verified]
    public static bool Same(Outcome a, Outcome b) => a == b;

    [Theorem]
    static Proof MatchedIsOne() => Prove.That(Code(Outcome.Matched) == 1);

    [Theorem]
    static Proof NoMatchIsTwo() => Prove.That(Code(Outcome.NoMatch) == 2);

    [Theorem]
    static Proof DifferentOutcomes() => Prove.That(!Same(Outcome.Matched, Outcome.NoMatch));
}
