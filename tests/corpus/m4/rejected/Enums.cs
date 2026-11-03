// Enum uses M4 rejects or warns about (plan KTD13, KTD15, KTD18).
using Warrant;

namespace Corpus.Rejected;

public enum Light { Red, Amber, Green }

[Closed]
public enum Phase { Draft, Open, Closed }

// Two members with the same value would become two constructors the kernel proves different.
[Closed]
public enum Aliased { First = 0, Second = 0, Third = 1 }

// No member is 0, so default(Starting) is a value the closed model says cannot exist (WRT0008).
[Closed]
public enum Starting { One = 1, Two = 2 }

// Only int and long underlying types are modelled; this one has a value no long holds.
[Closed]
public enum Wide : ulong { Zero = 0, Max = ulong.MaxValue }

public static class Enums
{
    // .NET throws SwitchExpressionException for an unnamed value; exceptions are M6.
    [Verified]
    public static int LightCode(Light l) => l switch
    {
        Light.Red => 0,
        Light.Amber => 1,
        Light.Green => 2,
    };

    [Verified]
    public static Phase PhaseFromInt(int x) => (Phase)x;

    [Verified]
    public static Phase UnnamedConstant() => (Phase)5;

    [Verified]
    public static Phase DefaultPhase() => default;

    [Verified]
    public static bool UsesAliased(Aliased a) => a == Aliased.First;

    [Verified]
    public static int Relational(Phase p) => p switch
    {
        >= Phase.Open => 1,
        _ => 0,
    };

    // A switch over a closed type is its recursor, so only constants, `or` and `_` can be placed.
    [Verified]
    public static int NotPattern(Phase p) => p switch
    {
        not Phase.Draft => 1,
        _ => 0,
    };

    [Verified]
    public static bool RelationalComparison(Phase p) => p > Phase.Draft;

    // Unverified code: integer casts and unboxing to a [Closed] enum are warnings (WRT0008).
    public static Phase CastInUnverifiedCode(int x) => (Phase)x;

    public static Phase UnboxInUnverifiedCode(object o) => (Phase)o;

    // So is arithmetic, which can step past the last member.
    public static Phase NextInUnverifiedCode(Phase p) => p + 1;
}
