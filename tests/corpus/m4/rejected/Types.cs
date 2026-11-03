// Records and classes M4 rejects (plan KTD6, KTD10, KTD15).
using Warrant;

namespace Corpus.Rejected;

public record Unsealed(int X);

public sealed record OwnEquality(int X)
{
    public bool Equals(OwnEquality? other) => other is not null && X % 10 == other.X % 10;

    public override int GetHashCode() => X % 10;
}

// The generated Equals compares Extra too, which a model built from the primary constructor would miss.
public sealed record ExtraState(int X)
{
    public int Extra { get; init; }
}

public readonly record struct Pair(int A, int B);

public sealed record Left(Right Other);

public sealed record Right(Left Other);

// casesOn is a name Lean gives an inductive's auxiliary construction (plan KTD6).
public sealed record Reserved(int casesOn);

public sealed class Counter
{
    private readonly int _start;

    public Counter(int start) => _start = start;

    [Verified]
    public int Next() => _start + 1;
}

public static class Types
{
    [Verified]
    public static int UsesUnsealed(Unsealed u) => u.X;

    [Verified]
    public static bool UsesOwnEquality(OwnEquality a, OwnEquality b) => a == b;

    [Verified]
    public static int UsesExtraState(ExtraState e) => e.X;

    [Verified]
    public static int UsesRecordStruct(Pair p) => p.A;

    [Verified]
    public static Left UsesCyclicRecords(Left l) => l;

    [Verified]
    public static int UsesReservedName(Reserved r) => r.casesOn;

    [Verified]
    public static int NullableParameter(Point? p) => p is null ? 0 : 1;

    [Verified]
    public static Point? ReturnsNull() => null;
}

public sealed record Point(int X, int Y);
