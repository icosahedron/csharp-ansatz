// Records and classes M4 rejects (plan KTD6, KTD10, KTD15).
using Warrant;

namespace Corpus.Rejected;

public record Unsealed(int X);

public sealed record OwnEquality(int X)
{
    public bool Equals(OwnEquality? other) => other is not null && X % 10 == other.X % 10;

    public override int GetHashCode() => X % 10;
}

// #132: EqualityComparer<ExplicitEquality>.Default, which an enclosing record's Equals uses, calls this one.
public sealed record ExplicitEquality(int X) : System.IEquatable<ExplicitEquality>
{
    bool System.IEquatable<ExplicitEquality>.Equals(ExplicitEquality? other) => true;
}

public sealed record HoldsExplicitEquality(ExplicitEquality Inner);

// The generated Equals compares Extra too, which a model built from the primary constructor would miss.
public sealed record ExtraState(int X)
{
    public int Extra { get; init; }
}

// `with` runs this constructor, so (r with { }).X is X + 100, not the field-by-field copy the model makes.
public sealed record OwnCopy(int X)
{
    private OwnCopy(OwnCopy original) => X = original.X + 100;
}

// The generated Equals compares Grade through Grade.Equals, under which A and B are equal; the model would compare
// them as two instances.
[Closed]
public sealed class Grade
{
    public static Grade A { get; } = new(1);

    public static Grade B { get; } = new(1);

    private Grade(int rank) => Rank = rank;

    public int Rank { get; }

    public override bool Equals(object? obj) => obj is Grade g && g.Rank == Rank;

    public override int GetHashCode() => Rank;
}

public sealed record Graded(Grade Grade);

public readonly record struct Pair(int A, int B);

public sealed record Left(Right Other);

public sealed record Right(Left Other);

// casesOn is a name Lean gives an inductive's auxiliary construction (plan KTD6).
public sealed record Reserved(int casesOn);

// An instance property of a class: M6 accepts a class's instance methods that call dependencies, not its properties.
public sealed class Tally
{
    private readonly int _start;

    public Tally(int start) => _start = start;

    [Verified]
    public int Current => _start;
}

public static class Types
{
    [Verified]
    public static int UsesUnsealed(Unsealed u) => u.X;

    [Verified]
    public static bool UsesOwnEquality(OwnEquality a, OwnEquality b) => a == b;

    [Verified]
    public static bool UsesExplicitEquality(HoldsExplicitEquality a, HoldsExplicitEquality b) => a == b;

    [Verified]
    public static bool UsesGraded(Graded a, Graded b) => a == b;

    [Verified]
    public static int UsesExtraState(ExtraState e) => e.X;

    [Verified]
    public static int UsesOwnCopy(OwnCopy r) => (r with { }).X;

    [Verified]
    public static int UsesRecordStruct(Pair p) => p.A;

    [Verified]
    public static Left UsesCyclicRecords(Left l) => l;

    [Verified]
    public static int UsesReservedName(Reserved r) => r.casesOn;

    // NullableParameter and ReturnsNull, which M6 supports, moved to tests/corpus/m6 (README). A parameter not
    // declared nullable is assumed non-null, so comparing it with null stays rejected.
    [Verified]
    public static bool ComparesWithNull(Point p) => p == null;
}

public sealed record Point(int X, int Y);
