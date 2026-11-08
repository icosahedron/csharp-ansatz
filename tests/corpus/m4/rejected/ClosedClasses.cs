// [Closed] classes without the closed shape (WRT0009, one per step in docs/m4/03), and reading a
// closed class's instance state (WRT0002).
using Warrant;

namespace Corpus.Rejected;

// Step 1: not sealed.
[Closed]
public class NotSealed
{
    public static NotSealed A { get; } = new();

    private NotSealed() { }
}

// Step 2: a constructor that is not private.
[Closed]
public sealed class PublicConstructor
{
    public static PublicConstructor A { get; } = new();

    public PublicConstructor() { }
}

// Step 3: a property with an expression body returns a new instance on every read.
[Closed]
public sealed class FreshEveryRead
{
    public static FreshEveryRead A => new();

    private FreshEveryRead() { }
}

// Step 4: the private constructor is called outside the static initialisers.
[Closed]
public sealed class Factory
{
    public static Factory A { get; } = new();

    private Factory() { }

    public static Factory Make() => new();
}

// Step 3: a static constructor runs after the initialisers and here makes Second the same object as First.
[Closed]
public sealed class Reassigned
{
    public static readonly Reassigned First = new();
    public static readonly Reassigned Second = new();

    static Reassigned() => Second = First;

    private Reassigned() { }
}

// Step 5: no instances at all.
[Closed]
public sealed class Empty
{
    private Empty() { }
}

// Step 3: the constructor divides by its argument, so the type initialiser throws and every use of the class
// throws TypeInitializationException, while the model would still have the instance.
[Closed]
public sealed class Throws
{
    public static Throws Zero { get; } = new(0);

    private Throws(int divisor) => Ratio = 100 / divisor;

    public int Ratio { get; }
}

[Closed]
public sealed class Tier
{
    public static Tier Gold { get; } = new(3);

    private Tier(int rank) => Rank = rank;

    public int Rank { get; }
}

public static class ClosedClasses
{
    [Verified]
    public static int ReadsAField(Tier t) => t.Rank;

    [Verified]
    public static bool UsesThrows(Throws t) => t == Throws.Zero;
}
