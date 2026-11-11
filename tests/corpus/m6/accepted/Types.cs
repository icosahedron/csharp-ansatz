// Moved from tests/corpus/m4/rejected/Types.cs by M6 U17 (keys unchanged): a parameter and a return value declared
// nullable, which are Option values (KTD5).
using Warrant;

namespace Corpus.Rejected;

public static class Types
{
    [Verified]
    public static int NullableParameter(Point? p) => p is null ? 0 : 1;

    [Verified]
    public static Point? ReturnsNull() => null;
}

public sealed record Point(int X, int Y);
