// Moved from tests/corpus/m4/rejected/Arithmetic.cs by M6 U7 (keys unchanged): `/` and `%` by a constant other than
// 0 and -1 cannot throw, so these stay pure (KTD11) and are expected to prove as M4 members do.
using Warrant;

namespace Corpus.Rejected;

public static class Arithmetic
{
    [Verified]
    public static int Halve(int x) => x / 2;

    [Verified]
    public static int Remainder(int x) => x % 3;
}
