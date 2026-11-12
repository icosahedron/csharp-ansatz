// Moved from tests/corpus/m4/rejected/Statements.cs by M6 U7 and U17 (keys unchanged): an explicit throw, which the
// method's obligation allows (KTD12), and a decimal passed through (KTD7).
using System;
using Warrant;

namespace Corpus.Rejected;

public static class Statements
{
    [Verified]
    public static int Throws(int n) => n >= 0 ? n : throw new ArgumentOutOfRangeException(nameof(n));

    [Verified]
    public static decimal Decimals(decimal d) => d;
}
