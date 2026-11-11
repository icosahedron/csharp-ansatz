// Moved from tests/corpus/m4/rejected/Statements.cs by M6 U7 (key unchanged): an explicit throw, which the method's
// obligation allows (KTD12).
using System;
using Warrant;

namespace Corpus.Rejected;

public static class Statements
{
    [Verified]
    public static int Throws(int n) => n >= 0 ? n : throw new ArgumentOutOfRangeException(nameof(n));
}
