// Moved from tests/corpus/m4/rejected/Statements.cs by M6 U7 (key unchanged): Math.Abs is modelled now, and throws
// OverflowException for int.MinValue (R4).
using System;
using Warrant;

namespace Corpus.Rejected;

public static class Statements
{
    [Verified]
    public static int CallsUnverified(int n) => Math.Abs(n);
}
