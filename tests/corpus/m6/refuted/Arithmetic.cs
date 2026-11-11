// Moved from tests/corpus/m4/rejected/Arithmetic.cs by M6 U7 (key unchanged): checked addition can overflow, and with no
// Spec.Requires nothing rules that out (KTD12).
using Warrant;

namespace Corpus.Rejected;

public static class Arithmetic
{
    [Verified]
    public static int CheckedAdd(int a, int b) => checked(a + b);
}
