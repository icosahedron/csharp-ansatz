// Compiled with overflow checking on (expected.json sets checkOverflow for this file): a widening
// conversion cannot overflow and is accepted (plan KTD15). The members whose operations can overflow
// moved to tests/corpus/m6 when M6 accepted checked arithmetic (README).
using Warrant;

namespace Corpus.Rejected.CheckedProject;

public static class Checked
{
    [Verified]
    public static long Widen(int a) => a;
}
