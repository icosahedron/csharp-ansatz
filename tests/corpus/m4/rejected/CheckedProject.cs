// Compiled with overflow checking on (expected.json sets checkOverflow for this file): every
// operation that can overflow is checked and rejected until M6; a widening conversion cannot
// overflow and is accepted (plan KTD15).
using Warrant;

namespace Corpus.Rejected.CheckedProject;

public static class Checked
{
    [Verified]
    public static int Add(int a, int b) => a + b;

    [Verified]
    public static int Negate(int a) => -a;

    [Verified]
    public static int Narrow(long a) => (int)a;

    [Verified]
    public static long Widen(int a) => a;
}
