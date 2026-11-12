// Moved from tests/corpus/m4/rejected/CheckedProject.cs by M6 U7 (keys unchanged). Compiled with overflow checking on
// (expected.json sets checkOverflow for this file): each operation is checked and can overflow.
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
}
