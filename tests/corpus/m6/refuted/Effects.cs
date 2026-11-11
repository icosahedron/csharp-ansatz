// M6 U7's new constructs whose implicit exceptions nothing rules out without a Spec.Requires (KTD12).
using System;
using Warrant;

namespace Corpus.M6.Refuted;

public static class Effects
{
    [Verified]
    public static int Ratio(int a, int b) => a / b;

    [Verified]
    public static long Magnitude(long a) => Math.Abs(a);
}
