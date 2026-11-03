// Code that a build's #if symbols change (plan KTD15). Extraction compares every combination of the tested symbols.
using Warrant;

namespace Corpus.Rejected;

public static class Conditional
{
    // A Debug build returns 1 and a Release build 2, so no single model describes both.
    [Verified]
    public static int BuildNumber()
    {
#if DEBUG
        return 1;
#else
        return 2;
#endif
    }

    // Unaffected by the #if above, so it is translated as usual.
    [Verified]
    public static int Unaffected(int x) => x;
}
