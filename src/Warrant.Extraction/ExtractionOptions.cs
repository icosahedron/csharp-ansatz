using Microsoft.CodeAnalysis.CSharp;

namespace Warrant.Extraction;

/// <summary>
/// How extraction treats <c>#if</c> (KTD21; docs/m5a/07, "Reproducing the compilation"), and the referenced projects whose
/// source it may read (#32).
/// </summary>
public sealed class ExtractionOptions
{
    /// <summary>M4's settings: no build's defines, so every <c>#if</c> combination is compared.</summary>
    public static ExtractionOptions Default { get; } = new();

    /// <summary>
    /// Whether the compilation was parsed with a real build's defines (from Csc's arguments). Code is then translated
    /// under that build's configuration, without comparing <c>#if</c> combinations, unless
    /// <see cref="KeepConditionalCheck"/> is set.
    /// </summary>
    public bool BuildDefines { get; init; }

    /// <summary>
    /// Whether to compare every combination of the <c>#if</c> symbols even with a build's defines: a multi-targeted
    /// build sets it, so code whose translation differs between target frameworks is rejected rather than verified for one.
    /// </summary>
    public bool KeepConditionalCheck { get; init; }

    /// <summary>
    /// A referenced project's compilation by assembly name, rebuilt from its recorded source
    /// (<c>Warrant.Frontend.ReferencedSource</c>), or null when there is none; null for no referenced sources (#32). It is
    /// asked only for the assembly of a <c>[Closed]</c> class that a unit uses, which is then checked from that source as
    /// a class of the compilation itself is, and a unit that uses it assumes the referenced assembly was built from that
    /// source. A compilation whose assembly identity is not the reference's is not used. It may throw
    /// <see cref="System.IO.InvalidDataException"/>, which extraction lets through.
    /// </summary>
    public Func<string, CSharpCompilation?>? ReferencedSource { get; init; }
}
