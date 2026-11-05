namespace Warrant.Extraction;

/// <summary>How extraction treats <c>#if</c> (KTD21; docs/m5a/07, "Reproducing the compilation").</summary>
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
}
