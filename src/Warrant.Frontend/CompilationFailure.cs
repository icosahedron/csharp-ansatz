using System.Collections.Immutable;
using System.Globalization;
using Microsoft.CodeAnalysis;

namespace Warrant.Frontend;

/// <summary>
/// A compilation that does not compile (WRT0012; KTD21). Generated sources exist only inside Csc, so a project whose code
/// needs a source generator's output fails this way; the symbols the compiler could not find are named.
/// </summary>
public sealed class CompilationFailure
{
    /// <summary>The diagnostic code the CLI reports.</summary>
    public const string Code = "WRT0012";

    /// <summary>
    /// The compiler errors that mean a name was not found: a type, namespace or member (CS0103, CS0117, CS0234, CS0246,
    /// CS0426, CS1061), or the implementation of a partial member a generator would write (CS8795, CS9248).
    /// </summary>
    private static readonly ImmutableHashSet<string> MissingCodes =
        ImmutableHashSet.Create(StringComparer.Ordinal, "CS0103", "CS0117", "CS0234", "CS0246", "CS0426", "CS1061", "CS8795", "CS9248");

    internal CompilationFailure(IReadOnlyList<Diagnostic> errors)
    {
        Errors = errors;
        MissingSymbols = errors
            .Where(d => MissingCodes.Contains(d.Id) && d.Location.IsInSource)
            .Select(d => d.Location.SourceTree!.GetText().ToString(d.Location.SourceSpan))
            .Distinct(StringComparer.Ordinal)
            .OrderBy(n => n, StringComparer.Ordinal)
            .ToList();
    }

    /// <summary>The names the compiler could not find, as written in the source, sorted ordinally and without repeats.</summary>
    public IReadOnlyList<string> MissingSymbols { get; }

    /// <summary>Every compiler error, in the compiler's order.</summary>
    public IReadOnlyList<Diagnostic> Errors { get; }

    /// <summary>A message for people: the missing symbols, or the first error when no name is missing.</summary>
    public string Message =>
        MissingSymbols.Count > 0
            ? "The compilation does not compile without generated sources (source generators run only inside the compiler); missing: "
                + string.Join(", ", MissingSymbols) + "."
            : "The compilation does not compile: " + Errors[0].GetMessage(CultureInfo.InvariantCulture);
}
