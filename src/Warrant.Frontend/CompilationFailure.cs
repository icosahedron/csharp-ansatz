using System.Collections.Immutable;
using System.Globalization;
using Microsoft.CodeAnalysis;

namespace Warrant.Frontend;

/// <summary>
/// A compilation Warrant cannot trust to be the compiler's (WRT0012; KTD21): it does not compile, or a source generator
/// could not load or threw, which fails even when the code compiles without the generator's output. The symbols the
/// compiler could not find are named.
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

    internal CompilationFailure(IReadOnlyList<Diagnostic> errors, IReadOnlyList<string> generatorProblems)
    {
        Errors = errors;
        GeneratorProblems = generatorProblems;
        MissingSymbols = errors
            .Where(d => MissingCodes.Contains(d.Id) && d.Location.IsInSource)
            .Select(d => d.Location.SourceTree!.GetText().ToString(d.Location.SourceSpan))
            .Distinct(StringComparer.Ordinal)
            .OrderBy(n => n, StringComparer.Ordinal)
            .ToList();
    }

    /// <summary>The names the compiler could not find, as written in the source, sorted ordinally and without repeats.</summary>
    public IReadOnlyList<string> MissingSymbols { get; }

    /// <summary>Every compiler error, in the compiler's order; empty when only a generator problem failed the compilation.</summary>
    public IReadOnlyList<Diagnostic> Errors { get; }

    /// <summary>Why a source generator could not run: it failed to load, or it threw.</summary>
    public IReadOnlyList<string> GeneratorProblems { get; }

    /// <summary>A message for people: the missing symbols, or the first error when no name is missing, then any generator problem.</summary>
    public string Message
    {
        get
        {
            var parts = new List<string>();
            if (MissingSymbols.Count > 0)
            {
                parts.Add("The compilation does not compile; missing: " + string.Join(", ", MissingSymbols) + ".");
            }
            else if (Errors.Count > 0)
            {
                parts.Add("The compilation does not compile: " + Errors[0].GetMessage(CultureInfo.InvariantCulture));
            }
            if (GeneratorProblems.Count > 0)
            {
                parts.Add("A source generator did not run, so the compilation may differ from the compiler's: " + string.Join("; ", GeneratorProblems));
            }
            return string.Join(" ", parts);
        }
    }
}
