using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;

namespace Warrant.Extraction;

/// <summary>
/// Diagnostics-only extraction (M5b KTD22, docs/m5b/06): the subset checks of <see cref="Extractor.Extract(CSharpCompilation, CancellationToken)"/>
/// for one member or type at a time, quickly enough for an analyzer to run per keystroke. It runs the same rule code as a
/// full extraction, on the member and everything it reaches, so the IDE and the build agree, but it never asks the
/// compilation for all its errors and never re-parses it for <c>#if</c> combinations. One instance serves one compilation
/// and is thread-safe; the scan of the whole compilation that the closed shape and WRT0008 need is made once, when first
/// needed.
/// </summary>
/// <remarks>
/// What a full extraction reports that this does not: the compilation's own errors, and the check that a member
/// translates the same under every <c>#if</c> combination. A member whose own declaration has a compiler error gets no
/// diagnostics here, because the compiler already reports what is wrong with it.
/// </remarks>
public sealed class Diagnoser
{
    private readonly CSharpCompilation _compilation;
    private readonly Lazy<List<INamedTypeSymbol>> _types;
    private readonly Lazy<Dictionary<string, ISymbol>> _attributed;
    private readonly Lazy<CompilationScan> _scan;

    /// <summary>Creates the diagnoser for a compilation.</summary>
    /// <param name="compilation">The compilation.</param>
    public Diagnoser(CSharpCompilation compilation)
    {
        _compilation = compilation ?? throw new ArgumentNullException(nameof(compilation));
        _types = new Lazy<List<INamedTypeSymbol>>(() => Extractor.Run.SortedSourceTypes(compilation), LazyThreadSafetyMode.ExecutionAndPublication);
        _attributed = new Lazy<Dictionary<string, ISymbol>>(
            () => Extractor.Run.AttributedMembers(_types.Value).ToDictionary(Symbols.Key, m => m, StringComparer.Ordinal),
            LazyThreadSafetyMode.ExecutionAndPublication);
        _scan = new Lazy<CompilationScan>(
            () => CompilationScan.Run(new ExtractionContext(compilation, Extractor.Run.Facts(compilation)), CancellationToken.None),
            LazyThreadSafetyMode.ExecutionAndPublication);
    }

    /// <summary>The compilation's <c>[Verified]</c> members and <c>[Theorem]</c>s, by key.</summary>
    public IEnumerable<ISymbol> Members() => _attributed.Value.Values.OrderBy(Symbols.Key, StringComparer.Ordinal);

    /// <summary>The compilation's <c>[Closed]</c> types, by key.</summary>
    public IEnumerable<INamedTypeSymbol> ClosedTypes() => _types.Value.Where(Symbols.IsClosed);

    /// <summary>Whether a symbol is one <see cref="Member"/> diagnoses: a <c>[Verified]</c> member or a <c>[Theorem]</c>.</summary>
    public static bool IsAttributed(ISymbol symbol) =>
        symbol is IMethodSymbol { MethodKind: not MethodKind.PropertyGet and not MethodKind.PropertySet } or IPropertySymbol
        && (Symbols.IsVerified(symbol) || Symbols.IsTheorem(symbol));

    /// <summary>Whether a type is one <see cref="ClosedType"/> diagnoses: one marked <c>[Closed]</c>.</summary>
    public static bool IsClosed(INamedTypeSymbol type) => Symbols.IsClosed(type);

    /// <summary>The key a diagnostic about this member or type carries in <see cref="ExtractionDiagnostic.MemberKey"/>.</summary>
    public static string Key(ISymbol symbol) => Symbols.Key(symbol);

    /// <summary>
    /// The diagnostics about a <c>[Verified]</c> member or <c>[Theorem]</c>, and about the records, enums and closed types
    /// it reaches, as a full extraction reports them; not those about the other members it calls, which are theirs.
    /// </summary>
    /// <param name="member">The member.</param>
    /// <param name="cancellationToken">Cancels the check.</param>
    /// <returns>The diagnostics, sorted as <see cref="ExtractionResult.Diagnostics"/> is.</returns>
    public IReadOnlyList<ExtractionDiagnostic> Member(ISymbol member, CancellationToken cancellationToken = default)
    {
        if (member is null)
        {
            throw new ArgumentNullException(nameof(member));
        }
        if (!IsAttributed(member) || HasCompileErrors(member, cancellationToken))
        {
            return [];
        }
        var key = Symbols.Key(member);
        var diagnostics = new Extractor.Run(_compilation, cancellationToken, _scan, deferReferenced: true).ExecuteFor(member, _attributed.Value);
        var types = new HashSet<string>(diagnostics.Select(d => d.MemberKey).Where(k => k is not null && !_attributed.Value.ContainsKey(k))!, StringComparer.Ordinal);
        return diagnostics.Where(d => d.MemberKey == key || (d.MemberKey is not null && types.Contains(d.MemberKey))).ToList();
    }

    /// <summary>The diagnostics about a <c>[Closed]</c> type's shape, which a full extraction reports whether or not the type is used.</summary>
    /// <param name="type">The type.</param>
    /// <param name="cancellationToken">Cancels the check.</param>
    /// <returns>The diagnostics.</returns>
    public IReadOnlyList<ExtractionDiagnostic> ClosedType(INamedTypeSymbol type, CancellationToken cancellationToken = default)
    {
        if (type is null)
        {
            throw new ArgumentNullException(nameof(type));
        }
        if (!Symbols.IsClosed(type))
        {
            return [];
        }
        var key = Symbols.Key(type);
        return new Extractor.Run(_compilation, cancellationToken, _scan, deferReferenced: true).ExecuteFor(type, _attributed.Value)
            .Where(d => d.MemberKey == key)
            .ToList();
    }

    /// <summary>WRT0008, a property of the whole compilation: every way an unnamed value can reach a <c>[Closed]</c> enum.</summary>
    /// <returns>The warnings, sorted as <see cref="ExtractionResult.Diagnostics"/> is.</returns>
    public IReadOnlyList<ExtractionDiagnostic> UnnamedClosedValues() => Extractor.Sorted(Extractor.Run.UnnamedClosedValues(_scan.Value, _types.Value).ToList());

    private bool HasCompileErrors(ISymbol member, CancellationToken cancellationToken)
    {
        foreach (var reference in member.DeclaringSyntaxReferences)
        {
            var model = _compilation.GetSemanticModel(reference.SyntaxTree);
            if (model.GetDiagnostics(reference.Span, cancellationToken).Any(d => d.Severity == DiagnosticSeverity.Error))
            {
                return true;
            }
        }
        return false;
    }
}
