using System.Collections.Concurrent;
using System.Collections.Immutable;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.Diagnostics;
using Microsoft.CodeAnalysis.Text;
using Warrant.Extraction;
using Warrant.Vir;

namespace Warrant.Analyzers;

/// <summary>
/// Reports extraction's diagnostics while the developer types (M5b R18, KTD22, docs/m5b/06): WRT0002 to WRT0005 and
/// WRT0009 for each <c>[Verified]</c> member, <c>[Theorem]</c>, <c>[ProofFor]</c> method, <c>[Closed]</c> type and
/// <c>[ContractFor]</c> class (whose contract class is read only from the compilation being analysed, as the build reads it), and WRT0008 for the
/// compilation. It runs the extractor's own rules through <see cref="Diagnoser"/>, so it reports what the build
/// reports, at the same place. It does no I/O and never reports proof results.
/// </summary>
/// <remarks>
/// The <c>Warrant</c> package removes this analyzer from builds that are not design-time builds (KTD23), so the
/// <c>warrant</c> CLI stays the one reporter in a build and an error here never stops the build before verification.
/// </remarks>
[DiagnosticAnalyzer(LanguageNames.CSharp)]
public sealed class WarrantAnalyzer : DiagnosticAnalyzer
{
    private const string Category = "Warrant";

    private const string HelpLink = "https://github.com/icosahedron/csharp-ansatz/blob/claude/ansatz-csharp-design-00846r/docs/proving/reference.md#diagnostics";

    /// <summary>WRT0002: a construct outside the supported subset.</summary>
    public static readonly DiagnosticDescriptor Unsupported = Error(DiagnosticIds.Unsupported, "Construct outside the supported subset");

    /// <summary>WRT0003: a call to a <c>[Theorem]</c>.</summary>
    public static readonly DiagnosticDescriptor CallsTheorem = Error(DiagnosticIds.CallsTheorem, "Call to a theorem");

    /// <summary>WRT0004: a malformed specification or proof script.</summary>
    public static readonly DiagnosticDescriptor MalformedSpec = Error(DiagnosticIds.MalformedSpec, "Malformed specification");

    /// <summary>WRT0005: a call to a member that is neither verified nor modelled.</summary>
    public static readonly DiagnosticDescriptor NotVerified = Error(DiagnosticIds.NotVerified, "Call to a member that is not verified");

    /// <summary>WRT0008: a way an unnamed value can reach a <c>[Closed]</c> enum; a property of the whole compilation.</summary>
    public static readonly DiagnosticDescriptor UnnamedClosedValue = new(
        DiagnosticIds.UnnamedClosedValue, "A [Closed] enum can hold an unnamed value", "{0}", Category, DiagnosticSeverity.Warning,
        isEnabledByDefault: true, helpLinkUri: HelpLink, customTags: WellKnownDiagnosticTags.CompilationEnd);

    /// <summary>WRT0009: a <c>[Closed]</c> class without the closed shape.</summary>
    public static readonly DiagnosticDescriptor NotClosedShape = Error(DiagnosticIds.NotClosedShape, "[Closed] class without the closed shape");

    private static readonly ImmutableDictionary<string, DiagnosticDescriptor> ById =
        new[] { Unsupported, CallsTheorem, MalformedSpec, NotVerified, UnnamedClosedValue, NotClosedShape }.ToImmutableDictionary(d => d.Id);

    /// <inheritdoc/>
    public override ImmutableArray<DiagnosticDescriptor> SupportedDiagnostics { get; } =
        ImmutableArray.Create(Unsupported, CallsTheorem, MalformedSpec, NotVerified, UnnamedClosedValue, NotClosedShape);

    private static DiagnosticDescriptor Error(string id, string title) =>
        new(id, title, "{0}", Category, DiagnosticSeverity.Error, isEnabledByDefault: true, helpLinkUri: HelpLink);

    /// <inheritdoc/>
    public override void Initialize(AnalysisContext context)
    {
        if (context is null)
        {
            throw new ArgumentNullException(nameof(context));
        }
        context.EnableConcurrentExecution();
        context.ConfigureGeneratedCodeAnalysis(GeneratedCodeAnalysisFlags.None);
        context.RegisterCompilationStartAction(start =>
        {
            // Nothing to check in a compilation that cannot use Warrant's attributes.
            if (start.Compilation is not CSharpCompilation compilation || compilation.GetTypeByMetadataName("Warrant.VerifiedAttribute") is null)
            {
                return;
            }
            var session = new Session(compilation);
            start.RegisterSymbolAction(session.AnalyzeSymbol, SymbolKind.Method, SymbolKind.Property, SymbolKind.NamedType);
            start.RegisterCompilationEndAction(session.AnalyzeCompilation);
        });
    }

    /// <summary>
    /// One compilation's analysis. A diagnostic about a record or enum is found through every member that uses it; it is
    /// reported once, whichever member gets there first, so the set reported is the same on every run.
    /// </summary>
    private sealed class Session
    {
        private readonly CSharpCompilation _compilation;
        private readonly Diagnoser _diagnoser;
        private readonly ConcurrentDictionary<ExtractionDiagnostic, byte> _reported = new();
        private readonly Lazy<ImmutableDictionary<string, SyntaxTree>> _trees;

        public Session(CSharpCompilation compilation)
        {
            _compilation = compilation;
            _diagnoser = new Diagnoser(compilation);
            _trees = new Lazy<ImmutableDictionary<string, SyntaxTree>>(
                () => compilation.SyntaxTrees.GroupBy(t => t.FilePath, StringComparer.Ordinal).ToImmutableDictionary(g => g.Key, g => g.First(), StringComparer.Ordinal),
                LazyThreadSafetyMode.ExecutionAndPublication);
        }

        public void AnalyzeSymbol(SymbolAnalysisContext context)
        {
            var symbol = context.Symbol;
            IReadOnlyList<ExtractionDiagnostic> diagnostics = symbol switch
            {
                INamedTypeSymbol type => [
                    .. Diagnoser.IsClosed(type) ? _diagnoser.ClosedType(type, context.CancellationToken) : [],
                    .. Diagnoser.IsContractClass(type) ? _diagnoser.ContractClass(type, context.CancellationToken) : [],
                ],
                _ when Diagnoser.IsAttributed(symbol) => _diagnoser.Member(symbol, context.CancellationToken),
                _ => [],
            };
            foreach (var d in diagnostics)
            {
                if (_reported.TryAdd(d, 0) && ToRoslyn(d) is { } diagnostic)
                {
                    context.ReportDiagnostic(diagnostic);
                }
            }
        }

        public void AnalyzeCompilation(CompilationAnalysisContext context)
        {
            foreach (var d in _diagnoser.UnnamedClosedValues())
            {
                if (ToRoslyn(d) is { } diagnostic)
                {
                    context.ReportDiagnostic(diagnostic);
                }
            }
        }

        private Diagnostic? ToRoslyn(ExtractionDiagnostic d) =>
            ById.TryGetValue(d.Id, out var descriptor) ? Diagnostic.Create(descriptor, ToLocation(d.Location), d.Message) : null;

        /// <summary>The source location a span names: extraction's spans are a tree's path and 1-based lines and columns.</summary>
        private Location ToLocation(VirSpan? span)
        {
            if (span is null || !_trees.Value.TryGetValue(span.Path, out var tree))
            {
                return Location.None;
            }
            var lines = tree.GetText().Lines;
            int start = Position(lines, span.StartLine, span.StartColumn);
            int end = Position(lines, span.EndLine, span.EndColumn);
            return Location.Create(tree, TextSpan.FromBounds(start, Math.Max(start, end)));
        }

        private static int Position(TextLineCollection lines, int line, int column)
        {
            int index = Math.Min(Math.Max(line - 1, 0), lines.Count - 1);
            var text = lines[index];
            return Math.Min(text.Start + Math.Max(column - 1, 0), text.EndIncludingLineBreak);
        }
    }
}
