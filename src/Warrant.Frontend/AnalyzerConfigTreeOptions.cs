using Microsoft.CodeAnalysis;

namespace Warrant.Frontend;

/// <summary>
/// The per-tree options Csc derives from <c>/analyzerconfig:</c> files: diagnostic severities and <c>generated_code</c>.
/// Trees are found by path, so a tree parsed again (extraction's <c>#if</c> combinations) keeps its options.
/// </summary>
internal sealed class AnalyzerConfigTreeOptions(AnalyzerConfigOptionsResult global, Dictionary<string, AnalyzerConfigOptionsResult> trees)
    : SyntaxTreeOptionsProvider
{
    public override GeneratedKind IsGenerated(SyntaxTree tree, CancellationToken cancellationToken) =>
        trees.TryGetValue(tree.FilePath, out var options) && options.AnalyzerOptions.TryGetValue("generated_code", out var value)
            ? bool.TryParse(value, out var generated) ? (generated ? GeneratedKind.MarkedGenerated : GeneratedKind.NotGenerated) : GeneratedKind.Unknown
            : GeneratedKind.Unknown;

    public override bool TryGetDiagnosticValue(SyntaxTree tree, string diagnosticId, CancellationToken cancellationToken, out ReportDiagnostic severity)
    {
        if (trees.TryGetValue(tree.FilePath, out var options) && options.TreeOptions.TryGetValue(diagnosticId, out severity))
        {
            return true;
        }
        severity = ReportDiagnostic.Default;
        return false;
    }

    public override bool TryGetGlobalDiagnosticValue(string diagnosticId, CancellationToken cancellationToken, out ReportDiagnostic severity) =>
        global.TreeOptions.TryGetValue(diagnosticId, out severity);
}
