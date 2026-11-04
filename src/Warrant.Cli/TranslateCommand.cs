using System.Globalization;
using Microsoft.CodeAnalysis;
using Warrant.Engine;
using Warrant.Engine.Reports;
using Warrant.Extraction;
using Warrant.Frontend;
using Warrant.Lean4Export;
using Warrant.Vir;

/// <summary>
/// <c>warrant translate</c> (docs/m4/07, KTD16): compiles a directory of C#, extracts VIR, runs the engine, and prints
/// one line per member plus diagnostics in the compiler's format. The CLI is only the Roslyn front end and file I/O;
/// everything after VIR is the engine.
/// </summary>
internal static class TranslateCommand
{
    public const string Usage = "warrant translate <directory> [--out <file.ndjson>] [--report <file.md>] [--check-overflow] [--bundle <path>]";

    /// <summary>Runs the verb.</summary>
    /// <param name="args">The arguments after <c>translate</c>.</param>
    /// <param name="output">Where member lines, diagnostics and the summary go.</param>
    /// <param name="error">Where usage errors and declines go.</param>
    /// <returns>
    /// 0 when every member translated and every theorem was proved; 1 when anything was rejected, false, unproved, undecided, an internal error, failed
    /// or skipped, or the compilation has errors; 2 for bad arguments or unreadable input.
    /// </returns>
    public static int Run(string[] args, TextWriter output, TextWriter error)
    {
        string? directory = null, outPath = null, reportPath = null, bundlePath = null;
        bool checkOverflow = false;
        for (int i = 0; i < args.Length; i++)
        {
            switch (args[i])
            {
                case "--out" when i + 1 < args.Length:
                    outPath = args[++i];
                    break;
                case "--report" when i + 1 < args.Length:
                    reportPath = args[++i];
                    break;
                case "--bundle" when i + 1 < args.Length:
                    bundlePath = args[++i];
                    break;
                case "--check-overflow":
                    checkOverflow = true;
                    break;
                case var a when directory is null && !a.StartsWith("--", StringComparison.Ordinal):
                    directory = a;
                    break;
                default:
                    error.WriteLine($"unknown option '{args[i]}'{Environment.NewLine}usage: {Usage}");
                    return 2;
            }
        }
        if (directory is null)
        {
            error.WriteLine($"usage: {Usage}");
            return 2;
        }
        if (!Directory.Exists(directory))
        {
            error.WriteLine($"declined: directory '{directory}' not found");
            return 2;
        }
        bundlePath ??= Path.Combine(AppDirectory(), SemanticsBundle.FileName);
        if (!File.Exists(bundlePath))
        {
            error.WriteLine($"declined: semantics bundle '{bundlePath}' not found");
            return 2;
        }

        try
        {
            return Translate(directory, outPath, reportPath, bundlePath, checkOverflow, output);
        }
        catch (Exception ex) when (ex is Lean4ExportFormatException or InvalidDataException or IOException or UnauthorizedAccessException)
        {
            error.WriteLine($"declined: {ex.Message}");
            return 2;
        }
    }

    private static int Translate(string directory, string? outPath, string? reportPath, string bundlePath, bool checkOverflow, TextWriter output)
    {
        var root = Path.GetFullPath(directory);
        var files = SourceFiles(root);
        var sources = new Sources(directory, root);
        output.WriteLine($"translating {files.Count} file(s) in {directory}");

        var compilation = CompilationFactory.FromFiles(root, files, checkOverflow);
        var extraction = Extractor.Extract(compilation);
        if (extraction.HasCompileErrors)
        {
            foreach (var d in extraction.Diagnostics)
            {
                output.WriteLine(sources.Format(d.Location, Severity(d.Severity), d.Id, d.Message));
            }
            output.WriteLine("the compilation has errors; nothing was translated");
            return 1;
        }

        var bundle = SemanticsBundle.Load(bundlePath);
        var inputs = extraction.Units.Select(u => new EngineUnit(u.Unit, u.DisplayName, u.Spans)).ToList();
        var result = Pipeline.Run(inputs, bundle);

        int width = result.Units.Select(u => u.DisplayName.Length).DefaultIfEmpty(0).Max();
        foreach (var unit in result.Units)
        {
            output.WriteLine($"  {unit.DisplayName.PadRight(width)}  {Describe(unit)}");
        }

        int errors = 0, warnings = 0;
        foreach (var d in extraction.Diagnostics)
        {
            if (d.Severity == ExtractionSeverity.Error)
            {
                errors++;
            }
            else
            {
                warnings++;
            }
            output.WriteLine(sources.Format(d.Location, Severity(d.Severity), d.Id, d.Message));
        }
        var units = extraction.Units.ToDictionary(u => u.Key, StringComparer.Ordinal);
        var engineUnits = inputs.ToDictionary(u => u.Unit.Key, StringComparer.Ordinal);
        foreach (var unit in result.Units)
        {
            var location = units.TryGetValue(unit.Key, out var extracted) ? extracted.Location : null;
            var theorem = MessageName(compilation, unit);
            switch (unit)
            {
                case FalseOutcome f:
                    errors++;
                    output.WriteLine(sources.Format(location, "error", FalseOutcome.Code, OutcomeText.FalseMessage(theorem)));
                    if (AssumptionReports.ClaimSpan(engineUnits[unit.Key]) is { } claimSpan && sources.Text(claimSpan) is { } claim)
                    {
                        output.WriteLine($"  Claim:  {claim}");
                    }
                    if (f.Sides.Length > 0)
                    {
                        output.WriteLine($"  Values: {OutcomeText.Values(f.Sides, sources.Text)}");
                    }
                    break;
                case NotProvedOutcome n:
                    errors++;
                    output.WriteLine(sources.Format(n.TacticSpan ?? location, "error", NotProvedOutcome.Code, OutcomeText.NotProvedMessage(theorem, n, sources.Text)));
                    foreach (var line in OutcomeText.NotProvedDetails(n))
                    {
                        output.WriteLine(line.Length == 0 ? "" : $"  {line}");
                    }
                    break;
                case UndecidedOutcome u:
                    errors++;
                    output.WriteLine(sources.Format(location, "error", UndecidedOutcome.Code, OutcomeText.UndecidedMessage(theorem, u.Reason)));
                    break;
                case InternalErrorOutcome i:
                    errors++;
                    output.WriteLine(sources.Format(location, "error", InternalErrorOutcome.Code, OutcomeText.InternalErrorMessage(theorem, i.Reason)));
                    break;
            }
        }

        if (outPath is not null)
        {
            using var stream = File.Create(outPath);
            result.WriteNdjson(stream);
            output.WriteLine($"wrote the bundle and {result.Admitted.Length} admitted declaration(s) to {outPath}");
        }
        if (reportPath is not null)
        {
            var settings = new ReportSettings(checkOverflow, OutcomeText.BundleName(bundlePath));
            File.WriteAllText(reportPath, MarkdownReport.Render(AssumptionReports.Build(result, inputs, settings, sources.Text)));
            output.WriteLine($"wrote the assumption report to {reportPath}");
        }

        var counts = result.Units.GroupBy(AssumptionReports.OutcomeName).ToDictionary(g => g.Key, g => g.Count(), StringComparer.Ordinal);
        int Count(string outcome) => counts.TryGetValue(outcome, out var n) ? n : 0;
        output.WriteLine(string.Create(
            CultureInfo.InvariantCulture,
            $"{result.Units.Length} unit(s): {Count("translated")} translated, {Count("proved")} proved, {Count("false")} false, "
            + $"{Count("unproved")} unproved, {Count("undecided")} undecided, {Count("internal")} internal error(s), "
            + $"{Count("failed")} failed, {Count("skipped")} skipped; {errors} error(s), {warnings} warning(s)"));

        bool clean = extraction.Diagnostics.All(d => d.Severity != ExtractionSeverity.Error)
            && result.Units.All(u => u is TranslatedOutcome or ProvedOutcome);
        return clean ? 0 : 1;
    }

    /// <summary>
    /// A unit's name as diagnostics print it (docs/m5a/04): the C# display name with containing types and parameter types
    /// but no namespace, e.g. <c>Increments.AlwaysLarger(int)</c>; the short name when the symbol cannot be found.
    /// </summary>
    internal static string MessageName(Compilation compilation, UnitOutcome unit) =>
        DocumentationCommentId.GetFirstSymbolForDeclarationId(unit.Key, compilation) is { } symbol
            ? symbol.ToDisplayString(MessageNameFormat)
            : OutcomeText.ShortName(unit.DisplayName);

    private static readonly SymbolDisplayFormat MessageNameFormat =
        new(
            globalNamespaceStyle: SymbolDisplayGlobalNamespaceStyle.Omitted,
            typeQualificationStyle: SymbolDisplayTypeQualificationStyle.NameAndContainingTypes,
            genericsOptions: SymbolDisplayGenericsOptions.IncludeTypeParameters,
            memberOptions: SymbolDisplayMemberOptions.IncludeParameters | SymbolDisplayMemberOptions.IncludeContainingType
                | SymbolDisplayMemberOptions.IncludeExplicitInterface,
            parameterOptions: SymbolDisplayParameterOptions.IncludeType | SymbolDisplayParameterOptions.IncludeParamsRefOut,
            miscellaneousOptions: SymbolDisplayMiscellaneousOptions.UseSpecialTypes | SymbolDisplayMiscellaneousOptions.EscapeKeywordIdentifiers);

    internal static string Describe(UnitOutcome unit) => unit switch
    {
        ProvedOutcome p => $"proved ({AssumptionReports.ProofName(p.By)})",
        FailedOutcome f => $"failed: {f.Reason}",
        SkippedOutcome s => $"skipped: {s.Reason}",
        _ => AssumptionReports.OutcomeName(unit),
    };

    /// <summary>Every .cs file under the root, as '/'-separated paths relative to it, in ordinal order.</summary>
    internal static List<string> SourceFiles(string root) =>
        Directory.EnumerateFiles(root, "*.cs", SearchOption.AllDirectories)
            .Select(f => Path.GetRelativePath(root, f).Replace('\\', '/'))
            .Order(StringComparer.Ordinal)
            .ToList();

    internal static string Severity(ExtractionSeverity severity) => severity == ExtractionSeverity.Error ? "error" : "warning";

    internal static string AppDirectory() =>
        Path.GetDirectoryName(typeof(TranslateCommand).Assembly.Location) is { Length: > 0 } dir ? dir : AppContext.BaseDirectory;

    /// <summary>The source files on disk, for diagnostic paths and the text of spans.</summary>
    internal sealed class Sources(string directory, string root)
    {
        private readonly Dictionary<string, string[]?> _lines = new(StringComparer.Ordinal);

        public string Format(VirSpan? location, string severity, string id, string message) =>
            location is null
                ? $"{severity} {id}: {message}"
                : string.Create(CultureInfo.InvariantCulture, $"{FilePath(location.Path)}({location.StartLine},{location.StartColumn}): {severity} {id}: {message}");

        /// <summary>A source path under the directory as the user named it, in the separator style they used.</summary>
        public string FilePath(string relative)
        {
            var separator = directory.Contains('\\', StringComparison.Ordinal) ? '\\' : '/';
            return directory.TrimEnd('/', '\\') + separator + relative.Replace('/', separator);
        }

        /// <summary>The source text of a span, with runs of whitespace across lines collapsed; null if unreadable.</summary>
        public string? Text(VirSpan span)
        {
            if (!_lines.TryGetValue(span.Path, out var lines))
            {
                var path = Path.Combine(root, span.Path);
                lines = File.Exists(path) ? File.ReadAllLines(path) : null;
                _lines.Add(span.Path, lines);
            }
            if (lines is null || span.StartLine < 1 || span.EndLine > lines.Length || span.StartLine > span.EndLine)
            {
                return null;
            }
            var parts = new List<string>();
            for (int line = span.StartLine; line <= span.EndLine; line++)
            {
                var text = lines[line - 1];
                int start = line == span.StartLine ? span.StartColumn - 1 : 0;
                int end = line == span.EndLine ? span.EndColumn - 1 : text.Length;
                if (start < 0 || end > text.Length || start > end)
                {
                    return null;
                }
                parts.Add(text[start..end].Trim());
            }
            return string.Join(" ", parts.Where(p => p.Length > 0));
        }
    }
}
