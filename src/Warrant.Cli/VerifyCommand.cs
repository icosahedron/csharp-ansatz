using System.Globalization;
using System.Text;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Warrant.Engine;
using Warrant.Engine.Reports;
using Warrant.Extraction;
using Warrant.Frontend;
using Warrant.Kernel;
using Warrant.Lean4Export;
using Warrant.Meta;
using Warrant.Vir;

/// <summary>
/// <c>warrant verify</c> (plan M5a U12, KTD20, KTD21, KTD24; docs/m5a/07): builds the compilation from the compiler's own
/// arguments, or like <c>translate</c> from a directory, then extracts, translates, proves and reports in-process. With
/// <c>--format msbuild</c> each diagnostic is one <c>WRT1</c> record (the format <c>Warrant.Build</c>'s
/// <c>OutputParser</c> reads), so a multi-line goal stays one MSBuild event.
/// </summary>
internal static class VerifyCommand
{
    public const string Usage = """
        warrant verify --csc-args <file> [--project-dir <dir>] [options]
               warrant verify <directory> [options]
          options: --format text|msbuild  --out <file.ndjson>  --report <dir>  --keep-conditional-check
                   --kernel-fuel <n>  --tactic-fuel <n>  --timeout <seconds>  --bundle <path>
        """;

    /// <summary>The attribute sidecar's file name; it ships beside the semantics bundle (KTD9).</summary>
    public const string SidecarFileName = "warrant-attributes.ndjson.gz";

    /// <summary>Runs the verb.</summary>
    /// <param name="args">The arguments after <c>verify</c>.</param>
    /// <param name="output">Where unit lines, diagnostics (or records) and the summary go.</param>
    /// <param name="error">Where usage errors and declines go.</param>
    /// <returns>0 when every theorem was proved (warnings allowed); 1 when an error was reported; 2 for bad arguments or unreadable input.</returns>
    public static int Run(string[] args, TextWriter output, TextWriter error)
    {
        string? directory = null, cscArgs = null, projectDir = null, outPath = null, reportDir = null, bundlePath = null;
        bool msbuild = false, keepConditionalCheck = false;
        long? kernelFuel = null, tacticFuel = null, timeoutSeconds = null;
        for (int i = 0; i < args.Length; i++)
        {
            bool hasValue = i + 1 < args.Length;
            switch (args[i])
            {
                case "--csc-args" when hasValue:
                    cscArgs = args[++i];
                    break;
                case "--project-dir" when hasValue:
                    projectDir = args[++i];
                    break;
                case "--format" when hasValue && args[i + 1] is "text" or "msbuild":
                    msbuild = args[++i] == "msbuild";
                    break;
                case "--out" when hasValue:
                    outPath = args[++i];
                    break;
                case "--report" when hasValue:
                    reportDir = args[++i];
                    break;
                case "--bundle" when hasValue:
                    bundlePath = args[++i];
                    break;
                case "--keep-conditional-check":
                    keepConditionalCheck = true;
                    break;
                case "--kernel-fuel" when hasValue && Count(args[i + 1]) is { } n:
                    kernelFuel = n;
                    i++;
                    break;
                case "--tactic-fuel" when hasValue && Count(args[i + 1]) is { } n:
                    tacticFuel = n;
                    i++;
                    break;
                case "--timeout" when hasValue && Count(args[i + 1]) is { } n:
                    timeoutSeconds = n;
                    i++;
                    break;
                case var a when directory is null && !a.StartsWith("--", StringComparison.Ordinal):
                    directory = a;
                    break;
                default:
                    error.WriteLine($"unknown or incomplete option '{args[i]}'{Environment.NewLine}usage: {Usage}");
                    return 2;
            }
        }
        if ((directory is null) == (cscArgs is null) || (projectDir is not null && cscArgs is null))
        {
            error.WriteLine($"usage: {Usage}");
            return 2;
        }
        if (cscArgs is not null && !File.Exists(cscArgs))
        {
            error.WriteLine($"declined: argument file '{cscArgs}' not found");
            return 2;
        }
        if (directory is not null && !Directory.Exists(directory))
        {
            error.WriteLine($"declined: directory '{directory}' not found");
            return 2;
        }
        bundlePath ??= Path.Combine(TranslateCommand.AppDirectory(), SemanticsBundle.FileName);
        if (!File.Exists(bundlePath))
        {
            error.WriteLine($"declined: semantics bundle '{bundlePath}' not found");
            return 2;
        }
        var sidecarPath = Path.Combine(Path.GetDirectoryName(Path.GetFullPath(bundlePath))!, SidecarFileName);
        if (!File.Exists(sidecarPath))
        {
            error.WriteLine($"declined: attribute sidecar '{sidecarPath}' not found; it ships beside the semantics bundle");
            return 2;
        }

        try
        {
            // The sidecar first: it names the bundle it was made for, so a mismatched pair is declined before the slow load.
            var sidecar = Sidecar.Load(sidecarPath, OutcomeText.FileSha256(bundlePath));
            var settings = new Settings(msbuild, outPath, reportDir, bundlePath, sidecar, kernelFuel, tacticFuel, timeoutSeconds);
            return cscArgs is not null
                ? FromCscArgs(cscArgs, projectDir ?? Environment.CurrentDirectory, keepConditionalCheck, settings, output)
                : FromDirectory(directory!, settings, output);
        }
        catch (Exception ex) when (ex is SidecarFormatException or Lean4ExportFormatException or InvalidDataException or IOException or UnauthorizedAccessException)
        {
            error.WriteLine($"declined: {ex.Message}");
            return 2;
        }
    }

    private sealed record Settings(
        bool Msbuild, string? OutPath, string? ReportDir, string BundlePath, Sidecar Sidecar, long? KernelFuel, long? TacticFuel, long? TimeoutSeconds)
    {
        /// <summary>The budgets: the given ones, else the build's defaults (corpus kernel fuel for the directory mode, like translate).</summary>
        public EngineOptions Engine(KernelLimits kernel) => EngineOptions.Default with
        {
            Kernel = KernelFuel is { } fuel ? kernel with { Fuel = fuel } : kernel,
            TacticFuel = TacticFuel ?? EngineOptions.DefaultTacticFuel,
            Timeout = TimeoutSeconds is { } seconds ? TimeSpan.FromSeconds(seconds) : EngineOptions.Default.Timeout,
            Attributes = Sidecar,
        };
    }

    private static int FromCscArgs(string argsFile, string projectDir, bool keepConditionalCheck, Settings settings, TextWriter output)
    {
        var root = Path.GetFullPath(projectDir);
        var compilation = CompilationFactory.FromCscArgs(argsFile, root, out var generatorProblems);
        var report = new Reporter(output, settings.Msbuild, new TranslateCommand.Sources(root, root));
        report.Line($"verifying {compilation.SyntaxTrees.Length} file(s) from {argsFile}");
        if (CompilationFactory.Failure(compilation, generatorProblems) is { } failure)
        {
            // A generator problem with no compile error has no source location of its own.
            var at = failure.Errors.FirstOrDefault(e => failure.MissingSymbols.Count > 0 && e.Location.IsInSource
                    && failure.MissingSymbols.Contains(e.Location.SourceTree!.GetText().ToString(e.Location.SourceSpan), StringComparer.Ordinal))
                ?? (failure.Errors.Count > 0 ? failure.Errors[0] : null);
            var details = failure.Errors.Select(e => report.Format(Span(e.Location), "error", e.Id, e.GetMessage(CultureInfo.InvariantCulture))).ToList();
            report.Diagnostic("error", CompilationFailure.Code, Span(at?.Location ?? Location.None), failure.Message, details);
            report.Summary(0, 0, 0);
            return 1;
        }
        var intercepted = CompilationFactory.InterceptedCalls(compilation);
        foreach (var (location, interceptor) in intercepted)
        {
            report.Diagnostic("error", "WRT0002", Span(location),
                $"Unsupported construct 'intercepted call': a source generator replaces this call with '{interceptor.ToDisplayString()}', which Warrant does not model.");
        }
        if (intercepted.Count > 0)
        {
            report.Summary(0, 0, 0);
            return 1;
        }
        var extraction = Extractor.Extract(compilation, new ExtractionOptions { BuildDefines = true, KeepConditionalCheck = keepConditionalCheck });
        return Verify(compilation, extraction, settings, settings.Engine(KernelLimits.Interactive), report);
    }

    private static int FromDirectory(string directory, Settings settings, TextWriter output)
    {
        var root = Path.GetFullPath(directory);
        var files = TranslateCommand.SourceFiles(root);
        var report = new Reporter(output, settings.Msbuild, new TranslateCommand.Sources(directory, root));
        report.Line($"verifying {files.Count} file(s) in {directory}");
        var compilation = CompilationFactory.FromFiles(root, files, checkOverflow: false);
        var extraction = Extractor.Extract(compilation);
        if (extraction.HasCompileErrors)
        {
            foreach (var d in extraction.Diagnostics)
            {
                report.Diagnostic(TranslateCommand.Severity(d.Severity), d.Id, d.Location, d.Message);
            }
            report.Summary(0, 0, 0);
            return 1;
        }
        return Verify(compilation, extraction, settings, settings.Engine(KernelLimits.Corpus), report);
    }

    private static int Verify(CSharpCompilation compilation, ExtractionResult extraction, Settings settings, EngineOptions options, Reporter report)
    {
        var bundle = SemanticsBundle.Load(settings.BundlePath);
        var inputs = extraction.Units.Select(u => new EngineUnit(u.Unit, u.DisplayName, u.Spans)).ToList();
        var result = Pipeline.Run(inputs, bundle, options);

        int width = result.Units.Select(u => u.DisplayName.Length).DefaultIfEmpty(0).Max();
        foreach (var unit in result.Units)
        {
            report.Line($"  {unit.DisplayName.PadRight(width)}  {TranslateCommand.Describe(unit)}");
        }

        foreach (var d in extraction.Diagnostics)
        {
            report.Diagnostic(TranslateCommand.Severity(d.Severity), d.Id, d.Location, d.Message);
        }
        var units = extraction.Units.ToDictionary(u => u.Key, StringComparer.Ordinal);
        var engineUnits = inputs.ToDictionary(u => u.Unit.Key, StringComparer.Ordinal);
        foreach (var unit in result.Units)
        {
            var location = units.TryGetValue(unit.Key, out var extracted) ? extracted.Location : null;
            var name = TranslateCommand.MessageName(compilation, unit);
            switch (unit)
            {
                case FalseOutcome f:
                    var lines = new List<string>();
                    if (AssumptionReports.ClaimSpan(engineUnits[unit.Key]) is { } claimSpan && report.Sources.Text(claimSpan) is { } claim)
                    {
                        lines.Add($"Claim:  {claim}");
                    }
                    if (f.Sides.Length > 0)
                    {
                        lines.Add($"Values: {OutcomeText.Values(f.Sides, engineUnits[unit.Key].Spans, report.Sources.Text)}");
                    }
                    report.Diagnostic("error", FalseOutcome.Code, location, OutcomeText.FalseMessage(name), lines);
                    break;
                case NotProvedOutcome n:
                    var spans = engineUnits[unit.Key].Spans;
                    report.Diagnostic(
                        "error", NotProvedOutcome.Code, OutcomeText.SpanOf(spans, n.TacticNode) ?? location,
                        OutcomeText.NotProvedMessage(name, n, spans, report.Sources.Text), OutcomeText.NotProvedDetails(n), n.Goals);
                    break;
                case UndecidedOutcome u:
                    report.Diagnostic("error", UndecidedOutcome.Code, location, OutcomeText.UndecidedMessage(name, u.Reason));
                    break;
                case InternalErrorOutcome i:
                    report.Diagnostic("error", InternalErrorOutcome.Code, location, OutcomeText.InternalErrorMessage(name, i.Reason));
                    break;
                case FailedOutcome f:
                    report.Diagnostic("error", InternalErrorOutcome.Code, location, OutcomeText.FailedMessage(name, f.Reason));
                    break;
            }
        }

        if (settings.OutPath is not null)
        {
            using var stream = File.Create(settings.OutPath);
            result.WriteNdjson(stream);
            report.Line($"wrote the bundle and {result.Admitted.Length} admitted declaration(s) to {settings.OutPath}");
        }
        if (settings.ReportDir is not null)
        {
            Directory.CreateDirectory(settings.ReportDir);
            var reportSettings = new ReportSettings(compilation.Options.CheckOverflow, OutcomeText.BundleName(settings.BundlePath));
            var assumptions = AssumptionReports.Build(result, inputs, reportSettings, report.Sources.Text);
            File.WriteAllText(Path.Combine(settings.ReportDir, "report.md"), MarkdownReport.Render(assumptions));
            File.WriteAllText(Path.Combine(settings.ReportDir, "report.json"), JsonReport.Render(assumptions));
            report.Line($"wrote report.md and report.json to {settings.ReportDir}");
        }

        var theorems = result.Units.Where(u => u.UnitKind == VirUnitKind.Theorem).ToList();
        int proved = theorems.Count(u => u is ProvedOutcome);
        report.Summary(result.Units.Length, proved, theorems.Count - proved);

        bool clean = report.Errors == 0 && result.Units.All(u => u is TranslatedOutcome or ProvedOutcome);
        return clean ? 0 : 1;
    }

    private static long? Count(string text) =>
        long.TryParse(text, NumberStyles.None, CultureInfo.InvariantCulture, out var n) ? n : null;

    /// <summary>A compiler diagnostic's location as a span; its path is the tree's, relative to the project directory.</summary>
    private static VirSpan? Span(Location location)
    {
        if (!location.IsInSource)
        {
            return null;
        }
        var span = location.GetLineSpan();
        return new VirSpan(span.Path, span.StartLinePosition.Line + 1, span.StartLinePosition.Character + 1, span.EndLinePosition.Line + 1, span.EndLinePosition.Character + 1);
    }

    /// <summary>
    /// Writes diagnostics and the summary as text (the compiler's format) or as <c>WRT1</c> records (KTD20): tab-separated
    /// kind, severity, code, file, line, column, end line, end column and message, with the message's backslashes,
    /// newlines, carriage returns and tabs escaped.
    /// </summary>
    private sealed class Reporter(TextWriter output, bool msbuild, TranslateCommand.Sources sources)
    {
        public TranslateCommand.Sources Sources => sources;

        public int Errors { get; private set; }

        public void Line(string text) => output.WriteLine(text);

        public string Format(VirSpan? at, string severity, string code, string message) => sources.Format(at, severity, code, message);

        /// <summary>One diagnostic: its first line is complete on its own; the details and, in records, the goal block follow.</summary>
        public void Diagnostic(string severity, string code, VirSpan? at, string message, IReadOnlyList<string>? details = null, string? goals = null)
        {
            if (severity == "error")
            {
                Errors++;
            }
            details ??= [];
            if (!msbuild)
            {
                output.WriteLine(sources.Format(at, severity, code, message));
                foreach (var line in details)
                {
                    output.WriteLine(line.Length == 0 ? "" : $"  {line}");
                }
                return;
            }
            var full = details.Count == 0 ? message : message + "\n" + string.Join("\n", details);
            Record("diag", severity, code, at, full);
            if (!string.IsNullOrEmpty(goals))
            {
                Record("goal", "info", "", null, goals);
            }
        }

        public void Summary(int units, int proved, int notProved)
        {
            var text = string.Create(CultureInfo.InvariantCulture, $"Warrant: {units} verified units, {proved} theorems proved, {notProved} not proved.");
            if (msbuild)
            {
                Record("summary", "info", "", null, text);
            }
            else
            {
                output.WriteLine(text);
            }
        }

        private void Record(string kind, string severity, string code, VirSpan? at, string message)
        {
            var file = at is null ? "" : sources.FilePath(at.Path);
            var position = at is null
                ? "0\t0\t0\t0"
                : string.Create(CultureInfo.InvariantCulture, $"{at.StartLine}\t{at.StartColumn}\t{at.EndLine}\t{at.EndColumn}");
            // Only the message is escaped; the file is the path as it stands (the task's parser splits on tabs).
            output.WriteLine($"WRT1\t{kind}\t{severity}\t{code}\t{file}\t{position}\t{Escape(message)}");
        }

        private static string Escape(string text)
        {
            var result = new StringBuilder(text.Length);
            foreach (var c in text)
            {
                _ = c switch
                {
                    '\\' => result.Append(@"\\"),
                    '\n' => result.Append(@"\n"),
                    '\r' => result.Append(@"\r"),
                    '\t' => result.Append(@"\t"),
                    _ => result.Append(c),
                };
            }
            return result.ToString();
        }
    }
}
