using System.Collections.Immutable;
using System.Diagnostics;
using System.Globalization;
using System.IO.Compression;
using System.Text;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Warrant.Engine;
using Warrant.Engine.Reports;
using Warrant.Engine.Service;
using Warrant.Extraction;
using Warrant.Frontend;
using Warrant.Kernel;
using Warrant.Lean4Export;
using Warrant.Meta;
using Warrant.Semantics;
using Warrant.Vir;

/// <summary>
/// <c>warrant verify</c> (plan M5a U12, KTD20, KTD21, KTD24; docs/m5a/07): builds the compilation from the compiler's own
/// arguments, or like <c>translate</c> from a directory, then extracts, proves (through the verification server with
/// <c>--server auto</c>, else in-process; M5b KTD5) and reports. With <c>--format msbuild</c> each diagnostic is one
/// <c>WRT1</c> record (the format <c>Warrant.Build</c>'s <c>OutputParser</c> reads), so a multi-line goal stays one MSBuild
/// event.
/// </summary>
internal static class VerifyCommand
{
    public const string Usage = """
        warrant verify --csc-args <file> [--project-dir <dir>] [--reference-source <record>]... [options]
               warrant verify <directory> [options]
          options: --format text|msbuild  --out <file.ndjson>  --report <dir>  --keep-conditional-check
                   --kernel-fuel <n>  --tactic-fuel <n>  --timeout <seconds>  --bundle <path>  --cache-dir <dir>  --recheck
                   --server auto|off  --timings
        """;

    /// <summary>Runs the verb.</summary>
    /// <param name="args">The arguments after <c>verify</c>.</param>
    /// <param name="output">Where unit lines, diagnostics (or records) and the summary go.</param>
    /// <param name="error">Where usage errors and declines go.</param>
    /// <param name="server">How the server is found and started; a build's defaults when null.</param>
    /// <param name="cancellationToken">
    /// Interrupts the run (Ctrl+C): the server is sent <c>$/cancelRequest</c>, or the in-process run stops, and the units
    /// that had not finished are not reported (M5b R6).
    /// </param>
    /// <returns>0 when every theorem was proved (warnings allowed); 1 when an error was reported; 2 for bad arguments or unreadable input.</returns>
    public static int Run(string[] args, TextWriter output, TextWriter error, ServerSettings? server = null, CancellationToken cancellationToken = default)
    {
        string? directory = null, cscArgs = null, projectDir = null, outPath = null, reportDir = null, bundlePath = null, cacheDir = null, explain = null;
        bool msbuild = false, keepConditionalCheck = false, recheck = false, timings = false;
        bool? useServer = null;
        var referenceSources = new List<string>();
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
                case "--reference-source" when hasValue:
                    // A referenced project's source record (#32), written by Warrant.Build after that project's compile.
                    referenceSources.Add(args[++i]);
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
                case "--cache-dir" when hasValue:
                    cacheDir = args[++i];
                    break;
                case "--bundle" when hasValue:
                    bundlePath = args[++i];
                    break;
                case "--keep-conditional-check":
                    keepConditionalCheck = true;
                    break;
                case "--recheck":
                    recheck = true;
                    break;
                case "--server" when hasValue && args[i + 1] is "auto" or "off":
                    useServer = args[++i] == "auto";
                    break;
                case "--timings":
                    timings = true;
                    break;
                case "--explain" when hasValue:
                    // warrant explain's way in (ExplainCommand): verify one unit's closure with a trace of its script.
                    explain = args[++i];
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
        if ((directory is null) == (cscArgs is null) || ((projectDir is not null || referenceSources.Count > 0) && cscArgs is null)
            || (explain is not null && (outPath is not null || reportDir is not null || cacheDir is not null)))
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
        var sidecarPath = Path.Combine(Path.GetDirectoryName(Path.GetFullPath(bundlePath))!, SemanticsBundle.SidecarFileName);
        if (!File.Exists(sidecarPath))
        {
            error.WriteLine($"declined: attribute sidecar '{sidecarPath}' not found; it ships beside the semantics bundle");
            return 2;
        }

        try
        {
            // The sidecar first: it names the bundle it was made for, so a mismatched pair is declined before the slow load.
            var bundleSha256 = OutcomeText.FileSha256(bundlePath);
            var sidecar = Sidecar.Load(sidecarPath, bundleSha256);
            var settings = new Settings(msbuild, outPath, reportDir, bundlePath, sidecar, kernelFuel, tacticFuel, timeoutSeconds)
            {
                Hashes = new BundleHashes(bundleSha256, OutcomeText.FileSha256(sidecarPath)),
                // M5b KTD14: the NDJSON of --out needs every admitted declaration, which a cached unit does not admit
                // until export reads certificates from the cache (plan U16), so --out verifies without the cache.
                CacheDirectory = outPath is null && cacheDir is not null ? Path.GetFullPath(cacheDir) : null,
                Explain = explain,
                Recheck = recheck,
                SidecarPath = sidecarPath,
                UseServer = useServer,
                Timings = timings,
                Server = server ?? new ServerSettings(),
                ReferenceSources = referenceSources,
                CancellationToken = cancellationToken,
            };
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
        /// <summary>The project's directory, which a request names; the compiled directory in the directory mode.</summary>
        public string ProjectDirectory { get; init; } = "";

        /// <summary>The SHA-256 of the bundle and sidecar files, which cache keys cover.</summary>
        public required BundleHashes Hashes { get; init; }

        /// <summary>The result cache directory (M5b KTD14); null for no cache.</summary>
        public string? CacheDirectory { get; init; }

        /// <summary>Whether every cached proof is checked by the kernel again (M5b KTD16, <c>WarrantRecheck</c>).</summary>
        public bool Recheck { get; init; }

        /// <summary>The attribute sidecar's file, which a started server copies.</summary>
        public required string SidecarPath { get; init; }

        /// <summary>
        /// <c>--server auto</c> (true) or <c>--server off</c> (false); null when the option is absent, which is <c>off</c>
        /// with the summary unchanged, so direct uses of the CLI keep M5a's output. The build passes the option (KTD27).
        /// </summary>
        public bool? UseServer { get; init; }

        /// <summary>Whether each unit's time is printed after the summary (<c>--timings</c>, M5b KTD30).</summary>
        public bool Timings { get; init; }

        /// <summary>The unit <c>warrant explain</c> traces, as the user named it (M5b KTD24); null for a verify.</summary>
        public string? Explain { get; init; }

        /// <summary>How the server is found and started.</summary>
        public required ServerSettings Server { get; init; }

        /// <summary>The referenced projects' source records (<c>--reference-source</c>, #32).</summary>
        public IReadOnlyList<string> ReferenceSources { get; init; } = [];

        /// <summary>Interrupts the run.</summary>
        public CancellationToken CancellationToken { get; init; }

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
        settings = settings with { ProjectDirectory = root };
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
        // The referenced projects' records by assembly name (#32). A source is checked and compiled only when a closed class
        // from it is used; one that does not check out then fails the run, since verifying without it would report its
        // closed classes as unsupported for a reason that is only a stale build.
        var records = new Dictionary<string, ReferencedSource>(StringComparer.Ordinal);
        ExtractionResult extraction;
        try
        {
            foreach (var path in settings.ReferenceSources.Where(File.Exists))
            {
                // A record that names no assembly cannot match a reference; one Warrant cannot otherwise read fails only
                // when a closed class from its assembly is used (#120).
                if (ReferencedSource.Open(path) is { AssemblyName: { } name } record)
                {
                    records.TryAdd(name, record);
                }
            }
            extraction = Extractor.Extract(compilation, new ExtractionOptions
            {
                BuildDefines = true,
                KeepConditionalCheck = keepConditionalCheck,
                ReferencedSource = name => records.TryGetValue(name, out var record) ? record.Load(root) : null,
            });
        }
        catch (InvalidDataException ex)
        {
            report.Diagnostic("error", CompilationFailure.Code, null, $"Warrant cannot read a referenced project's source: {ex.Message}", []);
            report.Summary(0, 0, 0);
            return 1;
        }
        return Verify(compilation, extraction, settings, settings.Engine(KernelLimits.Interactive), report);
    }

    private static int FromDirectory(string directory, Settings settings, TextWriter output)
    {
        var root = Path.GetFullPath(directory);
        settings = settings with { ProjectDirectory = root };
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
        var extracted = extraction.Units.ToList();
        var diagnostics = extraction.Diagnostics.ToList();
        ExtractedUnit? explained = null;
        if (settings.Explain is { } query)
        {
            // M5b KTD24: the unit and what it needs, with nothing else reported.
            if (ExplainedUnit(extracted, query, report) is not { } target)
            {
                return 2;
            }
            explained = target;
            var closure = Closure(target, extracted);
            extracted = [.. extracted.Where(u => closure.Contains(u.Key))];
            diagnostics = [.. diagnostics.Where(d => d.MemberKey is not null && closure.Contains(d.MemberKey))];
        }
        var inputs = extracted.Select(u => new EngineUnit(u.Unit, u.DisplayName, u.Spans)).ToList();
        // What the server needs to keep this run's assumption report (KTD25): the claims are source text, which only the
        // client has.
        var claims = inputs
            .Where(u => u.Unit.Kind == VirUnitKind.Theorem)
            .Select(u => (u.Unit.Key, Text: AssumptionReports.ClaimSpan(u) is { } span ? report.Sources.Text(span) : null))
            .Where(c => c.Text is not null)
            .ToImmutableDictionary(c => c.Key, c => c.Text!, StringComparer.Ordinal);
        // M5b KTD1, KTD6: the same request the server takes, verified by the same service in-process. The spans and the
        // source text stay here, where the outcomes are rendered.
        var request = new VerifyRequest(
            VerificationService.ProtocolVersion,
            Guid.NewGuid().ToString("N"),
            settings.ProjectDirectory,
            settings.CacheDirectory,
            VerifyBudgets.From(options),
            settings.Recheck,
            Priority: 0,
            [.. extracted.Select(u => new RequestUnit(u.Key, u.Unit.Kind, u.DisplayName, VirWriter.Write(u.Unit)))])
        {
            Report = new VerifyReport(compilation.Options.CheckOverflow, OutcomeText.BundleName(settings.BundlePath), claims),
        };
        var execution = Execute(request, explained?.Key, settings, report);
        var (response, path) = (execution.Response, execution.Path);
        if (explained is not null)
        {
            PrintTrace(explained, execution.Steps, report);
        }
        // Both paths render from the response's wire outcomes, so they print the same bytes (M5b R3, KTD28).
        var outcomes = response.Units.Select(u => u.Outcome).ToList();

        int width = outcomes.Select(u => u.DisplayName.Length).DefaultIfEmpty(0).Max();
        foreach (var unit in outcomes)
        {
            report.Line($"  {unit.DisplayName.PadRight(width)}  {Describe(unit)}");
        }

        foreach (var d in diagnostics)
        {
            report.Diagnostic(TranslateCommand.Severity(d.Severity), d.Id, d.Location, d.Message);
        }
        var units = extracted.ToDictionary(u => u.Key, StringComparer.Ordinal);
        var engineUnits = inputs.ToDictionary(u => u.Unit.Key, StringComparer.Ordinal);
        // A proved theorem's outcome needs its certificate, which the wire leaves out; nothing below reports one.
        foreach (var unit in outcomes.Where(u => u.Kind != OutcomeKind.Proved).Select(u => u.ToOutcome([])))
        {
            var location = units.TryGetValue(unit.Key, out var extractedUnit) ? extractedUnit.Location : null;
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
                case NotProvedOutcome failed:
                    // A contract obligation reports every VC that failed, each at its node (M6 U11, #90).
                    foreach (var n in failed.EachFailure())
                    {
                        var spans = engineUnits[unit.Key].Spans;
                        report.Diagnostic(
                            "error", NotProvedOutcome.Code, OutcomeText.SpanOf(spans, n.TacticNode) ?? location,
                            OutcomeText.NotProvedMessage(name, n, spans, report.Sources.Text), OutcomeText.NotProvedDetails(n), n.Goals);
                    }
                    break;
                case UndecidedOutcome u:
                    report.Diagnostic("error", UndecidedOutcome.Code, location, OutcomeText.UndecidedMessage(u.UnitKind, name, u.Reason));
                    break;
                case InternalErrorOutcome i:
                    report.Diagnostic("error", InternalErrorOutcome.Code, location, OutcomeText.InternalErrorMessage(name, i.Reason));
                    break;
                case FailedOutcome { Code: { } code } f:
                    // M5b KTD33: a script the engine rejects as extraction rejects a malformed one, at the tactic.
                    report.Diagnostic("error", code, OutcomeText.SpanOf(engineUnits[unit.Key].Spans, f.Node) ?? location, f.Reason);
                    break;
                case FailedOutcome f:
                    report.Diagnostic("error", InternalErrorOutcome.Code, location, OutcomeText.FailedMessage(name, f.Reason));
                    break;
            }
        }

        // An interrupted export has no certificates to write.
        if (settings.OutPath is not null && !execution.Certificates.IsEmpty)
        {
            // Export's certificates (KTD25), from either path: the bytes M5a wrote, compressed for the wire.
            using (var stream = File.Create(settings.OutPath))
            using (var gzip = new GZipStream(new MemoryStream(execution.Certificates.ToArray()), CompressionMode.Decompress))
            {
                gzip.CopyTo(stream);
            }
            report.Line($"wrote the bundle and {execution.Admitted} admitted declaration(s) to {settings.OutPath}");
        }
        if (settings.ReportDir is not null)
        {
            Directory.CreateDirectory(settings.ReportDir);
            var reportSettings = new ReportSettings(compilation.Options.CheckOverflow, OutcomeText.BundleName(settings.BundlePath));
            // From the wire outcomes, on either path, as the server builds the report it keeps (KTD25).
            var assumptions = AssumptionReports.Build(outcomes, inputs, reportSettings, report.Sources.Text);
            File.WriteAllText(Path.Combine(settings.ReportDir, "report.md"), MarkdownReport.Render(assumptions));
            File.WriteAllText(Path.Combine(settings.ReportDir, "report.json"), JsonReport.Render(assumptions));
            report.Line($"wrote report.md and report.json to {settings.ReportDir}");
        }

        var theorems = outcomes.Where(u => u.UnitKind == VirUnitKind.Theorem).ToList();
        int proved = theorems.Count(u => u.Kind == OutcomeKind.Proved);
        // A cancelled theorem is unreported, not unproved (M5b R6).
        int notProved = theorems.Count(u => u.Kind is not (OutcomeKind.Proved or OutcomeKind.Cancelled));
        // The path is named only when the server was asked for, so the default output stays M5a's (KTD27).
        report.Summary(outcomes.Count, proved, notProved, response.Counters.Hits, response.Counters.Rechecked, settings.UseServer == true ? path : null);
        if (settings.Timings)
        {
            if (execution.Connection is { } connection)
            {
                var how = connection.Started ? "started the server and connected" : "connected to the running server";
                report.Line(string.Create(CultureInfo.InvariantCulture, $"timings (server): {how} in {connection.Elapsed.TotalMilliseconds:0.0} ms"));
            }
            report.Line(string.Create(CultureInfo.InvariantCulture, $"timings ({path}): {response.Elapsed.TotalMilliseconds:0.0} ms for the request"));
            foreach (var unit in response.Units)
            {
                var source = unit.FromCache ? (unit.Rechecked ? "rechecked" : "cache") : path;
                report.Line(string.Create(CultureInfo.InvariantCulture, $"  {unit.Elapsed.TotalMilliseconds,10:0.0} ms  {source,-10}  {unit.Outcome.DisplayName}"));
            }
        }

        bool clean = report.Errors == 0 && outcomes.All(u => u.Kind is OutcomeKind.Translated or OutcomeKind.Proved);
        return clean ? 0 : 1;
    }

    /// <summary>A unit's line: its outcome's name, with the proof kind or the reason where there is one.</summary>
    private static string Describe(OutcomeDto unit) => unit.Kind == OutcomeKind.Proved
        ? $"proved ({AssumptionReports.ProofName(unit.By ?? ProofKind.Script)})"
        : TranslateCommand.Describe(unit.ToOutcome([]));

    /// <summary>
    /// Verifies the request through the server when <c>--server auto</c> asks for it, else in-process (M5b KTD5). Any
    /// failure on the server path writes one message with the reason and verifies the request in-process with the same
    /// service; the server answers a request all at once, so a lost connection leaves no unit with a result, and the
    /// whole request runs again. An interrupted run is not a failure: its units come back cancelled.
    /// </summary>
    /// <param name="request">The request.</param>
    /// <param name="explain">The unit to trace (<c>explain</c>); null for a verify, or an export when <c>--out</c> is given.</param>
    /// <param name="settings">The settings.</param>
    /// <param name="report">Where the fallback message goes.</param>
    /// <returns>The response, the path taken (<c>server</c> or <c>in-process</c>), and what export or explain added.</returns>
    private static Execution Execute(VerifyRequest request, string? explain, Settings settings, Reporter report)
    {
        var token = settings.CancellationToken;
        var (interval, timeout) = (settings.Server.HeartbeatInterval, settings.Server.HeartbeatTimeout);
        if (settings.UseServer == true)
        {
            try
            {
                return Task.Run(async () =>
                {
                    var connecting = Stopwatch.StartNew();
                    using var client = await ServerClient.ConnectOrStartAsync(settings.Server, settings.Hashes, settings.BundlePath, settings.SidecarPath, token)
                        .ConfigureAwait(false);
                    var connection = new ServerConnection(connecting.Elapsed, client.Started);
                    if (explain is not null)
                    {
                        var explained = await client.ExplainAsync(new ExplainRequest(request, explain), interval, timeout, token).ConfigureAwait(false);
                        return new Execution(explained.Response, "server") { Steps = explained.Steps, Connection = connection };
                    }
                    if (settings.OutPath is not null)
                    {
                        var exported = await client.ExportAsync(request, interval, timeout, token).ConfigureAwait(false);
                        return new Execution(exported.Response, "server") { Certificates = exported.Certificates, Admitted = exported.Admitted, Connection = connection };
                    }
                    return new Execution(await client.VerifyAsync(request, interval, timeout, token).ConfigureAwait(false), "server") { Connection = connection };
                }).GetAwaiter().GetResult();
            }
            catch (OperationCanceledException) when (token.IsCancellationRequested)
            {
                return new Execution(Cancelled(request), "server");
            }
            catch (ServerUnavailableException ex)
            {
                report.Message($"Warrant: verification server unavailable ({ex.Message}); verifying in-process.");
            }
        }
        var service = settings.Server.InProcessService;
        using var owned = service is null ? new VerificationService(SemanticsBundle.Load(settings.BundlePath), settings.Sidecar, hashes: settings.Hashes) : null;
        var inProcess = owned ?? service!;
        if (explain is not null)
        {
            var explained = inProcess.Explain(new ExplainRequest(request, explain), token);
            return new Execution(explained.Response, "in-process") { Steps = explained.Steps };
        }
        if (settings.OutPath is not null)
        {
            var exported = inProcess.Export(request, token);
            return new Execution(exported.Response, "in-process") { Certificates = exported.Certificates, Admitted = exported.Admitted };
        }
        return new Execution(inProcess.Verify(request, token), "in-process");
    }

    /// <summary>What <see cref="Execute"/> got back.</summary>
    /// <param name="Response">The verification.</param>
    /// <param name="Path"><c>server</c> or <c>in-process</c>.</param>
    private sealed record Execution(VerifyResponse Response, string Path)
    {
        /// <summary>Export's gzip-compressed certificate file; empty for a verify, or when the run was interrupted.</summary>
        public ReadOnlyMemory<byte> Certificates { get; init; }

        /// <summary>The number of declarations the export's run admitted.</summary>
        public int Admitted { get; init; }

        /// <summary>The traced unit's steps (<c>explain</c>).</summary>
        public ImmutableArray<TacticStep> Steps { get; init; } = [];

        /// <summary>How the server was reached; null in-process.</summary>
        public ServerConnection? Connection { get; init; }
    }

    /// <summary>
    /// How long reaching the server took (<c>--timings</c>, M5b KTD30): connecting to a running one, or starting one,
    /// which includes its loading the bundle, and connecting.
    /// </summary>
    /// <param name="Elapsed">From the first connection attempt to the server's answers to <c>hello</c> and <c>status</c>.</param>
    /// <param name="Started">Whether this run started the server.</param>
    private sealed record ServerConnection(TimeSpan Elapsed, bool Started);

    /// <summary>
    /// The unit <c>warrant explain</c> names (KTD24): by documentation-comment ID, by display name, or by the end of a
    /// display name after a dot, with or without its parameter list, as a diagnostic names it (<c>Increments.AlwaysLarger(int)</c>).
    /// An unknown or ambiguous name lists the units, and the run stops.
    /// </summary>
    private static ExtractedUnit? ExplainedUnit(List<ExtractedUnit> units, string query, Reporter report)
    {
        static string WithoutParameters(string name) => name.IndexOf('(', StringComparison.Ordinal) is var i and >= 0 ? name[..i] : name;
        static bool EndsWith(string name, string suffix) =>
            string.Equals(name, suffix, StringComparison.Ordinal) || name.EndsWith("." + suffix, StringComparison.Ordinal);
        Func<ExtractedUnit, bool>[] rules =
        [
            u => string.Equals(u.Key, query, StringComparison.Ordinal),
            u => string.Equals(u.DisplayName, query, StringComparison.Ordinal),
            u => EndsWith(u.DisplayName, query),
            u => EndsWith(WithoutParameters(u.DisplayName), query),
        ];
        foreach (var rule in rules)
        {
            var matches = units.Where(rule).ToList();
            if (matches.Count == 1)
            {
                return matches[0];
            }
            if (matches.Count > 1)
            {
                report.Line($"'{query}' names {matches.Count} units; name one of them:");
                foreach (var m in matches)
                {
                    report.Line($"  {m.DisplayName}");
                }
                return null;
            }
        }
        report.Line($"no unit is named '{query}'; the units are:");
        foreach (var u in units.OrderBy(u => u.DisplayName, StringComparer.Ordinal))
        {
            report.Line($"  {u.DisplayName}");
        }
        return null;
    }

    /// <summary>The unit and every unit it depends on, transitively.</summary>
    private static HashSet<string> Closure(ExtractedUnit target, List<ExtractedUnit> units)
    {
        var byKey = units.ToDictionary(u => u.Key, StringComparer.Ordinal);
        var closure = new HashSet<string>(StringComparer.Ordinal);
        var work = new Stack<string>([target.Key]);
        while (work.Count > 0)
        {
            var key = work.Pop();
            if (closure.Add(key) && byKey.TryGetValue(key, out var unit))
            {
                foreach (var dep in unit.Unit.Deps)
                {
                    work.Push(dep);
                }
            }
        }
        return closure;
    }

    /// <summary>
    /// The trace of the explained unit (KTD24): each tactic as its source reads, where it is, and the goals before and
    /// after it or why it failed; a tactic inside <c>AllGoals</c> or <c>Try</c> is numbered under it.
    /// </summary>
    private static void PrintTrace(ExtractedUnit unit, ImmutableArray<TacticStep> steps, Reporter report)
    {
        report.Line(unit.Location is { } at ? $"explaining {unit.DisplayName}  {report.Sources.Position(at)}" : $"explaining {unit.DisplayName}");
        report.Line("");
        if (steps.IsEmpty)
        {
            report.Line(unit.Unit.Kind == VirUnitKind.Theorem
                ? "  no proof script ran; the outcome below says how the claim was decided"
                : "  not a theorem; the outcome below is its translation");
            report.Line("");
            return;
        }
        var numbers = new List<int>();
        foreach (var step in steps)
        {
            if (numbers.Count > step.Depth + 1)
            {
                numbers.RemoveRange(step.Depth + 1, numbers.Count - step.Depth - 1);
            }
            if (numbers.Count == step.Depth + 1)
            {
                numbers[step.Depth]++;
            }
            else
            {
                numbers.Add(1);
            }
            var indent = new string(' ', 2 * step.Depth);
            VirSpan? span = step.Node is { } id && unit.Spans.TryGetSpan(id, out var s) ? s : null;
            var label = span is null ? step.Tactic : report.Sources.Text(span) ?? step.Tactic;
            report.Line($"{indent}[{string.Join(".", numbers)}] {label}{(span is null ? "" : "   " + report.Sources.Position(span))}");
            Block(indent, "before:", step.Before);
            if (step.Failure is { } failure)
            {
                Block(indent, "failed:", failure);
            }
            else if (step.After is { } after)
            {
                Block(indent, "after:", after);
            }
            else
            {
                report.Line($"{indent}  stopped here: the run ended inside this tactic");
            }
        }
        report.Line("");

        void Block(string indent, string title, string text)
        {
            report.Line($"{indent}  {title}");
            var lines = text.Length == 0 ? ["no goals"] : text.Split('\n');
            foreach (var line in lines)
            {
                report.Line(line.Length == 0 ? "" : $"{indent}    {line}");
            }
        }
    }

    /// <summary>The response of a request interrupted before the server answered: every unit cancelled.</summary>
    private static VerifyResponse Cancelled(VerifyRequest request) => new(
        request.ProtocolVersion,
        request.RequestId,
        [
            .. request.Units.Select(u => new UnitResult(
                new OutcomeDto(OutcomeKind.Cancelled, u.Key, u.Kind, u.DisplayName ?? LeanNames.FallbackDisplay(u.Key), []), FromCache: false, Rechecked: false, TimeSpan.Zero)),
        ],
        new VerifyCounters(0, 0, 0, 0),
        TimeSpan.Zero);

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

        /// <summary>A line that is neither a diagnostic nor the summary, such as the server fallback's (M5b KTD5): an informational record.</summary>
        public void Message(string text)
        {
            if (msbuild)
            {
                Record("diag", "info", "", null, text);
            }
            else
            {
                output.WriteLine(text);
            }
        }

        /// <summary>
        /// The summary line; it says how many results came from the result cache when any did, how many of those the
        /// kernel checked again when any were, and, when given, the path the results came by (M5b R8, R11, KTD27).
        /// </summary>
        public void Summary(int units, int proved, int notProved, int fromCache = 0, int rechecked = 0, string? path = null)
        {
            var cached = (fromCache, rechecked) switch
            {
                (_, > 0) => string.Create(CultureInfo.InvariantCulture, $" ({fromCache} from cache, {rechecked} rechecked)"),
                (> 0, _) => string.Create(CultureInfo.InvariantCulture, $" ({fromCache} from cache)"),
                _ => "",
            };
            var text = string.Create(CultureInfo.InvariantCulture, $"Warrant: {units} verified units, {proved} theorems proved{cached}, {notProved} not proved.");
            if (path is not null)
            {
                text += $" [{path}]";
            }
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
