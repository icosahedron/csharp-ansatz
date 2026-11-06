using System.Diagnostics;
using System.Globalization;
using System.Text;
using Warrant.Kernel;
using Warrant.Lean4Export;

// Exit codes follow the Lean Kernel Arena convention:
//   0  every declaration accepted
//   1  a declaration was rejected (a type error)
//   2  declined: unreadable input, or a resource limit (fuel) was hit
return Cli.Run(args);

internal static class Cli
{
    private const string Usage = """
        usage:
          warrant check <export.ndjson[.gz]> [--fuel N] [--admit-rejected] [--quiet] [--slowest N]
          warrant stats <export.ndjson[.gz]>
          warrant export <export.ndjson[.gz]> <output.ndjson> [--fuel N] [--quiet]
          warrant translate <directory> [--out <file.ndjson>] [--report <file.md>] [--check-overflow] [--bundle <path>]
          warrant verify --csc-args <file> [--project-dir <dir>] [options]
          warrant verify <directory> [options]
          warrant server status | cancel <request id> | shutdown

        check   re-checks every declaration with the kernel (exit 0 accept, 1 reject, 2 decline)
                --fuel N          step budget per type checker (default 100000000)
                --admit-rejected  keep going after a rejection by admitting it unchecked
                --quiet           print only the summary
                --slowest N       also print the N declarations that took longest to check, with the time and
                                  the memory allocated since the previous result (reading included)
        stats   prints record counts without checking
        export  checks the file, then writes what the kernel admitted (its own generated
                constructors, recursors and quotient constants) as lean4export 3.1.0, so another
                kernel can re-check exactly what Warrant accepted
        translate compiles every .cs file under the directory, translates the [Verified] members and
                  [Theorem]s, and prints one line per member and any diagnostics (exit 0 when every
                  member translated and every theorem was proved, 1 otherwise, 2 for unreadable input)
                  --out FILE        write the bundle and every admitted declaration as lean4export NDJSON
                  --report FILE     write the assumption report as Markdown
                  --check-overflow  compile with overflow checking on
                  --bundle PATH     the semantics bundle (default: the one beside warrant.dll)
        verify  builds the compilation from the compiler's argument file (one argument per line, paths relative
                to --project-dir, default the current directory) or, like translate, from a directory; then
                translates, proves and reports every [Verified] member and [Theorem] (exit 0 when every theorem
                was proved, warnings allowed; 1 when an error was reported; 2 for bad arguments or unreadable input)
                  --format text|msbuild     text (default), or one tab-separated WRT1 record per diagnostic
                  --out FILE                write the bundle and every admitted declaration as lean4export NDJSON
                  --report DIR              write report.md and report.json
                  --keep-conditional-check  compare every #if combination even with the build's defines
                  --kernel-fuel N           kernel steps per theorem (default 20000000; 100000000 for a directory)
                  --tactic-fuel N           tactic steps per theorem (default 171970)
                  --timeout SECONDS         wall-clock limit per theorem (default 30)
                  --bundle PATH             the semantics bundle; the attribute sidecar must be beside it
                  --cache-dir DIR           read and write the result cache there (not with --out)
                  --recheck                 check every cached proof with the kernel again
                  --server auto|off         verify through the per-user verification server, starting it when none
                                            runs and verifying in-process when it cannot be used (auto); or always
                                            in-process (off, the default); --out and --report always verify in-process
                  --timings                 print each unit's time after the summary
        server  manages the verification server of this toolchain: status prints what it holds and runs, cancel stops a
                request, shutdown stops it after its running requests (exit 0 when no server runs, except for cancel)
        """;

    public static int Run(string[] args)
    {
        if (args.Length < 2 || args[0] is not ("check" or "stats" or "export" or "translate" or "verify" or "server") || (args[0] == "export" && args.Length < 3))
        {
            Console.Error.WriteLine(Usage);
            return 2;
        }
        try
        {
            return args[0] switch
            {
                "stats" => Stats(args[1]),
                "export" => Check(args[1], args.Skip(3).ToArray(), output: args[2]),
                "translate" => TranslateCommand.Run(args[1..], Console.Out, Console.Error),
                "verify" => Verify(args[1..]),
                "server" => ServerCommand.Run(args[1..], Console.Out, Console.Error),
                _ => Check(args[1], args.Skip(2).ToArray()),
            };
        }
        catch (Exception ex) when (ex is Lean4ExportFormatException or IOException or UnauthorizedAccessException or FormatException)
        {
            Console.Error.WriteLine($"declined: {ex.Message}");
            return 2;
        }
    }

    /// <summary>
    /// The build task reads verify's output as UTF-8 without a BOM, whatever the console's code page (goals hold ⊢). The
    /// first Ctrl+C interrupts the run, cancelling it on the server or in-process (M5b R6); a second one ends the process.
    /// </summary>
    private static int Verify(string[] args)
    {
        Console.OutputEncoding = new UTF8Encoding(encoderShouldEmitUTF8Identifier: false);
        using var interrupt = new CancellationTokenSource();
        void OnCancel(object? sender, ConsoleCancelEventArgs e)
        {
            if (!interrupt.IsCancellationRequested)
            {
                e.Cancel = true;
                interrupt.Cancel();
            }
        }
        Console.CancelKeyPress += OnCancel;
        try
        {
            return VerifyCommand.Run(args, Console.Out, Console.Error, cancellationToken: interrupt.Token);
        }
        finally
        {
            Console.CancelKeyPress -= OnCancel;
        }
    }

    private static int Stats(string path)
    {
        var file = Lean4Export.ReadFile(path);
        var s = file.Statistics;
        Console.WriteLine($"format {file.Metadata.FormatVersion}, Lean {file.Metadata.LeanVersion} ({file.Metadata.ExporterName} {file.Metadata.ExporterVersion})");
        Console.WriteLine($"names {s.Names:N0}, levels {s.Levels:N0}, expressions {s.Exprs:N0}, declaration lines {s.DeclarationLines:N0}");
        foreach (var g in file.Declarations.SelectMany(d => d.Constants).GroupBy(c => c.Kind).OrderBy(g => g.Key))
        {
            Console.WriteLine($"  {g.Key,-12} {g.Count(),8:N0}");
        }
        return 0;
    }

    private static int Check(string path, string[] options, string? output = null)
    {
        long fuel = KernelLimits.Corpus.Fuel;
        bool admitRejected = false, quiet = false;
        int slowest = 0;
        for (int i = 0; i < options.Length; i++)
        {
            switch (options[i])
            {
                case "--fuel" when i + 1 < options.Length:
                    fuel = long.Parse(options[++i], NumberStyles.None, CultureInfo.InvariantCulture);
                    break;
                case "--admit-rejected" when output is null:
                    admitRejected = true;
                    break;
                case "--quiet":
                    quiet = true;
                    break;
                case "--slowest" when i + 1 < options.Length:
                    slowest = int.Parse(options[++i], NumberStyles.None, CultureInfo.InvariantCulture);
                    break;
                default:
                    Console.Error.WriteLine($"unknown option '{options[i]}'{Environment.NewLine}{Usage}");
                    return 2;
            }
        }

        var sw = Stopwatch.StartNew();
        using var reader = new Lean4ExportReader(Lean4Export.OpenRead(path));
        Console.WriteLine($"checking {path} (format {reader.Metadata.FormatVersion}, Lean {reader.Metadata.LeanVersion})");
        var env = new KernelEnvironment();
        var checker = new ExportChecker(env, KernelLimits.Corpus with { Fuel = fuel }, admitRejected);
        int accepted = 0, rejected = 0, declined = 0;
        CheckResult? firstFailure = null;
        // The cost of each result: its checking time, and the memory the checking thread allocated since the previous
        // result (results come back on that thread, so reading the declaration is included in the memory).
        var costs = new PriorityQueue<(string Name, double Seconds, long Bytes), double>();
        long lastBytes = -1;
        checker.CheckAll(reader.ReadDeclarations(), r =>
        {
            if (slowest > 0)
            {
                long bytes = GC.GetAllocatedBytesForCurrentThread();
                if (lastBytes >= 0)
                {
                    costs.Enqueue((r.Name.ToString(), r.Elapsed.TotalSeconds, bytes - lastBytes), r.Elapsed.TotalSeconds);
                    if (costs.Count > slowest)
                    {
                        costs.Dequeue();
                    }
                }
                lastBytes = bytes;
            }
            if (r.Accepted)
            {
                accepted++;
                return;
            }
            if (r.ResourceLimit)
            {
                declined++;
            }
            else
            {
                rejected++;
            }
            firstFailure ??= r;
            if (!quiet)
            {
                var label = r.ResourceLimit ? "DECLINED" : "REJECTED";
                Console.WriteLine($"{label} {r.Name}: {r.Error}");
            }
        });
        Console.WriteLine($"accepted {accepted:N0}, rejected {rejected:N0}, declined {declined:N0}; {env.Count:N0} constants in {sw.Elapsed.TotalSeconds:F1}s");
        if (slowest > 0)
        {
            Console.WriteLine($"slowest {costs.Count} (seconds, MB allocated, name):");
            var top = new List<(string Name, double Seconds, long Bytes)>();
            while (costs.Count > 0)
            {
                top.Add(costs.Dequeue());
            }
            foreach (var (name, seconds, bytes) in Enumerable.Reverse(top))
            {
                Console.WriteLine(string.Create(CultureInfo.InvariantCulture, $"  {seconds,9:F3}  {bytes / (1024.0 * 1024.0),9:F1}  {name}"));
            }
        }
        if (output is not null)
        {
            using var writer = new Lean4ExportWriter(File.Create(output), reader.Metadata);
            writer.WriteAll(checker.Admitted);
            Console.WriteLine($"wrote {checker.Admitted.Count:N0} admitted declarations to {output}");
        }
        if (firstFailure is null)
        {
            return 0;
        }
        return firstFailure.ResourceLimit ? 2 : 1;
    }
}
