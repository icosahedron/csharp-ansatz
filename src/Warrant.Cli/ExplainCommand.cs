/// <summary>
/// <c>warrant explain &lt;unit&gt;</c> (M5b KTD24, docs/m5b/07): compiles and extracts as the build does, then verifies one unit
/// and the units it needs with a trace of its proof script, and prints every step, its source and the goals before and
/// after it, then the unit's outcome as <c>warrant verify</c> reports it. It never reads or writes the result cache: an
/// explanation comes from running the tactics.
/// </summary>
internal static class ExplainCommand
{
    public const string Usage = """
        warrant explain <unit> [--project-dir <dir>] [--csc-args <file>] [--sources <dir>] [options]
          <unit>   the name a diagnostic gives (Increments.AlwaysLarger(int)), any dotted end of the display name, or the
                   documentation-comment ID (M:Sample.Increments.AlwaysLarger(System.Int32))
          options: --server auto|off  --bundle <path>  --kernel-fuel <n>  --tactic-fuel <n>  --timeout <seconds>
          Without --csc-args or --sources, the argument file of the project's most recent build (obj/**/warrant.csc.args)
          is used.
        """;

    /// <summary>The argument file the build writes (Warrant.Build.targets).</summary>
    public const string CscArgsFileName = "warrant.csc.args";

    /// <summary>Runs the verb.</summary>
    /// <param name="args">The arguments after <c>explain</c>.</param>
    /// <param name="output">Where the trace and the outcome go.</param>
    /// <param name="error">Where usage errors and declines go.</param>
    /// <param name="server">How the server is found and started; a build's defaults when null.</param>
    /// <param name="cancellationToken">Interrupts the run.</param>
    /// <returns>0 when the unit verified; 1 when it did not; 2 for bad arguments, an unknown unit or unreadable input.</returns>
    public static int Run(string[] args, TextWriter output, TextWriter error, ServerSettings? server = null, CancellationToken cancellationToken = default)
    {
        string? unit = null, cscArgs = null, projectDir = null, sources = null;
        var passed = new List<string>();
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
                case "--sources" when hasValue:
                    sources = args[++i];
                    break;
                case "--server" or "--bundle" or "--kernel-fuel" or "--tactic-fuel" or "--timeout" when hasValue:
                    passed.Add(args[i]);
                    passed.Add(args[++i]);
                    break;
                case var a when unit is null && !a.StartsWith("--", StringComparison.Ordinal):
                    unit = a;
                    break;
                default:
                    error.WriteLine($"unknown or incomplete option '{args[i]}'{Environment.NewLine}usage: {Usage}");
                    return 2;
            }
        }
        if (unit is null || (sources is not null && (cscArgs is not null || projectDir is not null)))
        {
            error.WriteLine($"usage: {Usage}");
            return 2;
        }

        var verify = new List<string> { "--explain", unit };
        if (sources is not null)
        {
            verify.Add(sources);
        }
        else
        {
            var root = projectDir ?? Environment.CurrentDirectory;
            if (cscArgs is null)
            {
                cscArgs = LatestCscArgs(root);
                if (cscArgs is null)
                {
                    error.WriteLine($"declined: no {CscArgsFileName} under {Path.Combine(root, "obj")}; build the project once, or pass --csc-args or --sources");
                    return 2;
                }
            }
            verify.AddRange(["--csc-args", cscArgs, "--project-dir", root]);
        }
        verify.AddRange(passed);
        return VerifyCommand.Run([.. verify], output, error, server, cancellationToken);
    }

    /// <summary>The most recently written <see cref="CscArgsFileName"/> under the project's <c>obj</c> directory, or null.</summary>
    public static string? LatestCscArgs(string projectDirectory)
    {
        var obj = Path.Combine(projectDirectory, "obj");
        if (!Directory.Exists(obj))
        {
            return null;
        }
        return Directory.EnumerateFiles(obj, CscArgsFileName, SearchOption.AllDirectories)
            .OrderByDescending(File.GetLastWriteTimeUtc)
            .ThenBy(p => p, StringComparer.Ordinal)
            .FirstOrDefault();
    }
}
