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
                   --reference-source <record>...  --keep-conditional-check
          Without --csc-args or --sources, the project's most recent verifying build is explained as it was verified
          (obj/**/warrant.explain): its argument file, its referenced projects' source records, and its options. A project
          with no such file and exactly one obj/**/warrant.csc.args uses that argument file.
        """;

    /// <summary>The argument file the build writes (Warrant.Build.targets).</summary>
    public const string CscArgsFileName = "warrant.csc.args";

    /// <summary>
    /// What the build's <c>WarrantVerify</c> target ran with, written beside its argument file before each run
    /// (Warrant.Build.targets; #123, #124): only the target framework that verifies writes one.
    /// </summary>
    /// <remarks>
    /// One entry per line:
    /// <code>
    /// warrant-explain 1
    /// args=&lt;full path of the argument file&gt;
    /// project=&lt;full path of the project directory&gt;
    /// keep-conditional-check=true|false
    /// reference-source=&lt;full path of a referenced project's source record&gt;
    /// </code>
    /// </remarks>
    public const string BuildFileName = "warrant.explain";

    private const string BuildHeader = "warrant-explain 1";

    /// <summary>A verifying build, as its <see cref="BuildFileName"/> records it.</summary>
    /// <param name="CscArgs">The argument file.</param>
    /// <param name="ProjectDirectory">The project directory.</param>
    /// <param name="KeepConditionalCheck">Whether the build kept the conditional-compilation check.</param>
    /// <param name="ReferenceSources">The referenced projects' source records.</param>
    public sealed record VerifiedBuild(string CscArgs, string ProjectDirectory, bool KeepConditionalCheck, IReadOnlyList<string> ReferenceSources);

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
        bool keepConditionalCheck = false;
        var referenceSources = new List<string>();
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
                case "--reference-source" when hasValue:
                    referenceSources.Add(args[++i]);
                    break;
                case "--keep-conditional-check":
                    keepConditionalCheck = true;
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
        if (unit is null || (sources is not null && (cscArgs is not null || projectDir is not null || referenceSources.Count > 0)))
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
                // The build that verified, so explain compiles what it compiled and sees the referenced projects it saw.
                VerifiedBuild? build;
                try
                {
                    build = LatestBuild(root);
                }
                catch (InvalidDataException e)
                {
                    error.WriteLine($"declined: {e.Message}");
                    return 2;
                }
                if (build is not null)
                {
                    cscArgs = build.CscArgs;
                    root = build.ProjectDirectory;
                    keepConditionalCheck |= build.KeepConditionalCheck;
                    referenceSources.AddRange(build.ReferenceSources);
                }
                else
                {
                    var found = CscArgsFiles(root);
                    if (found.Count != 1)
                    {
                        error.WriteLine(found.Count == 0
                            ? $"declined: no {CscArgsFileName} under {Path.Combine(root, "obj")}; build the project once, or pass --csc-args or --sources"
                            : $"declined: {found.Count} {CscArgsFileName} files under {Path.Combine(root, "obj")} and no {BuildFileName} saying which one was verified; build the project with Warrant enabled, or pass --csc-args");
                        return 2;
                    }
                    cscArgs = found[0];
                }
            }
            verify.AddRange(["--csc-args", cscArgs, "--project-dir", root]);
            foreach (var record in referenceSources)
            {
                verify.AddRange(["--reference-source", record]);
            }
            if (keepConditionalCheck)
            {
                verify.Add("--keep-conditional-check");
            }
        }
        verify.AddRange(passed);
        return VerifyCommand.Run([.. verify], output, error, server, cancellationToken);
    }

    /// <summary>
    /// The most recent verifying build: the newest <see cref="BuildFileName"/> under the project's <c>obj</c> directory, or
    /// null if there is none. Each build that verifies rewrites its file, so with several configurations it is the last one
    /// built; with several target frameworks only the first verifies, so it is never another framework's.
    /// </summary>
    /// <exception cref="InvalidDataException">The newest file is not one this Warrant can read.</exception>
    public static VerifiedBuild? LatestBuild(string projectDirectory)
    {
        var obj = Path.Combine(projectDirectory, "obj");
        if (!Directory.Exists(obj))
        {
            return null;
        }
        var path = Directory.EnumerateFiles(obj, BuildFileName, SearchOption.AllDirectories)
            .OrderByDescending(File.GetLastWriteTimeUtc)
            .ThenBy(p => p, StringComparer.Ordinal)
            .FirstOrDefault();
        return path is null ? null : ReadBuild(path);
    }

    private static VerifiedBuild ReadBuild(string path)
    {
        var lines = File.ReadAllLines(path).Where(l => l.Length > 0).ToList();
        if (lines.Count == 0 || lines[0] != BuildHeader)
        {
            throw new InvalidDataException($"{path} is not a {BuildFileName} this Warrant can read; build the project again");
        }
        string? args = null, project = null;
        bool keep = false;
        var records = new List<string>();
        foreach (var line in lines.Skip(1))
        {
            int eq = line.IndexOf('=', StringComparison.Ordinal);
            var (key, value) = eq < 0 ? (line, "") : (line[..eq], line[(eq + 1)..]);
            switch (key)
            {
                case "args":
                    args = value;
                    break;
                case "project":
                    project = value;
                    break;
                case "keep-conditional-check":
                    keep = string.Equals(value, "true", StringComparison.OrdinalIgnoreCase);
                    break;
                case "reference-source" when value.Length > 0:
                    records.Add(value);
                    break;
                default:
                    throw new InvalidDataException($"{path}: unexpected line '{line}'; build the project again");
            }
        }
        if (string.IsNullOrEmpty(args) || string.IsNullOrEmpty(project))
        {
            throw new InvalidDataException($"{path}: the args or project line is missing; build the project again");
        }
        return new VerifiedBuild(args, project, keep, records);
    }

    /// <summary>Every <see cref="CscArgsFileName"/> under the project's <c>obj</c> directory.</summary>
    private static List<string> CscArgsFiles(string projectDirectory)
    {
        var obj = Path.Combine(projectDirectory, "obj");
        return Directory.Exists(obj)
            ? [.. Directory.EnumerateFiles(obj, CscArgsFileName, SearchOption.AllDirectories).Order(StringComparer.Ordinal)]
            : [];
    }
}
