using System.Diagnostics;
using System.Globalization;
using System.Security.Cryptography;
using Warrant.Cic;
using Warrant.Engine.Service;
using Warrant.Kernel;
using Warrant.Lean4Export;
using Warrant.Store;

/// <summary>
/// <c>warrant import &lt;file.ndjson[.gz]&gt;... --store &lt;dir&gt; [--verified] [--fuel N]</c> (M5b KTD20, docs/m5b/05): builds a
/// new version of a store from lean4export files, read in order. A constant may come again in a later file only if it is
/// the same constant (up to binder names, as the kernel compares an exported constant with its own); the store keeps the
/// first. Trusted mode stores the declarations as read; verified mode checks each with the kernel first and stores what
/// the kernel admitted, its own constructors, recursors and quotient constants included, as <c>warrant export</c> does.
/// </summary>
/// <remarks>
/// The new version holds exactly the files given: importing replaces the store's content rather than adding to it, so a
/// store is always a snapshot of the sources its manifest lists. Exit codes are <c>warrant check</c>'s: 0 when the store
/// was written; 1 when the kernel rejected a declaration or a repeated constant differs; 2 for bad arguments, unreadable
/// input or a resource limit. Nothing is written unless the import succeeds.
/// </remarks>
internal static class ImportCommand
{
    public const string Usage = "warrant import <file.ndjson[.gz]>... --store <dir> [--verified] [--fuel N]";

    public static int Run(string[] args, TextWriter output, TextWriter error)
    {
        var files = new List<string>();
        string? store = null;
        bool verified = false;
        long fuel = KernelLimits.Corpus.Fuel;
        for (int i = 0; i < args.Length; i++)
        {
            switch (args[i])
            {
                case "--store" when i + 1 < args.Length:
                    store = args[++i];
                    break;
                case "--verified":
                    verified = true;
                    break;
                case "--fuel" when i + 1 < args.Length && long.TryParse(args[i + 1], NumberStyles.None, CultureInfo.InvariantCulture, out fuel):
                    i++;
                    break;
                case var option when option.StartsWith("--", StringComparison.Ordinal):
                    error.WriteLine($"unknown option '{option}'\nusage: {Usage}");
                    return 2;
                default:
                    files.Add(args[i]);
                    break;
            }
        }
        if (store is null || files.Count == 0)
        {
            error.WriteLine($"usage: {Usage}");
            return 2;
        }

        var sw = Stopwatch.StartNew();
        var mode = verified ? Manifest.Verified : Manifest.Trusted;
        output.WriteLine($"importing {files.Count} file(s) into {store} ({mode})");
        using var writer = StoreWriter.Create(store);
        var env = new KernelEnvironment();
        var checker = new ExportChecker(env, KernelLimits.Corpus with { Fuel = fuel });
        // The constants stored so far, for comparing a repeated one: as read in trusted mode, as admitted in verified mode.
        // Not the kernel's environment: it holds all four quotient constants once the first is checked.
        var stored = new Dictionary<Name, ConstantInfo>();
        var sources = new List<ManifestSource>();
        string? lean = null;
        var formats = new SortedSet<string>(StringComparer.Ordinal);
        foreach (var file in files)
        {
            var sha256 = Sha256(file);
            using var reader = new Lean4ExportReader(Lean4Export.OpenRead(file));
            lean ??= reader.Metadata.LeanVersion;
            if (reader.Metadata.LeanVersion != lean)
            {
                error.WriteLine($"{file}: exported from Lean {reader.Metadata.LeanVersion}, but the earlier files from Lean {lean}; a store holds one Lean version");
                return 2;
            }
            formats.Add(reader.Metadata.FormatVersion);
            int added = 0, repeated = 0;
            void Store(Declaration declaration)
            {
                writer.Add(declaration);
                foreach (var c in declaration.Constants)
                {
                    stored[c.Name] = c;
                }
                added++;
            }
            int code = KernelThread.Run(() =>
            {
                foreach (var declaration in reader.ReadDeclarations())
                {
                    var earlier = declaration.Constants.Select(c => (Exported: c, Earlier: stored.GetValueOrDefault(c.Name))).ToList();
                    if (earlier.Any(p => p.Earlier is not null))
                    {
                        foreach (var (exported, before) in earlier)
                        {
                            if (before is null || !ExportChecker.ConstantsMatch(before, exported))
                            {
                                error.WriteLine(before is null
                                    ? $"{file}: '{declaration.Constants[0].Name}' repeats part of an earlier declaration, without '{exported.Name}'"
                                    : $"{file}: '{exported.Name}' differs from the constant of that name an earlier file declared");
                                return 1;
                            }
                        }
                        repeated++;
                        continue;
                    }
                    if (!verified)
                    {
                        Store(declaration);
                        continue;
                    }
                    int admittedBefore = checker.Admitted.Count;
                    var result = checker.Check(declaration);
                    if (result is null)
                    {
                        // A mutual block, admitted when its last member arrives.
                        continue;
                    }
                    if (!result.Accepted)
                    {
                        error.WriteLine($"{(result.ResourceLimit ? "DECLINED" : "REJECTED")} {result.Name}: {result.Error}");
                        return result.ResourceLimit ? 2 : 1;
                    }
                    for (int i = admittedBefore; i < checker.Admitted.Count; i++)
                    {
                        Store(checker.Admitted[i]);
                    }
                }
                return 0;
            });
            if (code != 0)
            {
                return code;
            }
            sources.Add(new ManifestSource(Path.GetFileName(file), sha256));
            output.WriteLine($"  {Path.GetFileName(file)}: {added:N0} declarations stored, {repeated:N0} repeated");
        }
        var version = writer.Commit(sources, lean!, string.Join(", ", formats), mode, verified ? Toolchain.Identity : null);
        output.WriteLine($"wrote {version}: {writer.Declarations:N0} declarations, {writer.Constants:N0} constants in {sw.Elapsed.TotalSeconds:F1}s");
        return 0;
    }

    private static string Sha256(string path)
    {
        using var stream = new FileStream(path, FileMode.Open, FileAccess.Read, FileShare.Read, 1 << 16, FileOptions.SequentialScan);
        return Convert.ToHexStringLower(SHA256.HashData(stream));
    }
}

/// <summary>
/// <c>warrant check-store &lt;dir&gt; [--fuel N] [--quiet]</c> (M5b KTD20): reads the store's current version back in its stored
/// order into a fresh environment, checks every declaration with the kernel, whatever the manifest says, and prints the
/// same lines and summary as <c>warrant check</c>, with its exit codes.
/// </summary>
internal static class CheckStoreCommand
{
    public const string Usage = "warrant check-store <dir> [--fuel N] [--quiet]";

    public static int Run(string[] args, TextWriter output, TextWriter error)
    {
        string? store = null;
        bool quiet = false;
        long fuel = KernelLimits.Corpus.Fuel;
        for (int i = 0; i < args.Length; i++)
        {
            switch (args[i])
            {
                case "--quiet":
                    quiet = true;
                    break;
                case "--fuel" when i + 1 < args.Length && long.TryParse(args[i + 1], NumberStyles.None, CultureInfo.InvariantCulture, out fuel):
                    i++;
                    break;
                case var option when option.StartsWith("--", StringComparison.Ordinal) || store is not null:
                    error.WriteLine($"unknown option '{option}'\nusage: {Usage}");
                    return 2;
                default:
                    store = args[i];
                    break;
            }
        }
        if (store is null)
        {
            error.WriteLine($"usage: {Usage}");
            return 2;
        }

        var sw = Stopwatch.StartNew();
        using var reader = StoreReader.Open(store);
        output.WriteLine($"checking store {reader.StoreDirectory} ({reader.Version}, Lean {reader.Manifest.Lean})");
        var checker = new ExportChecker(new KernelEnvironment(), KernelLimits.Corpus with { Fuel = fuel });
        return KernelCheck.Run(checker, reader.ReadAll(new NameInterner()), output, quiet, slowest: 0, sw);
    }
}
