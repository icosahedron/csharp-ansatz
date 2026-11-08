using System;
using System.Collections.Generic;
using System.IO;
using System.Runtime.InteropServices;
using System.Text;
using Microsoft.Build.Framework;
using Microsoft.Build.Utilities;

namespace Warrant.Build;

/// <summary>
/// Runs <c>dotnet warrant.dll verify --csc-args … --format msbuild</c> and turns its records into build errors,
/// warnings and messages (KTD20, KTD22). Exit 0 means every theorem was proved, 1 that errors were reported, and 2
/// a usage or internal error, which the task reports as WRT0010 with the tail of the CLI's error output.
/// </summary>
public sealed class WarrantVerify : ToolTask
{
    /// <summary>The internal-error code: the CLI crashed, could not start, or broke its exit-code contract.</summary>
    public const string InternalErrorCode = "WRT0010";

    /// <summary>How many lines of the CLI's error output WRT0010 quotes.</summary>
    internal const int StderrTailLines = 20;

    private static readonly Encoding Utf8 = new UTF8Encoding(encoderShouldEmitUTF8Identifier: false);

    private readonly Queue<string> stderrTail = new();

    /// <summary>The file holding Csc's arguments, one per line (<c>obj/warrant.csc.args</c>).</summary>
    [Required]
    public string CscArgsFile { get; set; } = "";

    /// <summary>The project directory: the base of relative paths in the arguments, and the CLI's working directory.</summary>
    [Required]
    public string ProjectDirectory { get; set; } = "";

    /// <summary>
    /// The source records of the referenced projects that import <c>Warrant.Build</c> (<c>--reference-source</c>, #32), so
    /// the closed classes they define can be checked from their source.
    /// </summary>
    public ITaskItem[] ReferenceSources { get; set; } = [];

    /// <summary>The framework-dependent CLI, <c>warrant.dll</c>.</summary>
    [Required]
    public string CliPath { get; set; } = "";

    /// <summary>The <c>dotnet</c> host, from <c>$(DOTNET_HOST_PATH)</c>; when empty, <c>dotnet</c> is found on the path.</summary>
    public string? DotnetHostPath { get; set; }

    /// <summary>The kernel fuel per theorem (<c>$(WarrantKernelFuel)</c>); the CLI's default when empty.</summary>
    public string? KernelFuel { get; set; }

    /// <summary>The tactic fuel per theorem (<c>$(WarrantTacticFuel)</c>); the CLI's default when empty.</summary>
    public string? TacticFuel { get; set; }

    /// <summary>The wall-clock limit per theorem in seconds (<c>$(WarrantTimeoutSeconds)</c>); the CLI's default when empty.</summary>
    public string? TimeoutSeconds { get; set; }

    /// <summary>
    /// Keeps M4's <c>#if</c> combination check; set in multi-targeted projects, whose other target frameworks are not
    /// verified (KTD21).
    /// </summary>
    public bool KeepConditionalCheck { get; set; }

    /// <summary>
    /// Verifies through the per-user verification server, falling back to in-process verification when it cannot be used
    /// (<c>$(WarrantUseServer)</c>, <c>--server auto</c>); false always verifies in-process (<c>--server off</c>). M5b KTD27.
    /// </summary>
    public bool UseServer { get; set; } = true;

    /// <summary>Has the kernel check every cached proof again (<c>$(WarrantRecheck)</c>, <c>--recheck</c>). M5b KTD27.</summary>
    public bool Recheck { get; set; }

    /// <summary>The project's result cache (<c>$(WarrantCacheDir)</c>, <c>--cache-dir</c>); no cache when empty. M5b KTD27.</summary>
    public string? CacheDirectory { get; set; }

    /// <inheritdoc />
    protected override string ToolName => RuntimeInformation.IsOSPlatform(OSPlatform.Windows) ? "dotnet.exe" : "dotnet";

    /// <inheritdoc />
    protected override Encoding StandardOutputEncoding => Utf8;

    /// <inheritdoc />
    protected override Encoding StandardErrorEncoding => Utf8;

    // Kept apart so LogEventsFromTextOutput can tell the CLI's error output, quoted by WRT0010, from its records.
    /// <inheritdoc />
    protected override MessageImportance StandardOutputLoggingImportance => MessageImportance.Normal;

    /// <inheritdoc />
    protected override MessageImportance StandardErrorLoggingImportance => MessageImportance.High;

    /// <inheritdoc />
    protected override string GenerateFullPathToTool()
    {
        if (!string.IsNullOrEmpty(DotnetHostPath))
        {
            return DotnetHostPath!;
        }

        var path = Environment.GetEnvironmentVariable("PATH") ?? "";
        foreach (var directory in path.Split(Path.PathSeparator))
        {
            if (directory.Length == 0)
            {
                continue;
            }

            try
            {
                var candidate = Path.Combine(directory.Trim('"'), ToolName);
                if (File.Exists(candidate))
                {
                    return candidate;
                }
            }
            catch (ArgumentException)
            {
                // A malformed PATH entry names no directory; skip it.
            }
        }

        return ToolName;
    }

    /// <inheritdoc />
    protected override string GenerateCommandLineCommands()
    {
        var builder = new CommandLineBuilder();
        builder.AppendFileNameIfNotNull(CliPath);
        builder.AppendSwitch("verify");
        builder.AppendSwitchIfNotNull("--csc-args ", CscArgsFile);
        builder.AppendSwitchIfNotNull("--project-dir ", ProjectDirectory);
        foreach (var record in ReferenceSources)
        {
            builder.AppendSwitchIfNotNull("--reference-source ", record.ItemSpec);
        }
        builder.AppendSwitch("--format msbuild");
        AppendIfSet(builder, "--kernel-fuel ", KernelFuel);
        AppendIfSet(builder, "--tactic-fuel ", TacticFuel);
        AppendIfSet(builder, "--timeout ", TimeoutSeconds);
        if (KeepConditionalCheck)
        {
            builder.AppendSwitch("--keep-conditional-check");
        }

        builder.AppendSwitch(UseServer ? "--server auto" : "--server off");
        // A trailing separator would escape the closing quote of a quoted path.
        AppendIfSet(builder, "--cache-dir ", CacheDirectory?.TrimEnd('\\', '/'));
        if (Recheck)
        {
            builder.AppendSwitch("--recheck");
        }

        return builder.ToString();
    }

    /// <inheritdoc />
    protected override string GetWorkingDirectory() => ProjectDirectory;

    /// <inheritdoc />
    protected override bool ValidateParameters()
    {
        if (!File.Exists(CliPath))
        {
            Log.LogError(null, InternalErrorCode, null, null, 0, 0, 0, 0, $"Warrant: the warrant CLI was not found at '{CliPath}'.");
            return false;
        }

        return base.ValidateParameters();
    }

    /// <inheritdoc />
    protected override void LogEventsFromTextOutput(string singleLine, MessageImportance messageImportance)
    {
        var record = OutputParser.Parse(singleLine);
        if (record is not null)
        {
            LogRecord(record);
            return;
        }

        var fromStderr = messageImportance == StandardErrorImportanceToUse
            && messageImportance != StandardOutputImportanceToUse;
        if (fromStderr)
        {
            stderrTail.Enqueue(singleLine);
            if (stderrTail.Count > StderrTailLines)
            {
                stderrTail.Dequeue();
            }
        }

        var summary = singleLine.StartsWith("Warrant: ", StringComparison.Ordinal);
        Log.LogMessage(summary || fromStderr ? MessageImportance.High : MessageImportance.Normal, singleLine);
    }

    /// <inheritdoc />
    protected override bool HandleTaskExecutionErrors()
    {
        // Exit 1 with errors logged is the normal failure: the records already say why, so no MSB6006 is added.
        if (ExitCode == 1 && Log.HasLoggedErrors)
        {
            return false;
        }

        var reason = ExitCode switch
        {
            1 => "the warrant CLI exited with code 1 without reporting an error",
            2 => "the warrant CLI reported a usage or internal error (exit code 2)",
            _ => $"the warrant CLI exited with code {ExitCode}",
        };
        var message = new StringBuilder("Warrant: ").Append(reason).Append('.');
        if (stderrTail.Count > 0)
        {
            message.Append(" Its error output ended with:");
            foreach (var line in stderrTail)
            {
                message.Append('\n').Append(line);
            }
        }

        Log.LogError(null, InternalErrorCode, null, null, 0, 0, 0, 0, message.ToString());
        return false;
    }

    private static void AppendIfSet(CommandLineBuilder builder, string option, string? value)
    {
        if (!string.IsNullOrWhiteSpace(value))
        {
            builder.AppendSwitchIfNotNull(option, value!.Trim());
        }
    }

    private void LogRecord(OutputRecord record)
    {
        var file = record.File.Length == 0 ? null : record.File;
        switch (record.Kind)
        {
            case RecordKind.Diagnostic when record.Severity == RecordSeverity.Error:
                Log.LogError(null, record.Code, null, file, record.Line, record.Column, record.EndLine, record.EndColumn, record.Message);
                break;
            case RecordKind.Diagnostic when record.Severity == RecordSeverity.Warning:
                Log.LogWarning(null, record.Code, null, file, record.Line, record.Column, record.EndLine, record.EndColumn, record.Message);
                break;
            case RecordKind.Diagnostic:
                Log.LogMessage(null, record.Code, null, file, record.Line, record.Column, record.EndLine, record.EndColumn, MessageImportance.Normal, record.Message);
                break;
            default:
                // The goal block repeats what the diagnostic's later lines hold, so it is in the build output even
                // where only a diagnostic's first line is shown (KTD20); the summary is always shown.
                Log.LogMessage(MessageImportance.High, record.Message);
                break;
        }
    }
}
