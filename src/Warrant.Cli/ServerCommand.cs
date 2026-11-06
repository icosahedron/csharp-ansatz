using System.Globalization;
using Warrant.Engine;
using Warrant.Engine.Reports;
using Warrant.Engine.Service;

/// <summary>
/// <c>warrant server status | cancel &lt;id&gt; | shutdown</c> (M5b KTD26, R17; docs/m5b/07): manages the server a build of
/// this toolchain would use, found as a build finds it, from the semantics bundle and sidecar beside <c>warrant.dll</c>.
/// None of these verbs starts a server; the hidden <c>launch</c> verb is the CLI's own way to start one (KTD4).
/// </summary>
internal static class ServerCommand
{
    public const string Usage = "warrant server status | cancel <request id> | shutdown";

    /// <summary>Runs the verb.</summary>
    /// <param name="args">The arguments after <c>server</c>.</param>
    /// <param name="output">Where the answer goes.</param>
    /// <param name="error">Where usage errors and failures go.</param>
    /// <param name="settings">How the server is found; a build's defaults when null.</param>
    /// <returns>
    /// 0 when the verb did its job, or there is no server to report on or stop; 1 when <c>cancel</c> found no such request
    /// or the server could not be used; 2 for bad arguments.
    /// </returns>
    public static int Run(string[] args, TextWriter output, TextWriter error, ServerSettings? settings = null)
    {
        if (args is [ServerLauncher.LaunchVerb, var directory])
        {
            // Not for users: the short-lived process a CLI starts so the server outlives a cancelled build (KTD4).
            try
            {
                ServerLauncher.Launch(directory);
                return 0;
            }
            catch (ServerUnavailableException ex)
            {
                error.WriteLine($"warrant server: {ex.Message}");
                return 1;
            }
        }
        if (args is not (["status"] or ["shutdown"] or ["cancel", _]))
        {
            error.WriteLine($"usage: {Usage}");
            return 2;
        }
        settings ??= new ServerSettings();
        var bundlePath = Path.Combine(settings.SourceDirectory, SemanticsBundle.FileName);
        var sidecarPath = Path.Combine(settings.SourceDirectory, VerifyCommand.SidecarFileName);
        try
        {
            var hashes = new BundleHashes(OutcomeText.FileSha256(bundlePath), OutcomeText.FileSha256(sidecarPath));
            return Task.Run(() => RunAsync(args, output, error, settings, hashes)).GetAwaiter().GetResult();
        }
        catch (ServerUnavailableException ex)
        {
            error.WriteLine($"warrant server: the server could not be used: {ex.Message}");
            return 1;
        }
    }

    private static async Task<int> RunAsync(string[] args, TextWriter output, TextWriter error, ServerSettings settings, BundleHashes hashes)
    {
        using var client = await ServerClient.ConnectRunningAsync(settings, hashes, CancellationToken.None).ConfigureAwait(false);
        if (client is null)
        {
            var endpoint = ServerClient.Resolve(settings, ServerLauncher.CopyDirectory(settings, hashes));
            output.WriteLine($"No Warrant verification server is running for this toolchain (endpoint {endpoint.Address}).");
            return args[0] == "cancel" ? 1 : 0;
        }
        try
        {
            switch (args[0])
            {
                case "status":
                    Print(await client.StatusAsync().ConfigureAwait(false), output);
                    return 0;
                case "cancel":
                    if (await client.CancelAsync(args[1]).ConfigureAwait(false))
                    {
                        output.WriteLine($"Cancelled request {args[1]}.");
                        return 0;
                    }
                    output.WriteLine($"No request {args[1]} is running.");
                    return 1;
                default:
                    await client.ShutdownAsync().ConfigureAwait(false);
                    output.WriteLine($"The server (process {client.Hello!.ProcessId}) is shutting down once its running requests finish.");
                    return 0;
            }
        }
        catch (Exception ex) when (ex is StreamJsonRpc.RemoteInvocationException or StreamJsonRpc.ConnectionLostException or IOException)
        {
            await error.WriteLineAsync($"warrant server: {ex.Message}").ConfigureAwait(false);
            return 1;
        }
    }

    private static void Print(ServerStatus status, TextWriter output)
    {
        static string Megabytes(long bytes) => string.Create(CultureInfo.InvariantCulture, $"{bytes / (1024.0 * 1024.0):0.0} MB");
        output.WriteLine($"process      {status.ProcessId}");
        output.WriteLine($"endpoint     {status.Endpoint}");
        output.WriteLine($"toolchain    {status.ToolchainIdentity}");
        output.WriteLine(string.Create(CultureInfo.InvariantCulture, $"uptime       {status.Uptime:d\\.hh\\:mm\\:ss}"));
        output.WriteLine($"bundle       {status.BundleSha256 ?? "unknown"}");
        output.WriteLine($"GC heap      {Megabytes(status.GcHeapBytes)}");
        output.WriteLine($"working set  {Megabytes(status.WorkingSetBytes)}");
        var c = status.Counters;
        output.WriteLine($"cache        {c.Hits} hits, {c.Misses} misses, {c.TacticRuns} tactic runs, {c.Rechecked} rechecked");
        if (status.ActiveRequests.IsEmpty)
        {
            output.WriteLine("requests     none active");
            return;
        }
        output.WriteLine($"requests     {status.ActiveRequests.Length} active");
        foreach (var request in status.ActiveRequests)
        {
            output.WriteLine(string.Create(CultureInfo.InvariantCulture, $"  {request.RequestId}  {request.Units} units  {request.Elapsed.TotalSeconds:0.0} s  {request.ProjectDirectory}"));
        }
    }
}
