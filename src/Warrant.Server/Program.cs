using Warrant.Engine;
using Warrant.Engine.Service;
using Warrant.Lean4Export;
using Warrant.Meta;
using Warrant.Semantics;

namespace Warrant.Server;

/// <summary>
/// <c>warrant-server [--bundle &lt;path&gt;] [--sidecar &lt;path&gt;]</c> (M5b KTD1, KTD4): acquires its endpoint, exiting quietly
/// when another server holds it; loads the semantics bundle (checked by the kernel) and the attribute sidecar, from
/// beside its own assembly by default as <c>warrant verify</c> does; then serves until idle or shut down.
/// </summary>
internal static class Program
{
    private const string Usage = "usage: warrant-server [--bundle <path>] [--sidecar <path>]";

    /// <summary>Runs the server.</summary>
    /// <param name="args">The arguments.</param>
    /// <returns>0 when the server stopped or another holds its endpoint; 1 when it could not start; 2 for bad arguments.</returns>
    public static async Task<int> Main(string[] args)
    {
        string? bundlePath = null, sidecarPath = null;
        for (int i = 0; i < args.Length; i++)
        {
            bool hasValue = i + 1 < args.Length;
            switch (args[i])
            {
                case "--bundle" when hasValue:
                    bundlePath = args[++i];
                    break;
                case "--sidecar" when hasValue:
                    sidecarPath = args[++i];
                    break;
                default:
                    await Console.Error.WriteLineAsync(Usage).ConfigureAwait(false);
                    return 2;
            }
        }
        // A server outlives the build that started it. On Unix the launcher passes on the build's working directory, which
        // the server would otherwise hold for its whole life (an unmount fails as busy) and resolve relative paths against;
        // Windows already starts it in its own directory. Paths below are made absolute first.
        bundlePath = bundlePath is null ? null : Path.GetFullPath(bundlePath);
        sidecarPath = sidecarPath is null ? null : Path.GetFullPath(sidecarPath);
        Directory.SetCurrentDirectory(AppContext.BaseDirectory);
        bundlePath ??= Path.Combine(AppContext.BaseDirectory, SemanticsBundle.FileName);
        sidecarPath ??= Path.Combine(Path.GetDirectoryName(Path.GetFullPath(bundlePath))!, SemanticsBundle.SidecarFileName);

        var log = new ServerLog(ServerLog.DefaultPath());
        ServerHost? host;
        try
        {
            host = ServerHost.TryAcquire(ServerEndpoint.For(AppContext.BaseDirectory), log, ServerHost.IdleTimeoutFromEnvironment());
        }
        catch (Exception ex) when (ex is EndpointRefusedException or ArgumentException or IOException or UnauthorizedAccessException)
        {
            log.Write($"refused to start: {ex.Message}");
            await Console.Error.WriteLineAsync($"warrant-server: {ex.Message}").ConfigureAwait(false);
            return 1;
        }
        if (host is null)
        {
            return 0;
        }
        using (host)
        {
            VerificationService service;
            try
            {
                // The sidecar first: it names the bundle it was made for, so a mismatched pair is refused before the slow load.
                service = new VerificationService(bundlePath, sidecarPath);
            }
            catch (Exception ex) when (ex is SidecarFormatException or Lean4ExportFormatException or InvalidDataException or IOException or UnauthorizedAccessException)
            {
                log.Write($"could not load the semantics bundle '{bundlePath}' and sidecar '{sidecarPath}': {ex.Message}");
                await Console.Error.WriteLineAsync($"warrant-server: {ex.Message}").ConfigureAwait(false);
                return 1;
            }
            using (service)
            {
                log.Write($"loaded the semantics bundle '{bundlePath}' ({service.Hashes?.Bundle})");
                await host.RunAsync(service).ConfigureAwait(false);
            }
        }
        return 0;
    }
}
