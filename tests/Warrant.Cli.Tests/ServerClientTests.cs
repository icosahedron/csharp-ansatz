using System.Diagnostics;
using System.Globalization;
using System.Text;
using Warrant.Engine;
using Warrant.Engine.Reports;
using Warrant.Engine.Service;

namespace Warrant.Cli.Tests;

/// <summary>
/// A verification server of a test's own (M5b KTD29): a unique endpoint name, a temporary directory for the server's
/// per-toolchain copies, and a ten-minute idle limit as a backstop. Disposing it shuts down any server on the endpoint,
/// waits for its process to exit and deletes the copies, so no server outlives the test.
/// </summary>
internal sealed class TestServer : IAsyncDisposable
{
    private readonly string _copyRoot;

    public TestServer(string? endpointName = null)
        : this(endpointName ?? "wc" + Guid.NewGuid().ToString("N")[..16], Path.Combine(Path.GetTempPath(), "warrant-servers-" + Guid.NewGuid().ToString("N")[..12]))
    {
    }

    private TestServer(string? endpointName, string copyRoot)
    {
        _copyRoot = copyRoot;
        Settings = new ServerSettings
        {
            EndpointName = endpointName,
            CopyRoot = _copyRoot,
            ServerEnvironment = new Dictionary<string, string> { [ServerIdleVariable] = "600" },
        };
    }

    /// <summary>
    /// A server whose endpoint name is computed from its copy's directory, as a build's is, with its copies under
    /// <paramref name="copyRoot"/>, which the test owns and deletes.
    /// </summary>
    public static TestServer WithComputedEndpoint(string copyRoot) => new(endpointName: null, copyRoot);

    private const string ServerIdleVariable = "WARRANT_SERVER_IDLE_SECONDS";

    public ServerSettings Settings { get; }

    public string CopyRoot => _copyRoot;

    /// <summary>The bundle and sidecar beside the CLI, which the tests verify with.</summary>
    public static string BundlePath => Path.Combine(AppContext.BaseDirectory, SemanticsBundle.FileName);

    public static string SidecarPath => Path.Combine(AppContext.BaseDirectory, VerifyCommand.SidecarFileName);

    public static BundleHashes Hashes { get; } = new(OutcomeText.FileSha256(BundlePath), OutcomeText.FileSha256(SidecarPath));

    /// <summary>Connects to the running server without starting one; null when none runs.</summary>
    public Task<ServerClient?> ConnectAsync() => ServerClient.ConnectRunningAsync(Settings, Hashes, CancellationToken.None);

    /// <summary>The running server's status.</summary>
    public async Task<ServerStatus> StatusAsync()
    {
        using var client = await ConnectAsync() ?? throw new InvalidOperationException("no server is running");
        return await client.StatusAsync();
    }

    /// <summary>Polls the status until a condition holds; fails after <paramref name="seconds"/>.</summary>
    public async Task<ServerStatus> WaitForStatusAsync(Func<ServerStatus, bool> condition, int seconds = 30)
    {
        var deadline = DateTime.UtcNow.AddSeconds(seconds);
        while (true)
        {
            var status = await StatusAsync();
            if (condition(status))
            {
                return status;
            }
            Assert.True(DateTime.UtcNow < deadline, "the server's status never reached the expected state");
            await Task.Delay(20);
        }
    }

    /// <summary><c>warrant verify</c> in-process, with this server's settings.</summary>
    public (int Code, string Output) Verify(string[] args, VerificationService? inProcess = null, CancellationToken cancellationToken = default)
    {
        using var output = new StringWriter { NewLine = "\n" };
        var code = VerifyCommand.Run(args, output, output, Settings with { InProcessService = inProcess }, cancellationToken);
        return (code, output.ToString());
    }

    public async ValueTask DisposeAsync()
    {
        ServerClient? client;
        try
        {
            client = await ConnectAsync();
        }
        catch (ServerUnavailableException)
        {
            // An endpoint no server can hold.
            client = null;
        }
        using (client)
        {
            if (client is not null)
            {
                int pid = client.Hello!.ProcessId;
                await client.ShutdownAsync();
                WaitForExit(pid);
            }
        }
        for (int attempt = 0; Directory.Exists(_copyRoot); attempt++)
        {
            try
            {
                Directory.Delete(_copyRoot, recursive: true);
            }
            catch (Exception ex) when (attempt < 50 && ex is IOException or UnauthorizedAccessException)
            {
                await Task.Delay(100);
            }
        }
    }

    /// <summary>Waits up to 30 s for a process to exit; kills it and fails when it does not.</summary>
    public static void WaitForExit(int pid)
    {
        Process process;
        try
        {
            process = Process.GetProcessById(pid);
        }
        catch (ArgumentException)
        {
            return;
        }
        using (process)
        {
            if (!process.WaitForExit(30_000))
            {
                process.Kill();
                Assert.Fail($"the server (process {pid}) did not exit after shutdown");
            }
        }
    }
}

/// <summary>Source directories written for one test, compiled like <c>warrant verify &lt;directory&gt;</c>.</summary>
internal sealed class SourceDirectory : IDisposable
{
    public SourceDirectory(string source)
    {
        Directory.CreateDirectory(Path);
        File.WriteAllText(System.IO.Path.Combine(Path, "S.cs"), "using Warrant;\n" + source);
    }

    public string Path { get; } = System.IO.Path.Combine(System.IO.Path.GetTempPath(), "warrant-source-" + Guid.NewGuid().ToString("N")[..12]);

    public void Dispose() => Directory.Delete(Path, recursive: true);

    /// <summary>One proved theorem: quick on either path.</summary>
    public const string Fast = """
        public static class S
        {
            [Verified] public static int Inc(int x) => x + 1;
            [Theorem] static Proof Larger() => Prove.That(Inc(41) > 41);
        }
        """;

    /// <summary>
    /// A{k}(x) = A{k-1}(A{k-1}(x)) adds 2^k to x; deciding <c>A30(0) &gt; 0</c> runs until its kernel fuel or time runs
    /// out or it is cancelled. Early and Then are proved at once.
    /// </summary>
    public static string Slow()
    {
        var source = new StringBuilder("public static class S\n{\n    [Verified] public static int A0(int x) => x + 1;\n");
        for (int k = 1; k <= 30; k++)
        {
            source.Append(CultureInfo.InvariantCulture, $"    [Verified] public static int A{k}(int x) => A{k - 1}(A{k - 1}(x));\n");
        }
        source.Append("""
                [Theorem] static Proof Early() => Prove.That(A1(0) == 2);
                [Theorem] static Proof Slow() => Prove.That(A30(0) > 0);
                [Theorem] static Proof Then() => Prove.That(A0(0) == 1);
            }

            """);
        return source.ToString();
    }
}

/// <summary>
/// The CLI as the server's client (plan M5b U9; KTD3 to KTD5, KTD26, KTD27): it starts a detached server when none runs,
/// falls back in-process with one message when the server cannot be used, and cancels its request on the server.
/// </summary>
/// <remarks>
/// Not tested here: a pipe or socket served by another user. On Windows that needs a second account; on Unix a socket
/// directory owned by someone else needs root. The checks themselves are the endpoint's (<c>CurrentUserOnly</c>, the
/// socket directory check, the peer's user ID).
/// </remarks>
[Collection(ServerProcesses.Name)]
public sealed class ServerClientTests
{
    private const string FallbackPrefix = "Warrant: verification server unavailable (";

    [Fact]
    public async Task WithNoServerRunningServerAutoStartsOneFromACopyVerifiesThroughItAndItKeepsRunning()
    {
        await using var server = new TestServer();
        using var source = new SourceDirectory(SourceDirectory.Fast);
        Assert.Null(await server.ConnectAsync());

        var (code, output) = server.Verify([source.Path, "--server", "auto"]);

        Assert.True(code == 0, output);
        Assert.DoesNotContain(FallbackPrefix, output, StringComparison.Ordinal);
        Assert.EndsWith("Warrant: 2 verified units, 1 theorems proved, 0 not proved. [server]\n", output, StringComparison.Ordinal);
        // The CLI's run is over and the server still answers; it is a process of its own.
        var status = await server.StatusAsync();
        Assert.NotEqual(Environment.ProcessId, status.ProcessId);
        Assert.Empty(status.ActiveRequests);
        Assert.Equal(2, status.Counters.Misses);
        using (var running = Process.GetProcessById(status.ProcessId))
        {
            Assert.False(running.HasExited);
        }
        // It runs from its copy, so the CLI's own folder can be rebuilt under it (KTD4).
        var copy = Assert.Single(Directory.GetDirectories(server.CopyRoot));
        Assert.True(File.Exists(Path.Combine(copy, ServerLauncher.ServerAssembly)));
        using (File.Open(Path.Combine(AppContext.BaseDirectory, ServerLauncher.ServerAssembly), FileMode.Open, FileAccess.ReadWrite, FileShare.None))
        {
        }

        // A second run reuses the server rather than starting another.
        var (again, secondOutput) = server.Verify([source.Path, "--server", "auto"]);
        Assert.True(again == 0, secondOutput);
        Assert.Equal(status.ProcessId, (await server.StatusAsync()).ProcessId);
    }

    [Theory]
    [InlineData("text")]
    [InlineData("msbuild")]
    public async Task AnEndpointNameNobodyCanCreateFallsBackInProcessAndSaysWhyOnce(string format)
    {
        await using var server = new TestServer(endpointName: "no/such/endpoint");
        using var source = new SourceDirectory(SourceDirectory.Fast);

        var (code, output) = server.Verify([source.Path, "--server", "auto", "--format", format]);

        Assert.True(code == 0, output);
        var message = "Warrant: verification server unavailable (the endpoint name 'no/such/endpoint' is not a plain file name); verifying in-process.";
        var expected = format == "msbuild" ? $"WRT1\tdiag\tinfo\t\t\t0\t0\t0\t0\t{message}\n" : message + "\n";
        Assert.Equal(1, CountOf(output, FallbackPrefix));
        Assert.Contains(expected, output, StringComparison.Ordinal);
        Assert.EndsWith("2 verified units, 1 theorems proved, 0 not proved. [in-process]\n", output, StringComparison.Ordinal);
    }

    [Fact]
    public async Task ServerOffNeverConnectsOrStartsAServerAndLeavesTheSummaryUntagged()
    {
        await using var server = new TestServer();
        using var source = new SourceDirectory(SourceDirectory.Fast);

        var (code, output) = server.Verify([source.Path, "--server", "off"]);

        Assert.True(code == 0, output);
        Assert.EndsWith("Warrant: 2 verified units, 1 theorems proved, 0 not proved.\n", output, StringComparison.Ordinal);
        Assert.DoesNotContain(FallbackPrefix, output, StringComparison.Ordinal);
        Assert.Null(await server.ConnectAsync());
        Assert.False(Directory.Exists(server.CopyRoot));
    }

    [Fact]
    public async Task KillingTheServerMidRequestFinishesTheRunInProcessWithTheSameDiagnostics()
    {
        await using var server = new TestServer();
        using var fast = new SourceDirectory(SourceDirectory.Fast);
        using var slow = new SourceDirectory(SourceDirectory.Slow());
        Assert.Equal(0, server.Verify([fast.Path, "--server", "auto"]).Code);
        // Two million kernel steps take a few seconds on either path, and end the same way.
        string[] args = [slow.Path, "--format", "msbuild", "--kernel-fuel", "2000000"];

        var run = Task.Run(() => server.Verify([.. args, "--server", "auto"]));
        var status = await server.WaitForStatusAsync(s => s.ActiveRequests.Length == 1);
        using (var process = Process.GetProcessById(status.ProcessId))
        {
            process.Kill();
            await process.WaitForExitAsync();
        }
        var (code, output) = await run;
        var (offCode, offOutput) = server.Verify([.. args, "--server", "off"]);

        Assert.Equal(offCode, code);
        Assert.Equal(1, CountOf(output, FallbackPrefix + "the connection to the server was lost"));
        Assert.Contains("kernel fuel ran out (2,000,000 steps)", output, StringComparison.Ordinal);
        Assert.Equal(offOutput, Normalized(output));
        Assert.EndsWith("Warrant: 34 verified units, 2 theorems proved, 1 not proved. [in-process]\n", output, StringComparison.Ordinal);
    }

    [Fact]
    public async Task InterruptingTheRunCancelsTheTheoremOnTheServerKeepsFinishedUnitsAndLeavesNoActiveRequest()
    {
        await using var server = new TestServer();
        using var fast = new SourceDirectory(SourceDirectory.Fast);
        using var slow = new SourceDirectory(SourceDirectory.Slow());
        Assert.Equal(0, server.Verify([fast.Path, "--server", "auto"]).Code);
        using var interrupt = new CancellationTokenSource();

        var run = Task.Run(() => server.Verify([slow.Path, "--server", "auto", "--kernel-fuel", "100000000000", "--timeout", "3600"], cancellationToken: interrupt.Token));
        // Early and Then are proved at once; Slow keeps the request running.
        await server.WaitForStatusAsync(s => s.ActiveRequests.Length == 1);
        await Task.Delay(1000);
        var cancelled = Stopwatch.StartNew();
        await interrupt.CancelAsync();
        var (code, output) = await run;
        cancelled.Stop();
        var status = await server.WaitForStatusAsync(s => s.ActiveRequests.IsEmpty, seconds: 5);

        Assert.True(cancelled.Elapsed < TimeSpan.FromSeconds(5), $"the run took {cancelled.Elapsed} to stop");
        Assert.Equal(1, code);
        Assert.Matches(@"(?m)^  S\.Early\(\) +proved \(", output);
        Assert.Matches(@"(?m)^  S\.Then\(\) +proved \(", output);
        Assert.Matches(@"(?m)^  S\.Slow\(\) +cancelled$", output);
        Assert.DoesNotContain("WRT0006", output, StringComparison.Ordinal);
        Assert.DoesNotContain(FallbackPrefix, output, StringComparison.Ordinal);
        Assert.EndsWith("Warrant: 34 verified units, 2 theorems proved, 0 not proved. [server]\n", output, StringComparison.Ordinal);
        Assert.Empty(status.ActiveRequests);
    }

    [Fact]
    public async Task WithTheComputedEndpointNameTheCliFindsTheServerItStartedFromALinkedStateDirectory()
    {
        // A per-user state directory reached through a link (a symlinked home on Unix, a junction on Windows): the CLI names
        // the copy by the path it built, and the server must listen on that name, not on one from its resolved path.
        var real = Path.Combine(Path.GetTempPath(), "warrant-state-" + Guid.NewGuid().ToString("N")[..12]);
        var linked = real + "-link";
        Directory.CreateDirectory(real);
        LinkDirectory(linked, real);
        try
        {
            await using var server = TestServer.WithComputedEndpoint(Path.Combine(linked, "servers"));
            using var source = new SourceDirectory(SourceDirectory.Fast);

            var (code, output) = server.Verify([source.Path, "--server", "auto"]);

            Assert.True(code == 0, output);
            Assert.DoesNotContain(FallbackPrefix, output, StringComparison.Ordinal);
            Assert.EndsWith("Warrant: 2 verified units, 1 theorems proved, 0 not proved. [server]\n", output, StringComparison.Ordinal);
            var copy = Assert.Single(Directory.GetDirectories(server.CopyRoot));
            Assert.Equal(ServerEndpoint.For(copy).Address, (await server.StatusAsync()).Endpoint);
        }
        finally
        {
            // The link itself, not what it points at; then the real directory, which the server's disposal emptied.
            Directory.Delete(linked);
            Directory.Delete(real, recursive: true);
        }
    }

    [Fact]
    public async Task AnInterruptBeforeTheServerAnswersReportsEveryUnitCancelledWithoutFallingBack()
    {
        await using var server = new TestServer();
        using var source = new SourceDirectory(SourceDirectory.Fast);
        using var interrupted = new CancellationTokenSource();
        await interrupted.CancelAsync();

        var (code, output) = server.Verify([source.Path, "--server", "auto"], cancellationToken: interrupted.Token);

        Assert.Equal(1, code);
        Assert.DoesNotContain(FallbackPrefix, output, StringComparison.Ordinal);
        Assert.DoesNotContain("proved (", output, StringComparison.Ordinal);
        Assert.Matches(@"(?m)^  S\.Larger\(\) +cancelled$", output);
        Assert.Matches(@"(?m)^  S\.Inc\(int\) +cancelled$", output);
        Assert.EndsWith("Warrant: 2 verified units, 0 theorems proved, 0 not proved. [server]\n", output, StringComparison.Ordinal);
        // The CLI may have started a server before it saw the interrupt; it is left to be shut down with the test's.
        if (Directory.Exists(server.CopyRoot))
        {
            var deadline = DateTime.UtcNow.AddSeconds(30);
            ServerClient? started;
            while ((started = await server.ConnectAsync()) is null)
            {
                Assert.True(DateTime.UtcNow < deadline, "the started server never answered");
                await Task.Delay(50);
            }
            started.Dispose();
        }
    }

    /// <summary>A directory link: a symbolic link, or on Windows without the privilege to make one, a junction.</summary>
    private static void LinkDirectory(string link, string target)
    {
        try
        {
            Directory.CreateSymbolicLink(link, target);
        }
        catch (Exception ex) when (OperatingSystem.IsWindows() && ex is IOException or UnauthorizedAccessException)
        {
            var mklink = new ProcessStartInfo("cmd.exe") { UseShellExecute = false, RedirectStandardOutput = true };
            foreach (var argument in new[] { "/c", "mklink", "/J", link, target })
            {
                mklink.ArgumentList.Add(argument);
            }
            using var process = Process.Start(mklink)!;
            process.StandardOutput.ReadToEnd();
            process.WaitForExit();
            Assert.True(process.ExitCode == 0, $"mklink /J failed with {process.ExitCode}");
        }
    }

    [Fact]
    public async Task ServerStatusWithNoServerRunningSaysSoAndExitsZero()
    {
        await using var server = new TestServer();
        using var output = new StringWriter { NewLine = "\n" };

        var code = ServerCommand.Run(["status"], output, output, server.Settings);

        Assert.Equal(0, code);
        Assert.Equal($"No Warrant verification server is running for this toolchain (endpoint {server.Settings.Endpoint("unused").Address}).\n", output.ToString());
    }

    [Fact]
    public async Task ServerStatusCancelAndShutdownReachARunningServer()
    {
        await using var server = new TestServer();
        using var fast = new SourceDirectory(SourceDirectory.Fast);
        Assert.Equal(0, server.Verify([fast.Path, "--server", "auto"]).Code);

        var (statusCode, status) = Server(server, "status");
        var (cancelCode, cancel) = Server(server, "cancel", "no-such-request");
        int pid = (await server.StatusAsync()).ProcessId;
        var (shutdownCode, shutdown) = Server(server, "shutdown");
        TestServer.WaitForExit(pid);

        Assert.Equal(0, statusCode);
        Assert.Matches($@"(?m)^process +{pid}$", status);
        Assert.Matches($@"(?m)^toolchain +{Toolchain.Identity}$", status);
        Assert.Matches($@"(?m)^bundle +{TestServer.Hashes.Bundle}$", status);
        Assert.Matches(@"(?m)^cache +0 hits, 2 misses, \d+ tactic runs, 0 rechecked$", status);
        Assert.Matches(@"(?m)^requests +none active$", status);
        Assert.Equal((1, "No request no-such-request is running.\n"), (cancelCode, cancel));
        Assert.Equal((0, $"The server (process {pid}) is shutting down once its running requests finish.\n"), (shutdownCode, shutdown));
        Assert.Null(await server.ConnectAsync());
    }

    private static (int Code, string Output) Server(TestServer server, params string[] args)
    {
        using var output = new StringWriter { NewLine = "\n" };
        var code = ServerCommand.Run(args, output, output, server.Settings);
        return (code, output.ToString());
    }

    private static int CountOf(string text, string value)
    {
        int count = 0;
        for (int at = text.IndexOf(value, StringComparison.Ordinal); at >= 0; at = text.IndexOf(value, at + 1, StringComparison.Ordinal))
        {
            count++;
        }
        return count;
    }

    /// <summary>The output with the fallback message record removed and the summary's path tag dropped.</summary>
    private static string Normalized(string output) => string.Concat(
        output.Split('\n').SkipLast(1)
            .Where(line => !line.Contains(FallbackPrefix, StringComparison.Ordinal))
            .Select(line => line.Replace(" [in-process]", "", StringComparison.Ordinal).Replace(" [server]", "", StringComparison.Ordinal) + "\n"));
}

/// <summary>The tests that start server processes run one at a time, because two of them time a cancellation.</summary>
[CollectionDefinition(Name, DisableParallelization = true)]
public sealed class ServerProcesses
{
    public const string Name = "server processes";
}
