namespace Warrant.Cli.Tests;

/// <summary>
/// What the CLI keeps beside the server copies (M5b KTD4): a record of a failed start, so a server that cannot start costs
/// one build the start timeout rather than every build, and the pruning of copies that no build uses any more.
/// </summary>
[Collection(ServerProcesses.Name)]
public sealed class ServerStartTests
{
    private const string FallbackPrefix = "Warrant: verification server unavailable (";

    [Fact]
    public async Task AServerThatFailsToStartIsNotWaitedForAgainUntilTheRetryDelayHasPassed()
    {
        await using var server = new TestServer();
        using var source = new SourceDirectory(SourceDirectory.Fast);
        // A damaged copy: the CLI uses it as it is, and the host cannot run it.
        var copy = ServerLauncher.CopyDirectory(server.Settings, TestServer.Hashes);
        Directory.CreateDirectory(copy);
        File.WriteAllText(Path.Combine(copy, ServerLauncher.ServerAssembly), "not an assembly");
        var record = ServerLauncher.StartFailurePath(copy);
        Func<ServerSettings, ServerSettings> quick = s => s with { StartTimeout = TimeSpan.FromSeconds(3) };

        var (code, output) = server.Verify([source.Path, "--server", "auto"], configure: quick);

        Assert.True(code == 0, output);
        Assert.Contains($"{FallbackPrefix}the server did not start within 3 s); verifying in-process.\n", output, StringComparison.Ordinal);
        Assert.True(File.Exists(record), "the failed start was not recorded");
        var failedAt = File.GetLastWriteTimeUtc(record);

        // The next build falls back at once, without starting the server again.
        var (again, againOutput) = server.Verify([source.Path, "--server", "auto"], configure: quick);

        Assert.True(again == 0, againOutput);
        Assert.Matches(
            @"Warrant: verification server unavailable \(the server failed to start \d+ s ago \(the server did not start within 3 s\); it is tried again 300 s after the failure\); verifying in-process\.\n",
            againOutput);
        Assert.EndsWith("Warrant: 2 verified units, 1 theorems proved, 0 not proved. [in-process]\n", againOutput, StringComparison.Ordinal);
        Assert.Equal(failedAt, File.GetLastWriteTimeUtc(record));

        // Once the retry delay has passed, the server is started again.
        var (retried, retriedOutput) = server.Verify([source.Path, "--server", "auto"], configure: s => quick(s) with { StartRetryDelay = TimeSpan.Zero });

        Assert.True(retried == 0, retriedOutput);
        Assert.Contains($"{FallbackPrefix}the server did not start within 3 s); verifying in-process.\n", retriedOutput, StringComparison.Ordinal);
        Assert.True(File.Exists(record));
    }

    [Fact]
    public async Task ReachingTheServerForgetsAnEarlierFailedStart()
    {
        await using var server = new TestServer();
        using var source = new SourceDirectory(SourceDirectory.Fast);
        Assert.Equal(0, server.Verify([source.Path, "--server", "auto"]).Code);
        var copy = ServerLauncher.CopyDirectory(server.Settings, TestServer.Hashes);
        var record = ServerLauncher.StartFailurePath(copy);
        ServerLauncher.RecordStartFailure(copy, "an earlier failure");

        // A record only holds off a start: a server that runs is used, and the record goes.
        var (code, output) = server.Verify([source.Path, "--server", "auto"]);

        Assert.True(code == 0, output);
        Assert.DoesNotContain(FallbackPrefix, output, StringComparison.Ordinal);
        Assert.EndsWith("[server]\n", output, StringComparison.Ordinal);
        Assert.False(File.Exists(record), "the record of the failed start was kept");
    }

    [Fact]
    public void PruningDeletesOnlyOldCopiesTemporariesAndRecordsAndNeverTheCopyAboutToStart()
    {
        var root = Path.Combine(Path.GetTempPath(), "warrant-prune-" + Guid.NewGuid().ToString("N")[..12]);
        try
        {
            var settings = new ServerSettings { CopyRoot = root };
            var now = DateTime.UtcNow;
            string Hex(char c) => new(c, 32);
            string MakeDirectory(string name, TimeSpan age)
            {
                var path = Path.Combine(root, name);
                Directory.CreateDirectory(path);
                File.WriteAllText(Path.Combine(path, ServerLauncher.ServerAssembly), "");
                Directory.SetLastWriteTimeUtc(path, now - age);
                return path;
            }
            string MakeFile(string name, TimeSpan age)
            {
                var path = Path.Combine(root, name);
                File.WriteAllText(path, "");
                File.SetLastWriteTimeUtc(path, now - age);
                return path;
            }
            var oldCopy = MakeDirectory(Hex('a'), TimeSpan.FromDays(15));
            var usedCopy = MakeDirectory(Hex('b'), TimeSpan.FromDays(13));
            var keep = MakeDirectory(Hex('c'), TimeSpan.FromDays(30));
            var oldTemporary = MakeDirectory(Hex('a') + ".tmp-0123abcd", TimeSpan.FromHours(2));
            var newTemporary = MakeDirectory(Hex('b') + ".tmp-0123abcd", TimeSpan.FromMinutes(10));
            var oldRecord = MakeFile(Hex('a') + ".start-failed", TimeSpan.FromMinutes(6));
            var newRecord = MakeFile(Hex('b') + ".start-failed", TimeSpan.FromMinutes(4));
            var stranger = MakeDirectory("notes", TimeSpan.FromDays(400));
            var strangerFile = MakeFile("notes.txt", TimeSpan.FromDays(400));
            var shortName = MakeDirectory("abc", TimeSpan.FromDays(400));

            ServerLauncher.Prune(settings, keep);

            Assert.False(Directory.Exists(oldCopy));
            Assert.False(Directory.Exists(oldTemporary));
            Assert.False(File.Exists(oldRecord));
            Assert.True(Directory.Exists(usedCopy));
            Assert.True(Directory.Exists(keep));
            Assert.True(Directory.Exists(newTemporary));
            Assert.True(File.Exists(newRecord));
            Assert.True(Directory.Exists(stranger));
            Assert.True(File.Exists(strangerFile));
            Assert.True(Directory.Exists(shortName));

            // A copy root that does not exist is nothing to prune.
            ServerLauncher.Prune(settings with { CopyRoot = Path.Combine(root, "missing") }, keep);
        }
        finally
        {
            Directory.Delete(root, recursive: true);
        }
    }
}
