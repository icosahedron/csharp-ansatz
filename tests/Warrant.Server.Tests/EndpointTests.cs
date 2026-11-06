using System.Diagnostics;
using System.Runtime.Versioning;
using Warrant.Engine.Service;

namespace Warrant.Server.Tests;

/// <summary>A fact that runs only on Linux and macOS, and says so when it is skipped.</summary>
public sealed class UnixFactAttribute : FactAttribute
{
    public UnixFactAttribute()
    {
        if (OperatingSystem.IsWindows())
        {
            Skip = "Unix only: Windows uses a CurrentUserOnly named pipe, not a socket directory";
        }
    }
}

/// <summary>A fact that runs only on Windows, and says so when it is skipped.</summary>
public sealed class WindowsFactAttribute : FactAttribute
{
    public WindowsFactAttribute()
    {
        if (!OperatingSystem.IsWindows())
        {
            Skip = "Windows only: a named-pipe instance a client left before the server waited on it";
        }
    }
}

/// <summary>
/// The endpoint (M5b plan U8, KTD3): its name, the per-user socket directory's checks on Unix, and the log (KTD4).
/// </summary>
[Collection(ServerGroup.Name)]
public sealed class EndpointTests(ServiceFixture fixture)
{
    private const string Identity = "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef";

    [Fact]
    public void TheNameIsAShortStableHashThatEachInputChanges()
    {
        var directory = Path.Combine(Path.GetTempPath(), "server");
        var name = ServerEndpoint.NameFor("alice", false, directory, Identity);

        Assert.Equal(ServerEndpoint.NameLength, name.Length);
        Assert.Matches("^[A-Za-z0-9_-]+$", name);
        Assert.Equal(name, ServerEndpoint.NameFor("alice", false, directory + Path.DirectorySeparatorChar, Identity));
        Assert.NotEqual(name, ServerEndpoint.NameFor("bob", false, directory, Identity));
        Assert.NotEqual(name, ServerEndpoint.NameFor("alice", true, directory, Identity));
        Assert.NotEqual(name, ServerEndpoint.NameFor("alice", false, directory + "2", Identity));
        Assert.NotEqual(name, ServerEndpoint.NameFor("alice", false, directory, Identity.Replace('0', '1')));
    }

    [Fact]
    public void TheEnvironmentVariableReplacesTheNameButNotTheDirectory()
    {
        var previous = Environment.GetEnvironmentVariable(ServerEndpoint.EnvironmentVariable);
        try
        {
            Environment.SetEnvironmentVariable(ServerEndpoint.EnvironmentVariable, "wt-override");
            var endpoint = ServerEndpoint.For(AppContext.BaseDirectory);
            Assert.Equal("wt-override", endpoint.Name);
            Assert.Equal(OperatingSystem.IsWindows() ? null : ServerEndpoint.DefaultSocketDirectory(), endpoint.SocketDirectory);

            Environment.SetEnvironmentVariable(ServerEndpoint.EnvironmentVariable, "../escape");
            Assert.Throws<ArgumentException>(() => ServerEndpoint.For(AppContext.BaseDirectory));
        }
        finally
        {
            Environment.SetEnvironmentVariable(ServerEndpoint.EnvironmentVariable, previous);
        }
    }

    [Fact]
    public void TheLogIsRotatedOnceItPassesItsCap()
    {
        var path = Path.Combine(Path.GetTempPath(), $"warrant-log-test-{Guid.NewGuid():N}", "server.log");
        try
        {
            var log = new ServerLog(path, maxBytes: 200);
            for (int i = 0; i < 10; i++)
            {
                log.Write($"line {i} {new string('x', 40)}");
            }
            Assert.True(new FileInfo(path).Length < 200 + 120, "the current log passed its cap by more than a line");
            Assert.Contains("line 9", File.ReadAllText(path), StringComparison.Ordinal);
            Assert.True(File.Exists(path + ".1"));
            Assert.DoesNotContain("line 9", File.ReadAllText(path + ".1"), StringComparison.Ordinal);
        }
        finally
        {
            Directory.Delete(Path.GetDirectoryName(path)!, recursive: true);
        }
    }

    [UnixFact]
    [UnsupportedOSPlatform("windows")]
    public async Task TheSocketsDirectoryHasMode0700()
    {
        await using var server = HostedServer.Start(fixture.Service);
        var directory = server.Endpoint.SocketDirectory!;

        Assert.Equal(UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute, File.GetUnixFileMode(directory));
        Assert.Null(new DirectoryInfo(directory).LinkTarget);
        Assert.Contains(server.Endpoint.Address, Directory.GetFileSystemEntries(directory));
        Assert.True(ServerEndpoint.CheckDirectory(directory, out var problem), problem);
    }

    [UnixFact]
    [UnsupportedOSPlatform("windows")]
    public void ASocketDirectoryWithMode0777MakesTheServerRefuseToStart()
    {
        var directory = TempDirectory();
        try
        {
            Directory.CreateDirectory(directory);
            File.SetUnixFileMode(directory, (UnixFileMode)0x1FF);

            AssertRefused(directory, "has mode 777");
        }
        finally
        {
            Directory.Delete(directory, recursive: true);
        }
    }

    [UnixFact]
    [UnsupportedOSPlatform("windows")]
    public void ASocketDirectoryThatIsASymlinkMakesTheServerRefuseToStart()
    {
        var target = TempDirectory();
        var link = TempDirectory();
        try
        {
            Directory.CreateDirectory(target, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
            Directory.CreateSymbolicLink(link, target);

            AssertRefused(link, "is not a directory");
        }
        finally
        {
            File.Delete(link);
            Directory.Delete(target, recursive: true);
        }
    }

    [UnixFact]
    [UnsupportedOSPlatform("windows")]
    public void ASocketDirectoryOwnedByAnotherUserMakesTheServerRefuseToStart()
    {
        // Giving a directory away takes root; as anyone else, a directory root owns stands in for another user's.
        var directory = Environment.IsPrivilegedProcess ? TempDirectory() : "/";
        try
        {
            if (Environment.IsPrivilegedProcess)
            {
                Directory.CreateDirectory(directory, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
                using var chown = Process.Start("chown", ["65534", directory])!;
                chown.WaitForExit();
                Assert.Equal(0, chown.ExitCode);
            }

            AssertRefused(directory, "is owned by user");
        }
        finally
        {
            if (Environment.IsPrivilegedProcess)
            {
                Directory.Delete(directory, recursive: true);
            }
        }
    }

    /// <summary>The server refuses the directory, and the check a client makes (U9) refuses it too.</summary>
    private static void AssertRefused(string directory, string reason)
    {
        var endpoint = ServerEndpoint.Named("wt-refused", directory);
        var error = Assert.Throws<EndpointRefusedException>(() => ServerHost.TryAcquire(endpoint, new ServerLog(Path.Combine(directory, "unused.log")), ServerHost.DefaultIdleTimeout));
        Assert.Contains(reason, error.Message, StringComparison.Ordinal);
        Assert.False(ServerEndpoint.CheckDirectory(directory, out var problem));
        Assert.Contains(reason, problem, StringComparison.Ordinal);
        Assert.False(File.Exists(endpoint.Address));
    }

    private static string TempDirectory() => Path.Combine(Path.GetTempPath(), $"wt-{Guid.NewGuid():N}"[..19]);
}
