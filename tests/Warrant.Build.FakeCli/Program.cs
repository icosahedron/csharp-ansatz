// A stand-in for `warrant.dll` that replays a scripted run, for the Warrant.Build task's tests.
//
// It reads `fake-cli/` in its working directory, which the task sets to the project directory:
//   stdout.txt    copied byte for byte to standard output (absent: nothing)
//   stderr.txt    copied byte for byte to standard error (absent: nothing)
//   exitcode.txt  the exit code (absent: 0)
// and records each run's arguments, one per line, in `fake-cli/invocation-<n>.txt`.

var dir = Path.Combine(Environment.CurrentDirectory, "fake-cli");
Directory.CreateDirectory(dir);

var n = 1;
while (File.Exists(Path.Combine(dir, $"invocation-{n}.txt")))
{
    n++;
}

File.WriteAllLines(Path.Combine(dir, $"invocation-{n}.txt"), args);

Replay(Path.Combine(dir, "stdout.txt"), Console.OpenStandardOutput());
Replay(Path.Combine(dir, "stderr.txt"), Console.OpenStandardError());

var exitCodeFile = Path.Combine(dir, "exitcode.txt");
return File.Exists(exitCodeFile) ? int.Parse(File.ReadAllText(exitCodeFile).Trim(), System.Globalization.CultureInfo.InvariantCulture) : 0;

static void Replay(string path, Stream stream)
{
    if (File.Exists(path))
    {
        var bytes = File.ReadAllBytes(path);
        stream.Write(bytes, 0, bytes.Length);
        stream.Flush();
    }
}
