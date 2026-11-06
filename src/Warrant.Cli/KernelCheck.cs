using System.Diagnostics;
using System.Globalization;
using Warrant.Cic;
using Warrant.Kernel;

/// <summary>
/// What <c>warrant check</c> and <c>warrant check-store</c> share: each declaration through the kernel in order, a line per
/// rejection, and the summary, with the Lean Kernel Arena's exit codes.
/// </summary>
internal static class KernelCheck
{
    /// <summary>Checks the declarations and reports.</summary>
    /// <param name="checker">The checker, on the environment to extend.</param>
    /// <param name="declarations">The declarations, in order.</param>
    /// <param name="output">Where the lines go.</param>
    /// <param name="quiet">Print only the summary.</param>
    /// <param name="slowest">Also print this many of the slowest declarations.</param>
    /// <param name="started">Measures the run, reading included.</param>
    /// <returns>0 when every declaration was accepted, 1 when the first failure was a rejection, 2 when it was a declined one.</returns>
    public static int Run(ExportChecker checker, IEnumerable<Declaration> declarations, TextWriter output, bool quiet, int slowest, Stopwatch started)
    {
        int accepted = 0, rejected = 0, declined = 0;
        CheckResult? firstFailure = null;
        // The cost of each result: its checking time, and the memory the checking thread allocated since the previous
        // result (results come back on that thread, so reading the declaration is included in the memory).
        var costs = new PriorityQueue<(string Name, double Seconds, long Bytes), double>();
        long lastBytes = -1;
        checker.CheckAll(declarations, r =>
        {
            if (slowest > 0)
            {
                long bytes = GC.GetAllocatedBytesForCurrentThread();
                if (lastBytes >= 0)
                {
                    costs.Enqueue((r.Name.ToString(), r.Elapsed.TotalSeconds, bytes - lastBytes), r.Elapsed.TotalSeconds);
                    if (costs.Count > slowest)
                    {
                        costs.Dequeue();
                    }
                }
                lastBytes = bytes;
            }
            if (r.Accepted)
            {
                accepted++;
                return;
            }
            if (r.ResourceLimit)
            {
                declined++;
            }
            else
            {
                rejected++;
            }
            firstFailure ??= r;
            if (!quiet)
            {
                var label = r.ResourceLimit ? "DECLINED" : "REJECTED";
                output.WriteLine($"{label} {r.Name}: {r.Error}");
            }
        });
        output.WriteLine($"accepted {accepted:N0}, rejected {rejected:N0}, declined {declined:N0}; {checker.Env.Count:N0} constants in {started.Elapsed.TotalSeconds:F1}s");
        if (slowest > 0)
        {
            output.WriteLine($"slowest {costs.Count} (seconds, MB allocated, name):");
            var top = new List<(string Name, double Seconds, long Bytes)>();
            while (costs.Count > 0)
            {
                top.Add(costs.Dequeue());
            }
            foreach (var (name, seconds, bytes) in Enumerable.Reverse(top))
            {
                output.WriteLine(string.Create(CultureInfo.InvariantCulture, $"  {seconds,9:F3}  {bytes / (1024.0 * 1024.0),9:F1}  {name}"));
            }
        }
        return firstFailure is null ? 0 : firstFailure.ResourceLimit ? 2 : 1;
    }
}
