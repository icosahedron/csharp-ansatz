using Warrant.Engine.Service;

namespace Warrant.Engine.Tests;

/// <summary>
/// The worker pool (M5b KTD8): results in the order of the work whatever order the workers finish in, an item's exception
/// rethrown on the caller after every item has finished, and a pool disposed while work is queued is an
/// <see cref="ObjectDisposedException"/>, never a crash on a worker.
/// </summary>
public sealed class WorkerPoolTests
{
    [Fact]
    public void ResultsComeBackInTheOrderOfTheWorkWhateverOrderTheyFinishIn()
    {
        using var pool = new WorkerPool(4);
        // The first items take longest, so they finish last.
        var results = pool.RunAll(Enumerable.Range(0, 8).Select(i => (Func<int>)(() =>
        {
            Thread.Sleep((8 - i) * 10);
            return i * i;
        })));
        Assert.Equal(Enumerable.Range(0, 8).Select(i => i * i), results);
    }

    [Fact]
    public void AnItemsExceptionIsRethrownAfterEveryItemHasFinishedAndTheWorkersLiveOn()
    {
        using var pool = new WorkerPool(1);
        int finished = 0;
        var ex = Assert.Throws<InvalidOperationException>(() => pool.RunAll(new Func<int>[]
        {
            () => throw new InvalidOperationException("boom"),
            () => Interlocked.Increment(ref finished),
            () => Interlocked.Increment(ref finished),
        }));
        Assert.Equal("boom", ex.Message);
        Assert.Equal(2, finished);
        // The one worker is still there.
        Assert.Equal(new[] { 7 }, pool.RunAll(new Func<int>[] { () => 7 }));
    }

    [Fact]
    public void RunningWorkOnAPoolBeingDisposedIsObjectDisposed()
    {
        var pool = new WorkerPool(1);
        using var started = new ManualResetEventSlim();
        using var gate = new ManualResetEventSlim();
        var busy = new Thread(() => pool.RunAll(new Func<int>[] { () => { started.Set(); gate.Wait(); return 0; } }));
        busy.Start();
        started.Wait();

        // Dispose completes adding, then waits for the busy worker: the queue no longer takes work but is not disposed.
        var disposing = new Thread(pool.Dispose);
        disposing.Start();
        Assert.True(SpinWait.SpinUntil(() => (disposing.ThreadState & ThreadState.WaitSleepJoin) != 0, TimeSpan.FromSeconds(10)));

        Assert.Throws<ObjectDisposedException>(() => pool.RunAll(new Func<int>[] { () => 1 }));

        gate.Set();
        busy.Join();
        disposing.Join();
        Assert.Throws<ObjectDisposedException>(() => pool.RunAll(new Func<int>[] { () => 1 }));
    }
}
