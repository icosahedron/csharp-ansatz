using System.Collections.Concurrent;
using System.Runtime.ExceptionServices;
using Warrant.Kernel;

namespace Warrant.Engine.Service;

/// <summary>
/// Long-lived worker threads with the kernel's large stack (M5b KTD8, docs/m5b/03): the theorems of every request a
/// <see cref="VerificationService"/> serves run on them, first come first served. The kernel and Meta recurse deeply, so
/// each worker has <see cref="KernelThread.DefaultStackSize"/> of stack, as <see cref="KernelThread.Run(Action, int)"/>
/// gives one call.
/// </summary>
public sealed class WorkerPool : IDisposable
{
    private readonly BlockingCollection<Action> _queue = [];
    private readonly Thread[] _threads;

    /// <summary>Starts <paramref name="size"/> workers.</summary>
    /// <param name="size">The number of workers; at least 1.</param>
    /// <param name="stackSize">Each worker's stack size.</param>
    /// <exception cref="ArgumentOutOfRangeException"><paramref name="size"/> is less than 1.</exception>
    public WorkerPool(int size, int stackSize = KernelThread.DefaultStackSize)
    {
        ArgumentOutOfRangeException.ThrowIfLessThan(size, 1);
        _threads = new Thread[size];
        for (int i = 0; i < size; i++)
        {
            _threads[i] = new Thread(Work, stackSize) { Name = $"Warrant worker {i + 1}", IsBackground = true };
            _threads[i].Start();
        }
    }

    /// <summary>The default number of workers: one fewer than the processors, at most 8 and at least 1.</summary>
    public static int DefaultSize => Math.Clamp(Environment.ProcessorCount - 1, 1, 8);

    /// <summary>The number of workers.</summary>
    public int Size => _threads.Length;

    /// <summary>
    /// Runs every item of <paramref name="work"/> on the workers and waits for all of them; the results are in the order of
    /// <paramref name="work"/>, whatever order the workers finish in.
    /// </summary>
    /// <typeparam name="T">The result type.</typeparam>
    /// <param name="work">The items.</param>
    /// <returns>The results.</returns>
    /// <exception cref="ObjectDisposedException">The pool was disposed.</exception>
    /// <remarks>An item that throws is rethrown here, after every item has finished.</remarks>
    public T[] RunAll<T>(IEnumerable<Func<T>> work)
    {
        ArgumentNullException.ThrowIfNull(work);
        var items = work.ToList();
        var results = new T[items.Count];
        var errors = new ExceptionDispatchInfo?[items.Count];
        using var done = new CountdownEvent(items.Count);
        for (int i = 0; i < items.Count; i++)
        {
            int index = i;
            _queue.Add(() =>
            {
                try
                {
                    results[index] = items[index]();
                }
#pragma warning disable CA1031 // Rethrown on the calling thread.
                catch (Exception ex)
#pragma warning restore CA1031
                {
                    errors[index] = ExceptionDispatchInfo.Capture(ex);
                }
                finally
                {
                    done.Signal();
                }
            });
        }
        done.Wait();
        foreach (var error in errors)
        {
            error?.Throw();
        }
        return results;
    }

    /// <summary>Lets the workers finish the work already queued, then stops them.</summary>
    public void Dispose()
    {
        if (_queue.IsAddingCompleted)
        {
            return;
        }
        _queue.CompleteAdding();
        foreach (var thread in _threads)
        {
            thread.Join();
        }
        _queue.Dispose();
    }

    private void Work()
    {
        foreach (var item in _queue.GetConsumingEnumerable())
        {
            item();
        }
    }
}
