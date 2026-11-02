using System.Runtime.ExceptionServices;

namespace Warrant.Kernel;

/// <summary>
/// Runs kernel work on a dedicated thread with a large stack.
/// </summary>
/// <remarks>
/// The kernel is recursive, like Lean's C++ kernel (which runs with large native stacks). Real proof
/// terms can be thousands of levels deep, far beyond the default 1 MB .NET stack. Only the address
/// space is reserved up front; pages are committed as the stack grows.
/// </remarks>
public static class KernelThread
{
    /// <summary>The default stack size: 512 MB.</summary>
    public const int DefaultStackSize = 512 * 1024 * 1024;

    /// <summary>Runs <paramref name="work"/> on a large-stack thread and returns its result (rethrowing its exception).</summary>
    public static T Run<T>(Func<T> work, int stackSize = DefaultStackSize)
    {
        ArgumentNullException.ThrowIfNull(work);
        T result = default!;
        ExceptionDispatchInfo? error = null;
        var thread = new Thread(
            () =>
            {
                try
                {
                    result = work();
                }
#pragma warning disable CA1031 // Rethrown on the calling thread.
                catch (Exception ex)
#pragma warning restore CA1031
                {
                    error = ExceptionDispatchInfo.Capture(ex);
                }
            },
            stackSize)
        {
            Name = "Warrant kernel",
            IsBackground = true,
        };
        thread.Start();
        thread.Join();
        error?.Throw();
        return result;
    }

    /// <summary>Runs <paramref name="work"/> on a large-stack thread (rethrowing its exception).</summary>
    public static void Run(Action work, int stackSize = DefaultStackSize)
    {
        ArgumentNullException.ThrowIfNull(work);
        Run<bool>(() =>
        {
            work();
            return true;
        }, stackSize);
    }
}
