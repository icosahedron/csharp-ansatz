namespace Warrant.Kernel;

/// <summary>A declaration was rejected by the kernel.</summary>
public class KernelException : Exception
{
    /// <summary>Creates the exception.</summary>
    public KernelException()
    {
    }

    /// <summary>Creates the exception with a message.</summary>
    public KernelException(string message)
        : base(message)
    {
    }

    /// <summary>Creates the exception with a message and inner exception.</summary>
    public KernelException(string message, Exception innerException)
        : base(message, innerException)
    {
    }
}

/// <summary>
/// The kernel ran out of fuel (its step budget) or hit a size limit. The declaration is rejected
/// conservatively; it may well be correct, but checking it needs a bigger budget.
/// </summary>
public sealed class KernelResourceException : KernelException
{
    /// <summary>Creates the exception.</summary>
    public KernelResourceException()
    {
    }

    /// <summary>Creates the exception with a message.</summary>
    public KernelResourceException(string message)
        : base(message)
    {
    }

    /// <summary>Creates the exception with a message and inner exception.</summary>
    public KernelResourceException(string message, Exception innerException)
        : base(message, innerException)
    {
    }
}
