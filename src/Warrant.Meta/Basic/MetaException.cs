namespace Warrant.Meta;

/// <summary>A Meta operation failed (Lean's <c>throwError</c> in <c>MetaM</c>).</summary>
/// <remarks>
/// Meta is untrusted: a failure here only means a tactic could not build a term. Nothing Meta
/// produces counts as proved until the kernel admits it.
/// </remarks>
public class MetaException : Exception
{
    /// <summary>Creates the exception.</summary>
    public MetaException()
    {
    }

    /// <summary>Creates the exception with a message.</summary>
    public MetaException(string message)
        : base(message)
    {
    }

    /// <summary>Creates the exception with a message and inner exception.</summary>
    public MetaException(string message, Exception innerException)
        : base(message, innerException)
    {
    }
}

/// <summary>
/// Meta ran out of its own fuel or passed the theorem's deadline (Lean's <c>maxHeartbeats</c> and
/// <c>checkSystem</c>). It is reported separately from the kernel's fuel.
/// </summary>
public sealed class MetaResourceException : MetaException
{
    /// <summary>Creates the exception.</summary>
    public MetaResourceException()
    {
    }

    /// <summary>Creates the exception with a message.</summary>
    public MetaResourceException(string message)
        : base(message)
    {
    }

    /// <summary>Creates the exception with a message and inner exception.</summary>
    public MetaResourceException(string message, Exception innerException)
        : base(message, innerException)
    {
    }
}
