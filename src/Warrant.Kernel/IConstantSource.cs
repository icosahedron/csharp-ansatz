using System.Diagnostics.CodeAnalysis;
using Warrant.Cic;

namespace Warrant.Kernel;

/// <summary>
/// Constants a base <see cref="KernelEnvironment"/> reads on demand instead of holding them (M5b KTD18), such as a store of
/// an imported Lean library. The kernel trusts what a source returns, exactly as it trusts what it admitted itself, so a
/// source is a trusted import: only a store creates one, never a cache.
/// </summary>
/// <remarks>
/// Many threads may look up constants at once, so <see cref="TryGet"/> must be thread-safe, and it must return the same
/// constant for a name every time. The kernel never writes to a source.
/// </remarks>
public interface IConstantSource
{
    /// <summary>Looks up a constant by name.</summary>
    /// <param name="name">The name.</param>
    /// <param name="constant">The constant, when the source has it.</param>
    /// <returns>Whether the source has a constant of that name.</returns>
    bool TryGet(Name name, [NotNullWhen(true)] out ConstantInfo? constant);

    /// <summary>The number of constants in the source.</summary>
    int Count { get; }

    /// <summary>
    /// Whether the source claims to hold the quotient constants. The environment believes the claim only when the source's
    /// <c>Quot</c>, <c>Quot.mk</c>, <c>Quot.lift</c> and <c>Quot.ind</c> are exactly the ones the kernel generates.
    /// </summary>
    bool QuotientsInitialized { get; }
}
