// Polyfill for netstandard2.0, which this project targets; the compiler finds it by name.
namespace System.Runtime.CompilerServices;

/// <summary>Enables <c>init</c> accessors, and so records, on netstandard2.0.</summary>
internal static class IsExternalInit
{
}
