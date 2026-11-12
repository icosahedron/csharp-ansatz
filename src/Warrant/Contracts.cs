using System;

namespace Warrant;

/// <summary>
/// Marks a class that states what the members of an interface are assumed to do (milestone M6). Each member of the
/// class implements the interface's member of the same signature with <see cref="Spec.Requires(bool)"/> and
/// <c>Spec.Ensures</c> calls followed by <c>return default!</c>, or with <c>=&gt; default!</c> to assume nothing. A
/// verified method that calls the interface through a dependency is proved for every implementation that keeps these
/// contracts. Nothing in the class is verified or run; the class must be <c>file</c> or <c>internal</c>, <c>abstract</c>,
/// and implement exactly the interface it names.
/// </summary>
[AttributeUsage(AttributeTargets.Class, Inherited = false, AllowMultiple = false)]
public sealed class ContractForAttribute : Attribute
{
    /// <summary>Marks the class as the contract of <paramref name="interface"/>.</summary>
    /// <param name="interface">The interface, written <c>typeof(I)</c>.</param>
    public ContractForAttribute(Type @interface) => Interface = @interface;

    /// <summary>The interface whose members the class states contracts for.</summary>
    public Type Interface { get; }
}

/// <summary>
/// Marks a method that supplies the proof script for another method's contract, in place of the default procedure
/// (milestone M6). The method is static, takes no parameters, returns <see cref="Proof"/>, sits in the same class as the
/// method it proves, and its body is <c>Prove.Contract().By(...)</c>. It is checked by Warrant and never executed.
/// </summary>
[AttributeUsage(AttributeTargets.Method, Inherited = false, AllowMultiple = false)]
public sealed class ProofForAttribute : Attribute
{
    /// <summary>Marks the method as the proof of <paramref name="method"/>'s contract.</summary>
    /// <param name="method">The method proved, written <c>nameof(M)</c>; it must not be overloaded.</param>
    public ProofForAttribute(string method) => Method = method;

    /// <summary>The name of the method whose contract the script proves.</summary>
    public string Method { get; }
}
