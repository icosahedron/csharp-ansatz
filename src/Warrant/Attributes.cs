using System;

namespace Warrant;

/// <summary>
/// Marks a method or property whose body Warrant translates into CIC and checks.
/// </summary>
[AttributeUsage(AttributeTargets.Method | AttributeTargets.Property, Inherited = false)]
public sealed class VerifiedAttribute : Attribute
{
}

/// <summary>
/// Marks a method whose body states a theorem with <see cref="Prove.That(bool)"/>, optionally followed by a proof
/// script with <see cref="Proof.By(Tactic[])"/>. The theorem's parameters are universally quantified.
/// Theorem methods are checked by Warrant and never executed.
/// </summary>
/// <remarks>
/// The budget properties override the project's settings for this theorem; zero, the default, means the project's
/// setting. Running out of any of them fails the theorem with WRT0006.
/// </remarks>
[AttributeUsage(AttributeTargets.Method, Inherited = false)]
public sealed class TheoremAttribute : Attribute
{
    /// <summary>The wall-clock limit for proving this theorem, in seconds; zero means the project's setting.</summary>
    public int TimeoutSeconds { get; set; }

    /// <summary>The fuel the proof script's tactics may spend; zero means the project's setting.</summary>
    public long TacticFuel { get; set; }

    /// <summary>The fuel the kernel may spend checking this theorem; zero means the project's setting.</summary>
    public long KernelFuel { get; set; }
}

/// <summary>
/// Marks an enum or class whose only values are its named members: an enum's declared members,
/// or the static instances of a sealed class with private constructors. Warrant models such a type
/// as exactly those values and records that as an assumption.
/// </summary>
[AttributeUsage(AttributeTargets.Enum | AttributeTargets.Class, Inherited = false)]
public sealed class ClosedAttribute : Attribute
{
}

/// <summary>
/// The return type of a <see cref="TheoremAttribute"/> method.
/// No instance is ever created; it exists only so a theorem has a type to return.
/// </summary>
public sealed class Proof
{
    private Proof()
    {
    }

    /// <summary>
    /// The proof script: tactics run in order on the theorem's goal, after its parameters are introduced.
    /// Warrant reads the script from source; the call never runs, because <see cref="Prove.That(bool)"/> throws first.
    /// </summary>
    /// <param name="steps">The tactics, in order.</param>
    /// <returns>This proof.</returns>
    public Proof By(params Tactic[] steps) => this;
}
