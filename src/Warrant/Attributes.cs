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
/// Marks a method whose body states a theorem with <see cref="Prove.That(bool)"/>.
/// Theorem methods are checked by Warrant and never executed.
/// </summary>
[AttributeUsage(AttributeTargets.Method, Inherited = false)]
public sealed class TheoremAttribute : Attribute
{
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
}
