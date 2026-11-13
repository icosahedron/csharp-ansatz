using Warrant.Cic;

namespace Warrant.Semantics;

/// <summary>
/// The Lean names of <c>Warrant.ClrExn</c>, the effect monad's exceptions (plan M6 KTD4, lean/Warrant/Effect.lean), its
/// constructors and its two exception postconditions: the one source the translation and the VC walker share (#232). A
/// test checks <see cref="Constructors"/> against the bundle's inductive.
/// </summary>
public static class ClrExnNames
{
    /// <summary><c>Warrant.ClrExn</c>, the inductive.</summary>
    public static Name Type { get; } = Name.Parse("Warrant.ClrExn");

    /// <summary><c>ClrExn.overflow</c>: a checked operation's overflow.</summary>
    public static Name Overflow { get; } = Type.Append("overflow");

    /// <summary><c>ClrExn.divideByZero</c>: an integer division or remainder by zero.</summary>
    public static Name DivideByZero { get; } = Type.Append("divideByZero");

    /// <summary><c>ClrExn.nullReference</c>: a null value used where a non-null one is required.</summary>
    public static Name NullReference { get; } = Type.Append("nullReference");

    /// <summary><c>ClrExn.invalidOperation</c>: the value of a null nullable read.</summary>
    public static Name InvalidOperation { get; } = Type.Append("invalidOperation");

    /// <summary><c>ClrExn.assertFailed</c>: a failed <c>Spec.Assert</c>, or default-context arithmetic that would wrap (#244).</summary>
    public static Name AssertFailed { get; } = Type.Append("assertFailed");

    /// <summary><c>ClrExn.thrown "key"</c>: an explicit <c>throw</c> of the exception type with that key.</summary>
    public static Name Thrown { get; } = Type.Append("thrown");

    /// <summary><c>ClrExn.external</c>: an exception propagated from a dependency (KTD12).</summary>
    public static Name ExternalException { get; } = Type.Append("external");

    /// <summary>Every constructor, in declaration order.</summary>
    public static IReadOnlyList<Name> Constructors { get; } =
        [Overflow, DivideByZero, NullReference, InvalidOperation, AssertFailed, Thrown, ExternalException];

    /// <summary><c>ClrExn.Allowed</c>: the exception postcondition of a contract (KTD12).</summary>
    public static Name Allowed { get; } = Type.Append("Allowed");

    /// <summary><c>ClrExn.External</c>: the exception postcondition of a <c>Spec.NoThrow</c> contract (#182).</summary>
    public static Name External { get; } = Type.Append("External");

    /// <summary>
    /// The equation of <c>ClrExn.Allowed</c> or <c>ClrExn.External</c> at a constructor, <c>ClrExn.allowed_overflow</c> or
    /// <c>ClrExn.external_overflow</c>, which the VC simp set uses.
    /// </summary>
    /// <param name="postcondition"><see cref="Allowed"/> or <see cref="External"/>.</param>
    /// <param name="constructor">One of <see cref="Constructors"/>.</param>
    /// <returns>The lemma's name.</returns>
    /// <exception cref="ArgumentException">An argument is not one of those.</exception>
    public static Name Equation(Name postcondition, Name constructor)
    {
        string prefix = postcondition == Allowed ? "allowed"
            : postcondition == External ? "external"
            : throw new ArgumentException($"'{postcondition}' is not a ClrExn postcondition.", nameof(postcondition));
        return Constructors.Contains(constructor)
            ? Type.Append($"{prefix}_{constructor.StringComponent}")
            : throw new ArgumentException($"'{constructor}' is not a ClrExn constructor.", nameof(constructor));
    }
}
