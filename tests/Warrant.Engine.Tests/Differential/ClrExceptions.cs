using Warrant.Cic;

namespace Warrant.Engine.Tests.Differential;

/// <summary>
/// Each <c>Warrant.ClrExn</c> constructor and the CLR exception type it stands for (plan M6 U13, KTD21, #78). The mapping
/// runs from the model to the CLR: an error is right when the CLR threw exactly the type its constructor maps to.
/// <list type="bullet">
/// <item><c>overflow</c>: <see cref="OverflowException"/>; <c>divideByZero</c>: <see cref="DivideByZeroException"/>;
/// <c>invalidOperation</c>: <see cref="InvalidOperationException"/>; <c>nullReference</c>: <see cref="NullReferenceException"/>.</item>
/// <item><c>thrown k</c>: the type whose documentation-comment ID is <c>k</c>, so an explicit
/// <c>throw new InvalidOperationException()</c> and a <c>Value</c> read of <c>null</c> both match the CLR's
/// <see cref="InvalidOperationException"/>: the CLR cannot tell them apart, and each of the two model errors is accepted.</item>
/// <item><c>assertFailed</c>: no CLR counterpart. <c>Spec.Assert</c> is <c>[Conditional]</c> and does nothing at run time,
/// so an input on which the model fails an assertion is skipped and counted (#186).</item>
/// <item><c>external</c>: <see cref="MockException"/>, the sentinel a mocked dependency throws (plan U22), and nothing else;
/// the sentinel matches nothing but <c>external</c>.</item>
/// </list>
/// </summary>
internal static class ClrExceptions
{
    /// <summary>The <c>ClrExn</c> constructors that stand for one CLR exception type, by their last name component.</summary>
    public static IReadOnlyDictionary<string, Type> Implicit { get; } = new Dictionary<string, Type>(StringComparer.Ordinal)
    {
        ["overflow"] = typeof(OverflowException),
        ["divideByZero"] = typeof(DivideByZeroException),
        ["invalidOperation"] = typeof(InvalidOperationException),
        ["nullReference"] = typeof(NullReferenceException),
    };

    /// <summary>The constructor for an explicit throw, <c>thrown (type : String)</c>.</summary>
    public const string Thrown = "thrown";

    /// <summary>The constructor of a failed <c>Spec.Assert</c>, which has no CLR counterpart (#186).</summary>
    public const string AssertFailed = "assertFailed";

    /// <summary>The constructor of an exception a dependency throws (plan U22): <see cref="MockException"/>.</summary>
    public const string External = "external";

    /// <summary><c>Warrant.ClrExn</c>.</summary>
    public static readonly Name Type = Name.Parse("Warrant.ClrExn");

    /// <summary>The constant <c>Warrant.ClrExn.c</c>.</summary>
    public static Expr Constructor(string name) => Expr.Const(Type.Append(name));

    /// <summary><c>ClrExn.thrown "k"</c>.</summary>
    public static Expr ThrownOf(string key) => Expr.App(Constructor(Thrown), Expr.StrLit(key));

    /// <summary>The documentation-comment ID of a CLR type, as extraction keys a thrown type (<c>T:System.ArgumentException</c>).</summary>
    public static string Key(Type type) => "T:" + type.FullName!.Replace('+', '.');

    /// <summary>
    /// The model errors that a CLR exception matches: the implicit constructor mapped to its exact type, if any, and
    /// <c>thrown</c> of its key.
    /// </summary>
    public static IReadOnlyList<Expr> ModelErrors(Exception exception)
    {
        ArgumentNullException.ThrowIfNull(exception);
        if (exception is MockException)
        {
            // A mocked dependency threw: only external stands for it (plan U22).
            return [Constructor(External)];
        }
        var type = exception.GetType();
        var errors = Implicit.Where(m => m.Value == type).Select(m => Constructor(m.Key)).ToList();
        errors.Add(ThrownOf(Key(type)));
        return errors;
    }
}
