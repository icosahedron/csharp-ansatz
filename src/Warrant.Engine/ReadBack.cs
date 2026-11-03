using System.Globalization;
using System.Numerics;
using Warrant.Cic;
using Warrant.Kernel;

namespace Warrant.Engine;

/// <summary>A value read back from the kernel, for messages only: verdicts never depend on it (docs/m4/07).</summary>
public abstract record ReadBackValue
{
    private protected ReadBackValue()
    {
    }
}

/// <summary>An <c>int</c>.</summary>
/// <param name="Value">The value.</param>
public sealed record Int32Value(int Value) : ReadBackValue
{
    /// <summary>The value as C# prints it.</summary>
    /// <returns>The decimal text.</returns>
    public override string ToString() => Value.ToString(CultureInfo.InvariantCulture);
}

/// <summary>A <c>long</c>.</summary>
/// <param name="Value">The value.</param>
public sealed record Int64Value(long Value) : ReadBackValue
{
    /// <summary>The value as C# prints it.</summary>
    /// <returns>The decimal text.</returns>
    public override string ToString() => Value.ToString(CultureInfo.InvariantCulture);
}

/// <summary>A <c>bool</c>.</summary>
/// <param name="Value">The value.</param>
public sealed record BoolValue(bool Value) : ReadBackValue
{
    /// <summary>The value as C# writes it.</summary>
    /// <returns><c>true</c> or <c>false</c>.</returns>
    public override string ToString() => Value ? "true" : "false";
}

/// <summary>A value that could not be read back: a type read-back does not cover, or a term that did not reduce.</summary>
/// <param name="Reason">Why, for people.</param>
public sealed record UnknownValue(string Reason) : ReadBackValue
{
    /// <summary>A placeholder for messages.</summary>
    /// <returns><c>unknown</c>.</returns>
    public override string ToString() => "unknown";
}

/// <summary>
/// Reads the value of a closed term back from the kernel (docs/m4/06, 07): an <c>Int32</c> or <c>Int64</c> by reducing
/// <c>BitVec.toNat (T.toBitVec t)</c> to a numeral and reinterpreting its bits as signed, a <c>Bool</c> by reducing it to
/// <c>Bool.true</c> or <c>Bool.false</c>. Any other type is reported as unknown rather than guessed.
/// </summary>
public static class ReadBack
{
    private static readonly Name Int32Name = Name.Parse("Int32");
    private static readonly Name Int64Name = Name.Parse("Int64");
    private static readonly Name BoolName = Name.Parse("Bool");
    private static readonly Name TrueName = Name.Parse("Bool.true");
    private static readonly Name FalseName = Name.Parse("Bool.false");
    private static readonly Expr BitVecToNat = Expr.Const(Name.Parse("BitVec.toNat"));
    private static readonly Expr Int32ToBitVec = Expr.Const(Name.Parse("Int32.toBitVec"));
    private static readonly Expr Int64ToBitVec = Expr.Const(Name.Parse("Int64.toBitVec"));

    /// <summary>Reads back <paramref name="term"/>, of type <paramref name="type"/>, on a large-stack thread.</summary>
    /// <param name="env">An environment with every constant the term mentions.</param>
    /// <param name="term">A closed term.</param>
    /// <param name="type">Its type: <c>Int32</c>, <c>Int64</c>, <c>Bool</c>, or something that reduces to one of them.</param>
    /// <param name="limits">The fuel for the reduction; <see cref="KernelLimits.Corpus"/> when null.</param>
    /// <returns>The value, or <see cref="UnknownValue"/>.</returns>
    public static ReadBackValue Value(KernelEnvironment env, Expr term, Expr type, KernelLimits? limits = null)
    {
        ArgumentNullException.ThrowIfNull(env);
        ArgumentNullException.ThrowIfNull(term);
        ArgumentNullException.ThrowIfNull(type);
        return KernelThread.Run(() => Core(env, term, type, limits ?? KernelLimits.Corpus));
    }

    /// <summary>As <see cref="Value"/>, on the calling thread, which must have a large stack.</summary>
    internal static ReadBackValue Core(KernelEnvironment env, Expr term, Expr type, KernelLimits limits)
    {
        try
        {
            var checker = new TypeChecker(env, limits: limits);
            var head = checker.Whnf(type);
            if (head is not ConstExpr c)
            {
                return new UnknownValue($"values of type {type} are not read back");
            }
            if (c.Name == Int32Name)
            {
                return Bits(checker, Int32ToBitVec, 32, term) is { } n ? new Int32Value(unchecked((int)(uint)n)) : NotANumeral(term);
            }
            if (c.Name == Int64Name)
            {
                return Bits(checker, Int64ToBitVec, 64, term) is { } n ? new Int64Value(unchecked((long)(ulong)n)) : NotANumeral(term);
            }
            if (c.Name == BoolName)
            {
                return checker.Whnf(term) switch
                {
                    ConstExpr { Name: var b } when b == TrueName => new BoolValue(true),
                    ConstExpr { Name: var b } when b == FalseName => new BoolValue(false),
                    var other => new UnknownValue($"{term} reduces to {other}, not to a Boolean"),
                };
            }
            return new UnknownValue($"values of type {type} are not read back");
        }
        catch (KernelException ex)
        {
            return new UnknownValue(ex.Message);
        }
        catch (InsufficientExecutionStackException ex)
        {
            return new UnknownValue(ex.Message);
        }
    }

    /// <summary>The bit pattern of a machine integer, <c>@BitVec.toNat w (toBitVec t)</c> as a numeral; null if it is not one.</summary>
    private static BigInteger? Bits(TypeChecker checker, Expr toBitVec, int width, Expr term)
    {
        var bits = checker.Whnf(Expr.App(BitVecToNat, Expr.NatLit(width), Expr.App(toBitVec, term)));
        return bits is NatLitExpr lit && lit.Value >= 0 && lit.Value < BigInteger.One << width ? lit.Value : null;
    }

    private static UnknownValue NotANumeral(Expr term) => new($"{term} does not reduce to a numeral");
}
