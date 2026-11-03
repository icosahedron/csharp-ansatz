using System.Diagnostics;
using Warrant.Cic;
using Warrant.Kernel;
using Warrant.Semantics;
using Warrant.Vir;

namespace Warrant.Engine.Tests.Differential;

/// <summary>
/// The per-input check of KTD14: the theorem <c>model = r</c>, where <c>r</c> is the literal .NET result, proved by
/// <c>@Eq.refl.{1} T model</c> and admitted into a scratch fork of the run's environment. The kernel accepts it exactly
/// when both sides are definitionally equal, the same check that proves a C# theorem; read-back only fills in messages.
/// </summary>
internal sealed class ModelCheck(KernelEnvironment env, Values values, KernelLimits limits)
{
    private static readonly Name TheoremName = Name.Parse("Warrant.Differential.agrees");

    /// <summary><c>Eq.{1}</c>: every type M4 translates (Int32, Int64, Bool, records, closed types) lives in <c>Type</c>.</summary>
    private static readonly Expr Eq = Expr.Const(Name.Parse("Eq"), Level.One);

    private static readonly Expr EqRefl = Expr.Const(Name.Parse("Eq.refl"), Level.One);

    public KernelEnvironment Env { get; } = env;

    public Values Values { get; } = values;

    /// <summary>The application <c>f a₁ … aₙ</c> of a function unit to .NET arguments (the receiver first for an instance member).</summary>
    public Expr Application(VirUnit unit, IReadOnlyList<object?> args)
    {
        var types = ParameterTypes(unit);
        return Expr.App(Expr.Const(LeanNames.ForKey(unit.Key)), [.. types.Select((t, i) => Values.Term(t, args[i]))]);
    }

    /// <summary>A function unit's parameter types, the receiver's first for an instance member.</summary>
    public static IReadOnlyList<VirType> ParameterTypes(VirUnit unit) =>
        [.. (unit.Self is { } self ? [VirType.Ref(self)] : Array.Empty<VirType>()), .. (unit.Params ?? VirList<VirParam>.Empty).Select(p => p.Type)];

    /// <summary>The theorem <c>@Eq.{1} T model expected</c>, proved by <c>@Eq.refl.{1} T model</c>.</summary>
    public static TheoremDecl Theorem(Expr type, Expr model, Expr expected) =>
        new(new TheoremInfo(
            TheoremName,
            EquatableArray<Name>.Empty,
            Expr.App(Eq, type, model, expected),
            Expr.App(EqRefl, type, model),
            EquatableArray.Create(TheoremName)));

    /// <summary>
    /// Whether the model agrees with a .NET result: null if the kernel admits <c>model = result</c>, else a message with
    /// both values. Must run on a kernel thread.
    /// </summary>
    /// <param name="description">The call, as C# would write it, for the message.</param>
    public string? Disagreement(string description, VirType type, Expr model, object? result)
    {
        Expr expected;
        try
        {
            expected = Values.Term(type, result);
        }
        catch (ModelGapException ex)
        {
            return $"{description}: the CLR returned {Values.Display(type, result)}, which the model cannot produce ({ex.Message}); "
                + $"the model computes {Values.ReadBackDisplay(Env, type, model, limits)}";
        }
        try
        {
            Kernel.Kernel.Add(Env.Fork(), Theorem(Values.CicType(type), model, expected), limits);
            return null;
        }
        catch (KernelException ex)
        {
            return $"{description}: the CLR returned {Values.Display(type, result)} but the model computes "
                + $"{Values.ReadBackDisplay(Env, type, model, limits)} (kernel: {FirstLine(ex.Message)})";
        }
    }

    /// <summary>
    /// The fuel and wall-clock time of the checks <see cref="Kernel.Kernel.Add"/> makes for this theorem (type, proof,
    /// definitional equality), measured on a fresh checker. Must run on a kernel thread.
    /// </summary>
    public (long Fuel, TimeSpan Elapsed) Measure(VirType type, Expr model, object? result)
    {
        var theorem = Theorem(Values.CicType(type), model, Values.Term(type, result)).Value;
        var watch = Stopwatch.StartNew();
        var checker = new TypeChecker(Env.Fork(), limits: limits);
        checker.Check(theorem.Type, theorem.LevelParams);
        var proofType = checker.Check(theorem.Proof, theorem.LevelParams);
        Assert.True(checker.IsDefEq(proofType, theorem.Type));
        return (checker.FuelUsed, watch.Elapsed);
    }

    private static string FirstLine(string message)
    {
        var newline = message.IndexOfAny(['\r', '\n']);
        return newline < 0 ? message : message[..newline];
    }
}
