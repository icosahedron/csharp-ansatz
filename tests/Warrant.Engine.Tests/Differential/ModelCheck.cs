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
    public string? Disagreement(string description, VirType type, Expr model, object? result) =>
        Disagreement(description, type, model, result, limits, reportFuel: true);

    /// <summary>
    /// <see cref="Disagreement(string, VirType, Expr, object?)"/> with the given fuel; running out of it throws
    /// <see cref="KernelResourceException"/> rather than reporting a disagreement, so that a recursive unit's caller can
    /// count the input as skipped (docs/m5a/08, "Bounded inputs"). Must run on a kernel thread.
    /// </summary>
    public string? DisagreementWithin(string description, VirType type, Expr model, object? result, KernelLimits fuel) =>
        Disagreement(description, type, model, result, fuel, reportFuel: false);

    private string? Disagreement(string description, VirType type, Expr model, object? result, KernelLimits fuel, bool reportFuel)
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
            Kernel.Kernel.Add(Env.Fork(), Theorem(Values.CicType(type), model, expected), fuel);
            return null;
        }
        catch (KernelException ex) when (reportFuel || ex is not KernelResourceException)
        {
            return $"{description}: the CLR returned {Values.Display(type, result)} but the model computes "
                + $"{Values.ReadBackDisplay(Env, type, model, limits)} (kernel: {FirstLine(ex.Message)})";
        }
    }

    /// <summary>
    /// The fuel and wall-clock time of the checks <see cref="Kernel.Kernel.Add"/> makes for this theorem (type, proof,
    /// definitional equality), measured on a fresh checker. Must run on a kernel thread.
    /// </summary>
    public (long Fuel, TimeSpan Elapsed) Measure(VirType type, Expr model, object? result) =>
        Measure(Theorem(Values.CicType(type), model, Values.Term(type, result)));

    /// <summary>
    /// The fuel and wall-clock time of the checks <see cref="Kernel.Kernel.Add"/> makes for a theorem, measured on a fresh
    /// checker. Must run on a kernel thread.
    /// </summary>
    public (long Fuel, TimeSpan Elapsed) Measure(TheoremDecl declaration)
    {
        var theorem = declaration.Value;
        var watch = Stopwatch.StartNew();
        var checker = new TypeChecker(Env.Fork(), limits: limits);
        checker.Check(theorem.Type, theorem.LevelParams);
        var proofType = checker.Check(theorem.Proof, theorem.LevelParams);
        Assert.True(checker.IsDefEq(proofType, theorem.Type));
        return (checker.FuelUsed, watch.Elapsed);
    }

    // ---- Units that can raise (plan M6 U13, KTD21, #110) ----

    private static readonly Name ClrM = Name.Parse("Warrant.ClrM");

    /// <summary><c>Eq.{2}</c>: a run <c>∀ σ : Type, σ → Except ClrExn R</c> lives in <c>Type 1</c>.</summary>
    private static readonly Expr Eq2 = Expr.Const(Name.Parse("Eq"), Level.Succ(Level.One));

    private static readonly Expr EqRefl2 = Expr.Const(Name.Parse("Eq.refl"), Level.Succ(Level.One));

    private static readonly Expr TypeSort = Expr.Sort(Level.One);

    private static readonly Expr ClrExnType = Expr.Const(ClrExceptions.Type);

    private static Expr C(string dotted) => Expr.Const(Name.Parse(dotted), Level.Zero, Level.Zero);

    /// <summary>
    /// Whether a translated function is a <c>ClrM</c> program, <c>∀ {σ : Type} params, ClrM σ R</c> (plan M6 U9), rather
    /// than a pure function.
    /// </summary>
    public bool IsRaising(VirUnit unit) =>
        Env.Get(LeanNames.ForKey(unit.Key)).Type is ForallExpr { BinderInfo: BinderInfo.Implicit } type
        && ExprOps.Find(type, (e, _) => e is ConstExpr { Name: var n } && n == ClrM) is not null;

    /// <summary><c>Except ClrExn R</c>.</summary>
    private static Expr Except(Expr returns) => Expr.App(C("Except"), ClrExnType, returns);

    /// <summary><c>@Except.ok ClrExn R v</c>.</summary>
    public static Expr Ok(Expr returns, Expr value) => Expr.App(C("Except.ok"), ClrExnType, returns, value);

    /// <summary><c>@Except.error ClrExn R e</c>.</summary>
    public static Expr Error(Expr returns, Expr exception) => Expr.App(C("Except.error"), ClrExnType, returns, exception);

    /// <summary>
    /// A raising unit run from an arbitrary world, keeping the <c>Except</c> part (#110):
    /// <c>fun (σ : Type) (s : σ) =&gt; (StateT.run (ExceptT.run (f σ a₁ … aₙ)) s).1</c>.
    /// </summary>
    public Expr Run(VirUnit unit, IReadOnlyList<object?> args)
    {
        var types = ParameterTypes(unit);
        var returns = Values.CicType(unit.Returns!);
        var sigma = Expr.BVar(1);
        var except = Except(returns);
        var stateM = Expr.App(Expr.Const(Name.Parse("StateM"), Level.Zero), sigma);
        var program = Expr.App(Expr.Const(LeanNames.ForKey(unit.Key)), [sigma, .. types.Select((t, i) => Values.Term(t, args[i]))]);
        var run = Expr.App(C("StateT.run"), sigma, Expr.Const(Name.Parse("Id"), Level.Zero), except,
            Expr.App(C("ExceptT.run"), ClrExnType, stateM, returns, program),
            Expr.BVar(0));
        return Expr.Lam(Name.Parse("σ"), TypeSort, Expr.Lam(Name.Parse("s"), Expr.BVar(0),
            Expr.App(C("Prod.fst"), except, sigma, run)));
    }

    /// <summary>The same outcome from every world: <c>fun (σ : Type) (s : σ) =&gt; outcome</c>.</summary>
    public static Expr Everywhere(Expr outcome) =>
        Expr.Lam(Name.Parse("σ"), TypeSort, Expr.Lam(Name.Parse("s"), Expr.BVar(0), outcome));

    /// <summary>The theorem <c>@Eq.{2} (∀ σ : Type, σ → Except ClrExn R) run (fun σ s =&gt; outcome)</c>, proved by <c>Eq.refl</c>.</summary>
    public static TheoremDecl RunTheorem(Expr returns, Expr run, Expr outcome)
    {
        var type = Expr.Forall(Name.Parse("σ"), TypeSort, Expr.Forall(Name.Parse("s"), Expr.BVar(0), Except(returns)));
        return new TheoremDecl(new TheoremInfo(
            TheoremName,
            EquatableArray<Name>.Empty,
            Expr.App(Eq2, type, run, Everywhere(outcome)),
            Expr.App(EqRefl2, type, run),
            EquatableArray.Create(TheoremName)));
    }

    /// <summary>
    /// Whether the kernel admits <c>@Eq.{2} (∀ σ : Type, σ → Except ClrExn R) run (fun σ s =&gt; outcome)</c> by
    /// <c>Eq.refl</c>. Running out of fuel throws. Must run on a kernel thread.
    /// </summary>
    public bool RunsTo(Expr returns, Expr run, Expr outcome)
    {
        try
        {
            Kernel.Kernel.Add(Env.Fork(), RunTheorem(returns, run, outcome), limits);
            return true;
        }
        catch (KernelException ex) when (ex is not KernelResourceException)
        {
            return false;
        }
    }

    /// <summary>
    /// Whether a raising unit's run agrees with the CLR's outcome (<paramref name="thrown"/>, or else
    /// <paramref name="result"/>): <see cref="InputCheck.Agrees"/>, <see cref="InputCheck.Skipped"/> when the model
    /// fails a <c>Spec.Assert</c> (#186), or a message with both outcomes. Must run on a kernel thread.
    /// </summary>
    public InputCheck CheckRaising(string description, VirType returns, Expr run, object? result, Exception? thrown)
    {
        var r = Values.CicType(returns);
        string clr;
        if (thrown is null)
        {
            Expr value;
            try
            {
                value = Values.Term(returns, result);
            }
            catch (ModelGapException ex)
            {
                return InputCheck.Disagrees($"{description}: the CLR returned {Values.Display(returns, result)}, which the model cannot produce ({ex.Message}); the model computes {Outcome(returns, run)}");
            }
            if (RunsTo(r, run, Ok(r, value)))
            {
                return InputCheck.Agrees;
            }
            clr = $"returned {Values.Display(returns, result)}";
        }
        else
        {
            if (ClrExceptions.ModelErrors(thrown).Any(e => RunsTo(r, run, Error(r, e))))
            {
                return InputCheck.Agrees;
            }
            clr = $"threw {thrown.GetType().Name}";
        }
        return RunsTo(r, run, Error(r, ClrExceptions.Constructor(ClrExceptions.AssertFailed)))
            ? InputCheck.Skipped
            : InputCheck.Disagrees($"{description}: the CLR {clr} but the model computes {Outcome(returns, run)}");
    }

    /// <summary>
    /// The model's outcome in one world (<c>Unit</c>), for messages only: <c>ok v</c> with <c>v</c> read back, or
    /// <c>error c</c>. Must run on a kernel thread.
    /// </summary>
    public string Outcome(VirType returns, Expr run)
    {
        try
        {
            var checker = new TypeChecker(Env, limits: limits);
            var outcome = checker.Whnf(Expr.App(run, Expr.Const(Name.Parse("Unit")), Expr.Const(Name.Parse("Unit.unit"))));
            var args = outcome.GetAppArgs();
            switch (outcome.GetAppFn())
            {
                case ConstExpr { Name: var n } when n == Name.Parse("Except.ok"):
                    return $"ok {Values.ReadBackDisplay(Env, returns, args[2], limits)}";
                case ConstExpr { Name: var n } when n == Name.Parse("Except.error"):
                    {
                        var e = checker.Whnf(args[2]);
                        return e.GetAppFn() is ConstExpr { Name: var c }
                            ? $"error {c.StringComponent}{string.Concat(e.GetAppArgs().Select(a => " " + checker.Whnf(a)))}"
                            : $"error {e}";
                    }
                default:
                    return "unknown";
            }
        }
        catch (KernelException)
        {
            return "unknown";
        }
    }

    private static string FirstLine(string message)
    {
        var newline = message.IndexOfAny(['\r', '\n']);
        return newline < 0 ? message : message[..newline];
    }
}

/// <summary>The check of one input of an M6 function: agreement, a skip (the model failed a <c>Spec.Assert</c>), or a disagreement.</summary>
/// <param name="Disagreement">The message, when the two sides disagree.</param>
/// <param name="IsSkipped">Whether the model failed a <c>Spec.Assert</c>, which does nothing on the CLR (#186).</param>
internal sealed record InputCheck(string? Disagreement, bool IsSkipped)
{
    public static InputCheck Agrees { get; } = new(null, false);

    public static InputCheck Skipped { get; } = new(null, true);

    public static InputCheck Disagrees(string message) => new(message, false);
}
