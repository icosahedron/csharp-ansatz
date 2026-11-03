using Warrant.Cic;
using Warrant.Kernel;
using Warrant.Semantics;

namespace Warrant.Engine;

/// <summary>
/// The proof emitter (docs/m4/06, KTD12): the two fixed terms Lean's own <c>rfl</c> and <c>decide</c> elaborate to. It is
/// untrusted (KTD22): the kernel checks whatever it emits against the type translation fixed.
/// </summary>
public static class ProofTerms
{
    private static readonly Name EqName = Name.Parse("Eq");
    private static readonly Name EqReflName = Name.Parse("Eq.refl");

    /// <summary><c>@of_decide_eq_true</c>: no universe parameters.</summary>
    private static readonly Expr OfDecideEqTrue = Expr.Const(Name.Parse("of_decide_eq_true"));

    /// <summary><c>@Eq.refl.{1} Bool Bool.true</c>, a proof of <c>true = true</c>.</summary>
    private static readonly Expr TrueEqTrue = Expr.App(
        Expr.Const(EqReflName, Level.One), Expr.Const(Name.Parse("Bool")), Expr.Const(Name.Parse("Bool.true")));

    /// <summary>
    /// <c>@Eq.refl.{u} T a</c> for a statement <c>@Eq.{u} T a b</c>, using its left side; null when the statement is not an
    /// equation. The kernel accepts it exactly when <c>a</c> and <c>b</c> are definitionally equal.
    /// </summary>
    /// <param name="statement">The theorem's statement.</param>
    /// <returns>The term, or null.</returns>
    public static Expr? Rfl(Condition statement)
    {
        ArgumentNullException.ThrowIfNull(statement);
        if (statement.Prop.GetAppFn() is ConstExpr { Name: var name, Levels: var levels } && name == EqName)
        {
            var args = statement.Prop.GetAppArgs();
            if (args.Length == 3)
            {
                return Expr.App(Expr.Const(EqReflName, levels), args[0], args[1]);
            }
        }
        return null;
    }

    /// <summary>
    /// <c>@of_decide_eq_true P D (@Eq.refl Bool Bool.true)</c> for a statement <c>P</c> with instance <c>D</c>. The kernel
    /// accepts it exactly when <c>Decidable.decide P D</c> computes to <c>Bool.true</c>.
    /// </summary>
    /// <param name="statement">The theorem's statement.</param>
    /// <returns>The term.</returns>
    public static Expr Decide(Condition statement)
    {
        ArgumentNullException.ThrowIfNull(statement);
        return Expr.App(OfDecideEqTrue, statement.Prop, statement.Instance, TrueEqTrue);
    }

    /// <summary>
    /// Whether <paramref name="env"/> holds, under the shell's name, a theorem whose type is the shell's type (alpha-equal).
    /// The engine reports a theorem proved only when this holds after the kernel admitted it (KTD22).
    /// </summary>
    /// <param name="env">The environment.</param>
    /// <param name="shell">The statement translation built.</param>
    /// <returns>Whether the admitted constant is that theorem.</returns>
    public static bool IsAdmittedAs(KernelEnvironment env, TheoremShell shell)
    {
        ArgumentNullException.ThrowIfNull(env);
        ArgumentNullException.ThrowIfNull(shell);
        return env.Find(shell.Name) is TheoremInfo { LevelParams.Count: 0 } admitted && admitted.Type.AlphaEquals(shell.Type);
    }
}
