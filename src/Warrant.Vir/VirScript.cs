namespace Warrant.Vir;

/// <summary>
/// <c>tactic{name, args}</c>: one step of a theorem's proof script (plan KTD18). The node is generic, so a new tactic
/// needs no new VIR kind: <c>Tactic.Simp().With(decide: false)</c> is <c>simp</c> with the argument
/// <c>option{decide, bool false}</c>. Its span is the <c>Tactic.X(...)</c> call's.
/// </summary>
/// <param name="Name">The tactic's name, as Lean spells it: <c>intro</c>, <c>exact</c>, <c>apply</c>, <c>cases</c>,
/// <c>induction</c>, <c>unfold</c>, <c>simp</c>, <c>omega</c>, <c>all_goals</c> or <c>try</c>.</param>
/// <param name="Args">The arguments, in source order, then the options.</param>
public sealed record TacticNode(string Name, VirList<VirTacticArg> Args) : VirNode;

/// <summary>An argument of a <see cref="TacticNode"/>.</summary>
public abstract record VirTacticArg
{
    private protected VirTacticArg()
    {
    }
}

/// <summary><c>unit{key}</c>: a C# member named with <c>nameof</c>, by its unit key; the theorem depends on it.</summary>
/// <param name="Key">The unit key of the <c>[Verified]</c> member or <c>[Theorem]</c>.</param>
public sealed record UnitRefArg(string Key) : VirTacticArg;

/// <summary><c>lean{name}</c>: a Lean declaration named with <c>Lean.Const</c>.</summary>
/// <param name="Name">The declaration's full Lean name.</param>
public sealed record LeanRefArg(string Name) : VirTacticArg;

/// <summary><c>string{value}</c>: a string literal, which names a hypothesis or variable in the goal.</summary>
/// <param name="Value">The name.</param>
public sealed record StringArg(string Value) : VirTacticArg;

/// <summary><c>number{value}</c>: an integer argument.</summary>
/// <param name="Value">The value.</param>
public sealed record NumberArg(long Value) : VirTacticArg;

/// <summary><c>bool{value}</c>: a boolean argument, such as an option's value.</summary>
/// <param name="Value">The value.</param>
public sealed record BoolArg(bool Value) : VirTacticArg;

/// <summary><c>tactic{…}</c>: a nested tactic, as in <c>Tactic.Try(Tactic.Simp())</c>; encoded as the node itself.</summary>
/// <param name="Tactic">The nested tactic.</param>
public sealed record TacticArg(TacticNode Tactic) : VirTacticArg;

/// <summary><c>option{name, value}</c>: a named option, such as <c>decide</c> in <c>.With(decide: false)</c>.</summary>
/// <param name="Name">The option's name, as the C# parameter spells it.</param>
/// <param name="Value">The option's value.</param>
public sealed record OptionArg(string Name, VirTacticArg Value) : VirTacticArg;

/// <summary>
/// <c>budget{timeoutSeconds, tacticFuel, kernelFuel}</c>: a theorem's overrides of the project's budgets, from
/// <c>[Theorem(...)]</c>'s named arguments (plan KTD24). Zero means the project's setting; a theorem with no override
/// has no budget.
/// </summary>
/// <param name="TimeoutSeconds">The wall-clock limit, in seconds.</param>
/// <param name="TacticFuel">The tactic fuel.</param>
/// <param name="KernelFuel">The kernel fuel.</param>
public sealed record VirBudget(int TimeoutSeconds, long TacticFuel, long KernelFuel);
