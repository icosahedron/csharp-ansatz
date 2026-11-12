namespace Warrant.Vir;

/// <summary><c>decl{local, name, init}</c>: declares a local; its type is the initializer's.</summary>
/// <param name="Local">The local's ID, unique within the unit.</param>
/// <param name="Name">The source name.</param>
/// <param name="Init">The initial value.</param>
public sealed record DeclStmt(int Local, string Name, VirExpr Init) : VirStmt;

/// <summary><c>assign{local, value}</c>; compound assignment and <c>++</c>/<c>--</c> are lowered to this.</summary>
/// <param name="Local">The local's ID.</param>
/// <param name="Value">The new value.</param>
public sealed record AssignStmt(int Local, VirExpr Value) : VirStmt;

/// <summary><c>if{c, then, else?}</c>.</summary>
/// <param name="C">The condition.</param>
/// <param name="Then">The statement run when true.</param>
/// <param name="Else">The statement run when false, if any.</param>
public sealed record IfStmt(VirExpr C, VirStmt Then, VirStmt? Else) : VirStmt;

/// <summary>
/// <c>switch{scrutinee, sections}</c>: a switch statement.
/// A trailing <c>break</c> is not represented: when a section's end is reachable, control continues after the switch.
/// </summary>
/// <param name="Scrutinee">The value switched on.</param>
/// <param name="Sections">The sections, in source order.</param>
public sealed record SwitchStmt(VirExpr Scrutinee, VirList<SwitchSection> Sections) : VirStmt;

/// <summary>One section of a <see cref="SwitchStmt"/>.</summary>
/// <param name="Labels">The case labels; <c>default</c> is a <see cref="DiscardPattern"/>.</param>
/// <param name="Body">The section's statements, without a trailing <c>break</c>.</param>
public sealed record SwitchSection(VirList<VirPattern> Labels, VirList<VirStmt> Body);

/// <summary><c>return{value}</c>.</summary>
/// <param name="Value">The returned value.</param>
public sealed record ReturnStmt(VirExpr Value) : VirStmt;

/// <summary><c>block{stmts}</c>.</summary>
/// <param name="Stmts">The statements, in order.</param>
public sealed record BlockStmt(VirList<VirStmt> Stmts) : VirStmt;

/// <summary>
/// <c>decreases{measure}</c>: <c>Spec.Decreases(measure)</c>, the first statement of a recursive function's body.
/// The measure is over the parameters, and its type is <c>int32</c> or <c>int64</c>: an <c>int</c> measure keeps its
/// type rather than the implicit widening to <c>long</c> that the call's signature adds.
/// </summary>
/// <param name="Measure">The measure.</param>
public sealed record DecreasesStmt(VirExpr Measure) : VirStmt;

/// <summary>
/// <c>throw{exception}</c>: <c>throw new T(...)</c> (M6, KTD4). The arguments are not modelled; the exception is
/// <c>ClrExn.thrown</c> of the type's key.
/// </summary>
/// <param name="Exception">The thrown exception type's key, e.g. <c>T:System.ArgumentException</c>.</param>
public sealed record ThrowStmt(string Exception) : VirStmt;

/// <summary><c>eval{value}</c>: an expression statement, such as an awaited call whose result is discarded (M6, KTD22).</summary>
/// <param name="Value">The expression, evaluated for its effects.</param>
public sealed record EvalStmt(VirExpr Value) : VirStmt;

/// <summary>
/// <c>requires{condition}</c>: <c>Spec.Requires(condition)</c>, among the leading <c>Spec</c> statements of a function's or
/// a contract unit's body (M6, KTD8). It is a claim, not a step: it is never run.
/// </summary>
/// <param name="Condition">The precondition, a <c>bool</c> expression over the parameters.</param>
public sealed record RequiresStmt(VirExpr Condition) : VirStmt;

/// <summary>
/// <c>nothrow{}</c>: <c>Spec.NoThrow()</c>, among the leading <c>Spec</c> statements of a function's body, after its
/// <c>Spec.Requires</c> and before its <c>Spec.Ensures</c> (#182). It is a claim, not a step: no explicit <c>throw</c> is
/// reachable under the precondition, so the contract allows only an exception propagated from a dependency.
/// </summary>
public sealed record NoThrowStmt : VirStmt;

/// <summary>
/// <c>ensures{local?, name?, condition}</c>: <c>Spec.Ensures&lt;T&gt;(r =&gt; condition)</c>, which binds the result to a local,
/// or <c>Spec.Ensures(() =&gt; condition)</c>, which binds nothing (M6, KTD8). It is a claim, not a step: it is never run.
/// </summary>
/// <param name="Local">The result's local ID, read in the condition by a <see cref="LocalExpr"/>; null when nothing is bound.</param>
/// <param name="Name">The result's source name; null exactly when <paramref name="Local"/> is.</param>
/// <param name="Condition">The postcondition, a <c>bool</c> expression.</param>
public sealed record EnsuresStmt(int? Local, string? Name, VirExpr Condition) : VirStmt;

/// <summary>
/// <c>assert{condition, script}</c>: <c>Spec.Assert(condition, script...)</c>, a check node that must hold where it stands
/// (M6, KTD16).
/// </summary>
/// <param name="Condition">The fact, a <c>bool</c> expression.</param>
/// <param name="Script">The tactics that prove it; empty for the default procedure.</param>
public sealed record AssertStmt(VirExpr Condition, VirList<TacticNode> Script) : VirStmt;
