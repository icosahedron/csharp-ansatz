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
