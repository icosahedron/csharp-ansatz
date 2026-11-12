using System.Globalization;
using System.Text;

namespace Warrant.Vir;

/// <summary>
/// The canonical writer (docs/m4/04, "Encoding"). It is hand-written, not built on System.Text.Json, and has no
/// target-framework conditionals, so the netstandard2.0 and net10.0 builds write the same bytes (KTD5):
/// fields in the chapter's order, no insignificant whitespace, integer values as decimal strings, and strings
/// escaped by a fixed rule (<c>"</c> and <c>\</c> with a backslash, control characters as <c>\u00XX</c>, nothing else).
/// </summary>
/// <remarks>
/// Every node is an object with one field, named by its kind. An expression's content is an object whose first
/// field is its <c>type</c>; a node whose content is a single list or node (<c>block</c>, <c>return</c>,
/// <c>const</c>, pattern <c>not</c>) has that as its content directly. Fields that a unit kind does not have,
/// and an absent <c>else</c>, are omitted. Structural integers (<c>vir</c>, parameter indices, local IDs) are
/// JSON numbers, as in the chapter's example; program values (literals, enum member values) are decimal strings.
/// </remarks>
public static class VirWriter
{
    private static readonly UTF8Encoding Utf8 = new(encoderShouldEmitUTF8Identifier: false, throwOnInvalidBytes: true);

    /// <summary>Writes a unit's canonical encoding as UTF-8, without a byte-order mark.</summary>
    /// <param name="unit">The unit.</param>
    /// <returns>The canonical bytes, which the unit hash covers.</returns>
    /// <exception cref="ArgumentException">A string contains an unpaired surrogate, or the unit is malformed.</exception>
    public static byte[] Write(VirUnit unit) => Utf8.GetBytes(WriteString(unit));

    /// <summary>Writes a unit's canonical encoding as a string.</summary>
    /// <param name="unit">The unit.</param>
    /// <returns>The JSON text.</returns>
    /// <exception cref="ArgumentException">The unit is malformed, e.g. its body is neither a block nor an expression.</exception>
    public static string WriteString(VirUnit unit)
    {
        var w = new Json();
        w.Open();
        w.Name("vir").Number(unit.Vir);
        w.Name("key").String(unit.Key);
        w.Name("kind").String(VirSpelling.Of(unit.Kind));
        if (unit.Self is { } self)
        {
            w.Name("self").String(self);
        }
        if (unit.Params is { } parameters)
        {
            w.Name("params").OpenArray();
            foreach (var p in parameters)
            {
                w.Open();
                w.Name("name").String(p.Name);
                w.Name("type");
                Type(w, p.Type);
                w.Close();
            }
            w.CloseArray();
        }
        if (unit.Dependencies is { } dependencies)
        {
            w.Name("dependencies").OpenArray();
            foreach (var d in dependencies)
            {
                w.Open();
                w.Name("name").String(d.Name);
                w.Name("interface").String(d.Interface);
                w.Name("members").OpenArray();
                foreach (var m in d.Members)
                {
                    w.String(m);
                }
                w.CloseArray();
                w.Close();
            }
            w.CloseArray();
        }
        if (unit.Returns is { } returns)
        {
            w.Name("returns");
            Type(w, returns);
        }
        switch (unit.Body)
        {
            case null:
                break;
            case BlockStmt block:
                w.Name("body");
                Stmt(w, block);
                break;
            case VirExpr expr:
                w.Name("body");
                Expr(w, expr);
                break;
            default:
                throw new ArgumentException("A unit's body is a block or an expression.", nameof(unit));
        }
        if (unit.Statement is { } statement)
        {
            w.Name("statement");
            Expr(w, statement);
        }
        if (unit.Script is { } script)
        {
            w.Name("script").OpenArray();
            foreach (var tactic in script)
            {
                Tactic(w, tactic);
            }
            w.CloseArray();
        }
        if (unit.Budget is { } budget)
        {
            w.Name("budget").Open();
            w.Name("timeoutSeconds").String(Decimal(budget.TimeoutSeconds));
            w.Name("tacticFuel").String(Decimal(budget.TacticFuel));
            w.Name("kernelFuel").String(Decimal(budget.KernelFuel));
            w.Close();
        }
        if (unit.Definition is { } definition)
        {
            w.Name("definition");
            Definition(w, definition);
        }
        w.Name("assumptions").OpenArray();
        foreach (var a in unit.Assumptions)
        {
            w.Open();
            w.Name("kind").String(VirSpelling.Of(a.Kind));
            w.Name("subject").String(a.Subject);
            w.Close();
        }
        w.CloseArray();
        w.Name("facts").Open();
        w.Name("overflow").String(VirSpelling.Of(unit.Facts.Overflow));
        w.Name("language").String(unit.Facts.Language);
        w.Name("extractor").String(unit.Facts.Extractor);
        w.Name("roslyn").String(unit.Facts.Roslyn);
        w.Close();
        w.Name("deps").OpenArray();
        foreach (var d in unit.Deps)
        {
            w.String(d);
        }
        w.CloseArray();
        w.Close();
        return w.ToString();
    }

    private static void Type(Json w, VirType type)
    {
        switch (type)
        {
            case PrimitiveType p:
                w.String(VirSpelling.Of(p.Kind));
                break;
            case RefType r:
                w.Open();
                w.Name("ref").String(r.Key);
                w.Close();
                break;
            case NullableType n:
                w.Open();
                w.Name("nullable");
                Type(w, n.Value);
                w.Close();
                break;
            case TaskType t:
                w.Open();
                w.Name("task");
                Type(w, t.Result);
                w.Close();
                break;
            case OpaqueType o:
                w.Open();
                w.Name("opaque").String(o.Key);
                w.Close();
                break;
            default:
                throw new ArgumentException($"Unknown VIR type {type.GetType().Name}.", nameof(type));
        }
    }

    private static void Definition(Json w, VirDefinition definition)
    {
        w.Open();
        switch (definition)
        {
            case RecordDefinition r:
                w.Name("record").OpenArray();
                foreach (var f in r.Fields)
                {
                    w.Open();
                    w.Name("name").String(f.Name);
                    w.Name("type");
                    Type(w, f.Type);
                    w.Close();
                }
                w.CloseArray();
                break;
            case EnumDefinition e:
                w.Name("enum").Open();
                w.Name("underlying");
                Type(w, e.Underlying);
                w.Name("members").OpenArray();
                foreach (var m in e.Members)
                {
                    w.Open();
                    w.Name("name").String(m.Name);
                    w.Name("value").String(Decimal(m.Value));
                    w.Close();
                }
                w.CloseArray();
                w.Close();
                break;
            case ClosedDefinition c:
                w.Name("closed").OpenArray();
                foreach (var m in c.Members)
                {
                    w.Open();
                    w.Name("name").String(m.Name);
                    if (m.Value is { } value)
                    {
                        w.Name("value").String(Decimal(value));
                    }
                    w.Close();
                }
                w.CloseArray();
                break;
            default:
                throw new ArgumentException($"Unknown VIR definition {definition.GetType().Name}.", nameof(definition));
        }
        w.Close();
    }

    private static void Stmt(Json w, VirStmt stmt)
    {
        w.Open();
        switch (stmt)
        {
            case DeclStmt s:
                w.Name("decl").Open();
                w.Name("local").Number(s.Local);
                w.Name("name").String(s.Name);
                w.Name("init");
                Expr(w, s.Init);
                w.Close();
                break;
            case AssignStmt s:
                w.Name("assign").Open();
                w.Name("local").Number(s.Local);
                w.Name("value");
                Expr(w, s.Value);
                w.Close();
                break;
            case IfStmt s:
                w.Name("if").Open();
                w.Name("c");
                Expr(w, s.C);
                w.Name("then");
                Stmt(w, s.Then);
                if (s.Else is { } otherwise)
                {
                    w.Name("else");
                    Stmt(w, otherwise);
                }
                w.Close();
                break;
            case SwitchStmt s:
                w.Name("switch").Open();
                w.Name("scrutinee");
                Expr(w, s.Scrutinee);
                w.Name("sections").OpenArray();
                foreach (var section in s.Sections)
                {
                    w.Open();
                    w.Name("labels").OpenArray();
                    foreach (var label in section.Labels)
                    {
                        Pattern(w, label);
                    }
                    w.CloseArray();
                    w.Name("body");
                    Stmts(w, section.Body);
                    w.Close();
                }
                w.CloseArray();
                w.Close();
                break;
            case ReturnStmt s:
                w.Name("return");
                Expr(w, s.Value);
                break;
            case BlockStmt s:
                w.Name("block");
                Stmts(w, s.Stmts);
                break;
            case DecreasesStmt s:
                w.Name("decreases");
                Expr(w, s.Measure);
                break;
            case ThrowStmt s:
                w.Name("throw").Open();
                w.Name("exception").String(s.Exception);
                w.Close();
                break;
            case EvalStmt s:
                w.Name("eval");
                Expr(w, s.Value);
                break;
            case RequiresStmt s:
                w.Name("requires");
                Expr(w, s.Condition);
                break;
            case NoThrowStmt:
                w.Name("nothrow").Open();
                w.Close();
                break;
            case EnsuresStmt s:
                w.Name("ensures").Open();
                if ((s.Local is null) != (s.Name is null))
                {
                    throw new ArgumentException("An ensures binds both a local and a name, or neither.", nameof(stmt));
                }
                if (s.Local is { } local)
                {
                    w.Name("local").Number(local);
                    w.Name("name").String(s.Name!);
                }
                w.Name("c");
                Expr(w, s.Condition);
                w.Close();
                break;
            case AssertStmt s:
                w.Name("assert").Open();
                w.Name("c");
                Expr(w, s.Condition);
                w.Name("script").OpenArray();
                foreach (var tactic in s.Script)
                {
                    Tactic(w, tactic);
                }
                w.CloseArray();
                w.Close();
                break;
            default:
                throw new ArgumentException($"Unknown VIR statement {stmt.GetType().Name}.", nameof(stmt));
        }
        w.Close();
    }

    private static void Stmts(Json w, VirList<VirStmt> stmts)
    {
        w.OpenArray();
        foreach (var s in stmts)
        {
            Stmt(w, s);
        }
        w.CloseArray();
    }

    private static void Exprs(Json w, VirList<VirExpr> exprs)
    {
        w.OpenArray();
        foreach (var e in exprs)
        {
            Expr(w, e);
        }
        w.CloseArray();
    }

    private static void Expr(Json w, VirExpr expr)
    {
        w.Open();
        w.Name(ExprKind(expr)).Open();
        w.Name("type");
        Type(w, expr.Type);
        switch (expr)
        {
            case LitExpr e:
                w.Name("value").String(LitValue(e));
                break;
            case ParamExpr e:
                w.Name("index").Number(e.Index);
                break;
            case LocalExpr e:
                w.Name("id").Number(e.Id);
                break;
            case SelfExpr:
                break;
            case UnaryExpr e:
                w.Name("op").String(VirSpelling.Of(e.Op));
                w.Name("overflow").String(VirSpelling.Of(e.Overflow));
                w.Name("operand");
                Expr(w, e.Operand);
                break;
            case BinaryExpr e:
                w.Name("op").String(VirSpelling.Of(e.Op));
                w.Name("overflow").String(VirSpelling.Of(e.Overflow));
                w.Name("l");
                Expr(w, e.L);
                w.Name("r");
                Expr(w, e.R);
                break;
            case LogicalExpr e:
                w.Name("op").String(VirSpelling.Of(e.Op));
                w.Name("l");
                Expr(w, e.L);
                w.Name("r");
                Expr(w, e.R);
                break;
            case NotExpr e:
                w.Name("operand");
                Expr(w, e.Operand);
                break;
            case CompareExpr e:
                w.Name("op").String(VirSpelling.Of(e.Op));
                w.Name("kind").String(VirSpelling.Of(e.Kind));
                w.Name("l");
                Expr(w, e.L);
                w.Name("r");
                Expr(w, e.R);
                break;
            case ConvertExpr e:
                w.Name("from");
                Type(w, e.From);
                w.Name("to");
                Type(w, e.To);
                w.Name("overflow").String(VirSpelling.Of(e.Overflow));
                w.Name("operand");
                Expr(w, e.Operand);
                break;
            case CondExpr e:
                w.Name("c");
                Expr(w, e.C);
                w.Name("then");
                Expr(w, e.Then);
                w.Name("else");
                Expr(w, e.Else);
                break;
            case CallExpr e:
                w.Name("target").String(e.Target);
                w.Name("args");
                Exprs(w, e.Args);
                break;
            case NewExpr e:
                w.Name("args");
                Exprs(w, e.Args);
                break;
            case GetExpr e:
                w.Name("field").String(e.Field);
                w.Name("target");
                Expr(w, e.Target);
                break;
            case WithExpr e:
                w.Name("base");
                Expr(w, e.Base);
                w.Name("updates").OpenArray();
                foreach (var u in e.Updates)
                {
                    w.Open();
                    w.Name("field").String(u.Field);
                    w.Name("value");
                    Expr(w, u.Value);
                    w.Close();
                }
                w.CloseArray();
                break;
            case MemberExpr e:
                w.Name("name").String(e.Name);
                break;
            case SwitchExpr e:
                w.Name("scrutinee");
                Expr(w, e.Scrutinee);
                w.Name("arms").OpenArray();
                foreach (var arm in e.Arms)
                {
                    w.Open();
                    w.Name("pattern");
                    Pattern(w, arm.Pattern);
                    w.Name("value");
                    Expr(w, arm.Value);
                    w.Close();
                }
                w.CloseArray();
                break;
            case ImpliesExpr e:
                w.Name("a");
                Expr(w, e.A);
                w.Name("b");
                Expr(w, e.B);
                break;
            case ForAllExpr e:
                Binder(w, e.Local, e.Name, e.Domain, e.Body);
                break;
            case ExistsExpr e:
                Binder(w, e.Local, e.Name, e.Domain, e.Body);
                break;
            case DecimalLitExpr e:
                if (!e.IsValid)
                {
                    throw new ArgumentException($"A decimal literal has a mantissa below 2^96 and a scale of 0 to 28, not {e.Mantissa} and {Decimal(e.Scale)}.", nameof(expr));
                }
                w.Name("negative").String(e.Negative ? "true" : "false");
                w.Name("mantissa").String(e.Mantissa.ToString(CultureInfo.InvariantCulture));
                w.Name("scale").String(Decimal(e.Scale));
                break;
            case NullExpr:
                break;
            case IsNullExpr e:
                w.Name("operand");
                Expr(w, e.Operand);
                break;
            case UnwrapExpr e:
                w.Name("kind").String(VirSpelling.Of(e.Kind));
                w.Name("operand");
                Expr(w, e.Operand);
                break;
            case CoalesceExpr e:
                w.Name("l");
                Expr(w, e.L);
                w.Name("r");
                Expr(w, e.R);
                break;
            case ThrowExpr e:
                w.Name("exception").String(e.Exception);
                break;
            case AwaitExpr e:
                w.Name("operand");
                Expr(w, e.Operand);
                break;
            case ExternalCallExpr e:
                w.Name("dependency").Number(e.Dependency);
                w.Name("member").String(e.Member);
                w.Name("args");
                Exprs(w, e.Args);
                break;
            case ModelledCallExpr e:
                w.Name("member").String(e.Member);
                w.Name("args");
                Exprs(w, e.Args);
                break;
        }
        w.Close();
        w.Close();
    }

    private static string ExprKind(VirExpr expr) => expr switch
    {
        LitExpr => "lit",
        ParamExpr => "param",
        LocalExpr => "local",
        SelfExpr => "self",
        UnaryExpr => "unary",
        BinaryExpr => "binary",
        LogicalExpr => "logical",
        NotExpr => "not",
        CompareExpr => "compare",
        ConvertExpr => "convert",
        CondExpr => "cond",
        CallExpr => "call",
        NewExpr => "new",
        GetExpr => "get",
        WithExpr => "with",
        MemberExpr => "member",
        SwitchExpr => "switch",
        ImpliesExpr => "implies",
        ForAllExpr => "forall",
        ExistsExpr => "exists",
        DecimalLitExpr => "decimal",
        NullExpr => "null",
        IsNullExpr => "isnull",
        UnwrapExpr => "unwrap",
        CoalesceExpr => "coalesce",
        ThrowExpr => "throw",
        AwaitExpr => "await",
        ExternalCallExpr => "external",
        ModelledCallExpr => "modelled",
        _ => throw new ArgumentException($"Unknown VIR expression {expr.GetType().Name}.", nameof(expr)),
    };

    private static void Binder(Json w, int local, string name, VirType domain, VirExpr body)
    {
        w.Name("local").Number(local);
        w.Name("name").String(name);
        w.Name("domain");
        Type(w, domain);
        w.Name("body");
        Expr(w, body);
    }

    private static void Tactic(Json w, TacticNode tactic)
    {
        w.Open();
        w.Name("tactic").Open();
        w.Name("name").String(tactic.Name);
        w.Name("args").OpenArray();
        foreach (var arg in tactic.Args)
        {
            TacticArgument(w, arg);
        }
        w.CloseArray();
        w.Close();
        w.Close();
    }

    private static void TacticArgument(Json w, VirTacticArg arg)
    {
        if (arg is TacticArg nested)
        {
            Tactic(w, nested.Tactic);
            return;
        }
        w.Open();
        switch (arg)
        {
            case UnitRefArg a:
                w.Name("unit").String(a.Key);
                break;
            case LeanRefArg a:
                w.Name("lean").String(a.Name);
                break;
            case StringArg a:
                w.Name("string").String(a.Value);
                break;
            case NumberArg a:
                w.Name("number").String(Decimal(a.Value));
                break;
            case BoolArg a:
                w.Name("bool").String(a.Value ? "true" : "false");
                break;
            case OptionArg a:
                w.Name("option").Open();
                w.Name("name").String(a.Name);
                w.Name("value");
                TacticArgument(w, a.Value);
                w.Close();
                break;
            default:
                throw new ArgumentException($"Unknown VIR tactic argument {arg.GetType().Name}.", nameof(arg));
        }
        w.Close();
    }

    private static string LitValue(LitExpr lit)
    {
        if (lit.Type == VirType.Bool)
        {
            return lit.Value switch
            {
                0 => "false",
                1 => "true",
                _ => throw new ArgumentException($"A bool literal is 0 or 1, not {Decimal(lit.Value)}.", nameof(lit)),
            };
        }
        if (lit.Type == VirType.Unit && lit.Value != 0)
        {
            throw new ArgumentException($"The unit literal is 0, not {Decimal(lit.Value)}.", nameof(lit));
        }
        return Decimal(lit.Value);
    }

    private static void Pattern(Json w, VirPattern pattern)
    {
        w.Open();
        switch (pattern)
        {
            case ConstPattern p:
                w.Name("const");
                Expr(w, p.Value);
                break;
            case DiscardPattern:
                w.Name("discard").Open();
                w.Close();
                break;
            case RelationalPattern p:
                w.Name("relational").Open();
                w.Name("op").String(VirSpelling.Of(p.Op));
                w.Name("value");
                Expr(w, p.Value);
                w.Close();
                break;
            case AndPattern p:
                w.Name("and").Open();
                w.Name("l");
                Pattern(w, p.L);
                w.Name("r");
                Pattern(w, p.R);
                w.Close();
                break;
            case OrPattern p:
                w.Name("or").Open();
                w.Name("l");
                Pattern(w, p.L);
                w.Name("r");
                Pattern(w, p.R);
                w.Close();
                break;
            case NotPattern p:
                w.Name("not");
                Pattern(w, p.Operand);
                break;
            default:
                throw new ArgumentException($"Unknown VIR pattern {pattern.GetType().Name}.", nameof(pattern));
        }
        w.Close();
    }

    private static string Decimal(long value) => value.ToString(CultureInfo.InvariantCulture);

    /// <summary>Emits JSON tokens, placing commas; no whitespace.</summary>
    private sealed class Json
    {
        private readonly StringBuilder _out = new();
        private readonly Stack<bool> _first = new();
        private bool _afterName;

        public void Open()
        {
            Separate();
            _out.Append('{');
            _first.Push(true);
        }

        public void Close()
        {
            _first.Pop();
            _out.Append('}');
        }

        public Json OpenArray()
        {
            Separate();
            _out.Append('[');
            _first.Push(true);
            return this;
        }

        public void CloseArray()
        {
            _first.Pop();
            _out.Append(']');
        }

        /// <summary>Writes a field name; the value that follows is not separated from it.</summary>
        public Json Name(string name)
        {
            Separate();
            Escape(name);
            _out.Append(':');
            _afterName = true;
            return this;
        }

        public void String(string value)
        {
            Separate();
            Escape(value);
        }

        public void Number(int value)
        {
            Separate();
            _out.Append(value.ToString(CultureInfo.InvariantCulture));
        }

        public override string ToString() => _out.ToString();

        private void Separate()
        {
            if (_afterName)
            {
                _afterName = false;
                return;
            }
            if (_first.Count == 0)
            {
                return;
            }
            if (!_first.Pop())
            {
                _out.Append(',');
            }
            _first.Push(false);
        }

        private void Escape(string value)
        {
            _out.Append('"');
            foreach (char c in value)
            {
                if (c == '"' || c == '\\')
                {
                    _out.Append('\\').Append(c);
                }
                else if (char.IsControl(c))
                {
                    _out.Append("\\u00").Append(((int)c).ToString("X2", CultureInfo.InvariantCulture));
                }
                else
                {
                    _out.Append(c);
                }
            }
            _out.Append('"');
        }
    }
}
