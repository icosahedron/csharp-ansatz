using System.Globalization;
using System.Numerics;
using System.Text.Json;

namespace Warrant.Vir;

/// <summary>
/// Reads the canonical encoding back into a <see cref="VirUnit"/>. Built for net10.0 only and based on the in-box
/// System.Text.Json; reading is not where the bytes are decided (docs/m4/04, "Encoding").
/// </summary>
public static class VirReader
{
    /// <summary>Reads a unit from its UTF-8 encoding.</summary>
    /// <param name="utf8">The encoded unit.</param>
    /// <returns>The unit.</returns>
    /// <exception cref="FormatException">The input is not a VIR unit, or its version is newer than <see cref="VirUnit.CurrentVersion"/>.</exception>
    public static VirUnit Read(ReadOnlyMemory<byte> utf8)
    {
        try
        {
            using var doc = JsonDocument.Parse(utf8);
            return Unit(doc.RootElement);
        }
        catch (Exception e) when (e is JsonException or InvalidOperationException or KeyNotFoundException or OverflowException)
        {
            throw new FormatException($"Not a VIR unit: {e.Message}", e);
        }
    }

    private static VirUnit Unit(JsonElement e)
    {
        int version = e.GetProperty("vir").GetInt32();
        if (version > VirUnit.CurrentVersion)
        {
            throw new FormatException($"VIR version {version} is newer than this reader's version {VirUnit.CurrentVersion}.");
        }
        var kind = Parse<VirUnitKind>(Str(e, "kind"), VirSpelling.Of);
        VirNode? body = null;
        if (e.TryGetProperty("body", out var b))
        {
            body = Kind(b).Name == "block" ? Stmt(b) : Expr(b);
        }
        return new VirUnit(
            version,
            Str(e, "key"),
            kind,
            e.TryGetProperty("self", out var self) ? self.GetString()! : null,
            e.TryGetProperty("params", out var ps) ? List(ps, p => new VirParam(Str(p, "name"), Type(p.GetProperty("type")))) : null,
            e.TryGetProperty("returns", out var r) ? Type(r) : null,
            body,
            e.TryGetProperty("statement", out var s) ? Expr(s) : null,
            e.TryGetProperty("script", out var script) ? List(script, Tactic) : null,
            e.TryGetProperty("budget", out var budget) ? Budget(budget) : null,
            e.TryGetProperty("definition", out var d) ? Definition(d) : null,
            List(e.GetProperty("assumptions"), a => new VirAssumption(
                Parse<VirAssumptionKind>(Str(a, "kind"), VirSpelling.Of),
                Str(a, "subject"))),
            Facts(e.GetProperty("facts")),
            List(e.GetProperty("deps"), x => x.GetString()!),
            e.TryGetProperty("dependencies", out var ds) ? List(ds, Dependency) : null);
    }

    private static VirDependency Dependency(JsonElement e) =>
        new(Str(e, "name"), Str(e, "interface"), List(e.GetProperty("members"), m => m.GetString()!));

    private static VirBudget Budget(JsonElement e) => new(
        checked((int)Long(Str(e, "timeoutSeconds"))),
        Long(Str(e, "tacticFuel")),
        Long(Str(e, "kernelFuel")));

    private static TacticNode Tactic(JsonElement e)
    {
        var (name, v) = Kind(e);
        return name == "tactic"
            ? new TacticNode(Str(v, "name"), List(v.GetProperty("args"), TacticArgument))
            : throw new FormatException($"Unknown VIR tactic '{name}'.");
    }

    private static VirTacticArg TacticArgument(JsonElement e)
    {
        var (name, v) = Kind(e);
        return name switch
        {
            "unit" => new UnitRefArg(v.GetString()!),
            "lean" => new LeanRefArg(v.GetString()!),
            "string" => new StringArg(v.GetString()!),
            "number" => new NumberArg(Long(v.GetString()!)),
            "bool" => new BoolArg(v.GetString() switch
            {
                "false" => false,
                "true" => true,
                var text => throw new FormatException($"Not a bool argument: '{text}'."),
            }),
            "tactic" => new TacticArg(Tactic(e)),
            "option" => new OptionArg(Str(v, "name"), TacticArgument(v.GetProperty("value"))),
            _ => throw new FormatException($"Unknown VIR tactic argument '{name}'."),
        };
    }

    private static VirFacts Facts(JsonElement e) => new(
        Parse<VirOverflow>(Str(e, "overflow"), VirSpelling.Of) is var overflow && overflow != VirOverflow.Unchecked
            ? overflow
            : throw new FormatException("A unit's facts give the project's overflow setting, 'wrap' or 'checked', never 'unchecked'."),
        Str(e, "language"),
        Str(e, "extractor"),
        Str(e, "roslyn"));

    private static VirType Type(JsonElement e)
    {
        if (e.ValueKind == JsonValueKind.String)
        {
            return new PrimitiveType(Parse<VirPrimitive>(e.GetString()!, VirSpelling.Of));
        }
        var (name, value) = Kind(e);
        return name switch
        {
            "ref" => new RefType(value.GetString()!),
            "nullable" => new NullableType(Type(value)),
            "task" => new TaskType(Type(value)),
            "opaque" => new OpaqueType(value.GetString() ?? throw new FormatException("An opaque type names its key.")),
            _ => throw new FormatException($"Unknown VIR type '{name}'."),
        };
    }

    private static VirDefinition Definition(JsonElement e)
    {
        var (name, v) = Kind(e);
        return name switch
        {
            "record" => new RecordDefinition(List(v, f => new VirField(Str(f, "name"), Type(f.GetProperty("type"))))),
            "enum" => new EnumDefinition(
                Type(v.GetProperty("underlying")),
                List(v.GetProperty("members"), m => new VirEnumMember(Str(m, "name"), Long(Str(m, "value"))))),
            "closed" => new ClosedDefinition(List(v, m => new VirClosedMember(
                Str(m, "name"),
                m.TryGetProperty("value", out var x) ? Long(x.GetString()!) : null))),
            _ => throw new FormatException($"Unknown VIR definition '{name}'."),
        };
    }

    private static VirStmt Stmt(JsonElement e)
    {
        var (name, v) = Kind(e);
        return name switch
        {
            "decl" => new DeclStmt(v.GetProperty("local").GetInt32(), Str(v, "name"), Expr(v.GetProperty("init"))),
            "assign" => new AssignStmt(v.GetProperty("local").GetInt32(), Expr(v.GetProperty("value"))),
            "if" => new IfStmt(
                Expr(v.GetProperty("c")),
                Stmt(v.GetProperty("then")),
                v.TryGetProperty("else", out var otherwise) ? Stmt(otherwise) : null),
            "switch" => new SwitchStmt(
                Expr(v.GetProperty("scrutinee")),
                List(v.GetProperty("sections"), s => new SwitchSection(
                    List(s.GetProperty("labels"), Pattern),
                    List(s.GetProperty("body"), Stmt)))),
            "return" => new ReturnStmt(Expr(v)),
            "block" => new BlockStmt(List(v, Stmt)),
            "decreases" => new DecreasesStmt(Expr(v)),
            "throw" => new ThrowStmt(Str(v, "exception")),
            "eval" => new EvalStmt(Expr(v)),
            "requires" => new RequiresStmt(Expr(v)),
            "nothrow" => NoThrow(v),
            "ensures" => Ensures(v),
            "assert" => new AssertStmt(Expr(v.GetProperty("c")), List(v.GetProperty("script"), Tactic)),
            _ => throw new FormatException($"Unknown VIR statement '{name}'."),
        };
    }

    private static NoThrowStmt NoThrow(JsonElement v)
    {
        if (v.ValueKind != JsonValueKind.Object || v.EnumerateObject().Any())
        {
            throw new FormatException("A nothrow is an empty object.");
        }
        return new NoThrowStmt();
    }

    private static EnsuresStmt Ensures(JsonElement v)
    {
        bool hasLocal = v.TryGetProperty("local", out var local);
        bool hasName = v.TryGetProperty("name", out var name);
        if (hasLocal != hasName)
        {
            throw new FormatException("An ensures binds both a local and a name, or neither.");
        }
        return new EnsuresStmt(hasLocal ? local.GetInt32() : null, hasName ? name.GetString()! : null, Expr(v.GetProperty("c")));
    }

    private static VirExpr Expr(JsonElement e)
    {
        var (name, v) = Kind(e);
        var type = Type(v.GetProperty("type"));
        return name switch
        {
            "lit" => new LitExpr(type, LitValue(type, Str(v, "value"))),
            "param" => new ParamExpr(type, v.GetProperty("index").GetInt32()),
            "local" => new LocalExpr(type, v.GetProperty("id").GetInt32()),
            "self" => new SelfExpr(type),
            "unary" => new UnaryExpr(
                type,
                Parse<UnaryOp>(Str(v, "op"), VirSpelling.Of),
                Overflow(v),
                Expr(v.GetProperty("operand"))),
            "binary" => new BinaryExpr(
                type,
                Parse<BinaryOp>(Str(v, "op"), VirSpelling.Of),
                Overflow(v),
                Expr(v.GetProperty("l")),
                Expr(v.GetProperty("r"))),
            "logical" => Typed(type, new LogicalExpr(
                Parse<LogicalOp>(Str(v, "op"), VirSpelling.Of),
                Expr(v.GetProperty("l")),
                Expr(v.GetProperty("r")))),
            "not" => Typed(type, new NotExpr(Expr(v.GetProperty("operand")))),
            "compare" => Typed(type, new CompareExpr(
                Parse<CompareOp>(Str(v, "op"), VirSpelling.Of),
                Parse<CompareKind>(Str(v, "kind"), VirSpelling.Of),
                Expr(v.GetProperty("l")),
                Expr(v.GetProperty("r")))),
            "convert" => Typed(type, new ConvertExpr(
                Type(v.GetProperty("from")),
                Type(v.GetProperty("to")),
                Overflow(v),
                Expr(v.GetProperty("operand")))),
            "cond" => new CondExpr(type, Expr(v.GetProperty("c")), Expr(v.GetProperty("then")), Expr(v.GetProperty("else"))),
            "call" => new CallExpr(type, Str(v, "target"), List(v.GetProperty("args"), Expr)),
            "new" => new NewExpr(type, List(v.GetProperty("args"), Expr)),
            "get" => new GetExpr(type, Str(v, "field"), Expr(v.GetProperty("target"))),
            "with" => new WithExpr(
                type,
                Expr(v.GetProperty("base")),
                List(v.GetProperty("updates"), u => new WithUpdate(Str(u, "field"), Expr(u.GetProperty("value"))))),
            "member" => new MemberExpr(type, Str(v, "name")),
            "switch" => new SwitchExpr(
                type,
                Expr(v.GetProperty("scrutinee")),
                List(v.GetProperty("arms"), a => new SwitchArm(Pattern(a.GetProperty("pattern")), Expr(a.GetProperty("value"))))),
            "implies" => Typed(type, new ImpliesExpr(Expr(v.GetProperty("a")), Expr(v.GetProperty("b")))),
            "forall" => Typed(type, new ForAllExpr(
                v.GetProperty("local").GetInt32(), Str(v, "name"), Type(v.GetProperty("domain")), Expr(v.GetProperty("body")))),
            "exists" => Typed(type, new ExistsExpr(
                v.GetProperty("local").GetInt32(), Str(v, "name"), Type(v.GetProperty("domain")), Expr(v.GetProperty("body")))),
            "decimal" => Typed(type, DecimalLiteral(v)),
            "null" => new NullExpr(type),
            "isnull" => Typed(type, new IsNullExpr(Expr(v.GetProperty("operand")))),
            "unwrap" => new UnwrapExpr(type, Parse<UnwrapKind>(Str(v, "kind"), VirSpelling.Of), Expr(v.GetProperty("operand"))),
            "coalesce" => new CoalesceExpr(type, Expr(v.GetProperty("l")), Expr(v.GetProperty("r"))),
            "throw" => new ThrowExpr(type, Str(v, "exception")),
            "await" => new AwaitExpr(type, Expr(v.GetProperty("operand"))),
            "external" => new ExternalCallExpr(type, v.GetProperty("dependency").GetInt32(), Str(v, "member"), List(v.GetProperty("args"), Expr)),
            "modelled" => new ModelledCallExpr(type, Str(v, "member"), List(v.GetProperty("args"), Expr)),
            _ => throw new FormatException($"Unknown VIR expression '{name}'."),
        };
    }

    private static VirPattern Pattern(JsonElement e)
    {
        var (name, v) = Kind(e);
        return name switch
        {
            "const" => new ConstPattern(Expr(v)),
            "discard" => new DiscardPattern(),
            "relational" => new RelationalPattern(Parse<RelationalOp>(Str(v, "op"), VirSpelling.Of), Expr(v.GetProperty("value"))),
            "and" => new AndPattern(Pattern(v.GetProperty("l")), Pattern(v.GetProperty("r"))),
            "or" => new OrPattern(Pattern(v.GetProperty("l")), Pattern(v.GetProperty("r"))),
            "not" => new NotPattern(Pattern(v)),
            _ => throw new FormatException($"Unknown VIR pattern '{name}'."),
        };
    }

    /// <summary>A node kind whose type is fixed by its constructor must agree with the encoded <c>type</c>.</summary>
    private static VirExpr Typed(VirType encoded, VirExpr expr) =>
        expr.Type == encoded ? expr : throw new FormatException($"A {expr.GetType().Name} cannot have type {encoded}.");

    private static DecimalLitExpr DecimalLiteral(JsonElement v)
    {
        var negative = Str(v, "negative") switch
        {
            "false" => false,
            "true" => true,
            var text => throw new FormatException($"Not a sign: '{text}'."),
        };
        var literal = new DecimalLitExpr(
            negative,
            BigInteger.Parse(Str(v, "mantissa"), NumberStyles.None, CultureInfo.InvariantCulture),
            checked((int)Long(Str(v, "scale"))));
        return literal.IsValid ? literal : throw new FormatException($"Not a decimal: mantissa {literal.Mantissa}, scale {literal.Scale}.");
    }

    private static VirOverflow Overflow(JsonElement e) => Parse<VirOverflow>(Str(e, "overflow"), VirSpelling.Of);

    private static long LitValue(VirType type, string text)
    {
        if (type == VirType.Bool)
        {
            return text switch
            {
                "false" => 0,
                "true" => 1,
                _ => throw new FormatException($"Not a bool literal: '{text}'."),
            };
        }
        if (type == VirType.Unit && text != "0")
        {
            throw new FormatException($"Not the unit literal: '{text}'.");
        }
        return Long(text);
    }

    private static T Parse<T>(string text, Func<T, string> spell)
        where T : struct, Enum
    {
        foreach (var value in Enum.GetValues<T>())
        {
            if (spell(value) == text)
            {
                return value;
            }
        }
        throw new FormatException($"Unknown {typeof(T).Name} '{text}'.");
    }

    private static long Long(string text) => long.Parse(text, NumberStyles.AllowLeadingSign, CultureInfo.InvariantCulture);

    private static (string Name, JsonElement Value) Kind(JsonElement e)
    {
        using var props = e.EnumerateObject();
        if (!props.MoveNext())
        {
            throw new FormatException("A VIR node is an object with one field.");
        }
        var first = props.Current;
        if (props.MoveNext())
        {
            throw new FormatException("A VIR node is an object with one field.");
        }
        return (first.Name, first.Value);
    }

    private static string Str(JsonElement e, string name) =>
        e.GetProperty(name).GetString() ?? throw new FormatException($"'{name}' is null.");

    private static VirList<T> List<T>(JsonElement e, Func<JsonElement, T> item) => new(e.EnumerateArray().Select(item).ToList());
}
