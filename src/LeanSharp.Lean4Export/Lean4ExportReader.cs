using System.Globalization;
using System.Numerics;
using System.Text.Json;
using LeanSharp.Cic;

namespace LeanSharp.Lean4Export;

/// <summary>
/// Streaming reader for lean4export NDJSON files (format versions 3.0.0 and 3.1.0).
/// </summary>
/// <remarks>
/// <para>
/// The file is a <c>meta</c> line followed by table lines that define names (<c>in</c>), universe
/// levels (<c>il</c>) and expressions (<c>ie</c>) by integer index, and declaration lines that
/// refer to those indices. Index 0 of the name table is implicitly the anonymous name and index 0
/// of the level table is implicitly level zero. Indices need not be contiguous.
/// </para>
/// <para>
/// The reader is strict: unknown keys, missing fields, references to undefined indices, forward
/// references and redefinitions are all errors, reported with their line number. Accepting
/// something malformed is never safe in a verifier's input path.
/// </para>
/// </remarks>
public sealed class Lean4ExportReader : IDisposable
{
    /// <summary>The format versions this reader accepts.</summary>
    public static readonly IReadOnlySet<string> SupportedFormatVersions = new HashSet<string>(StringComparer.Ordinal) { "3.0.0", "3.1.0" };

    private readonly Stream _stream;
    private readonly bool _leaveOpen;
    private readonly LineReader _lines;
    private readonly bool _v30;
    private readonly IndexTable<Name> _names = new("name");
    private readonly IndexTable<Level> _levels = new("level");
    private readonly IndexTable<Expr> _exprs = new("expression");
    private readonly Queue<Declaration> _pending = new();
    private int _declarationLines;

    /// <summary>Opens a reader and reads the metadata line.</summary>
    /// <param name="stream">The (already decompressed) NDJSON stream.</param>
    /// <param name="leaveOpen">Whether to leave <paramref name="stream"/> open on dispose.</param>
    /// <exception cref="Lean4ExportFormatException">The metadata is missing, malformed or of an unsupported version.</exception>
    public Lean4ExportReader(Stream stream, bool leaveOpen = false)
    {
        ArgumentNullException.ThrowIfNull(stream);
        _stream = stream;
        _leaveOpen = leaveOpen;
        _lines = new LineReader(stream);
        _names.Define(0, Name.Anonymous, 0);
        _levels.Define(0, Level.Zero, 0);
        Metadata = ReadMetadata();
        _v30 = Metadata.FormatVersion == "3.0.0";
    }

    /// <summary>The file's metadata.</summary>
    public ExportMetadata Metadata { get; }

    /// <summary>Counts of the records read so far.</summary>
    public ExportStatistics Statistics =>
        new(_names.Count - 1, _levels.Count - 1, _exprs.Count, _declarationLines);

    /// <summary>Reads the remaining declarations, in file order.</summary>
    public IEnumerable<Declaration> ReadDeclarations()
    {
        while (ReadNextDeclaration() is { } d)
        {
            yield return d;
        }
    }

    /// <summary>Reads the next declaration, or returns <see langword="null"/> at end of file.</summary>
    /// <exception cref="Lean4ExportFormatException">The file is malformed.</exception>
    public Declaration? ReadNextDeclaration()
    {
        while (_pending.Count == 0)
        {
            if (!_lines.TryReadLine(out var line))
            {
                return null;
            }
            if (IsBlank(line.Span))
            {
                continue;
            }
            JsonDocument doc;
            try
            {
                doc = JsonDocument.Parse(line);
            }
            catch (JsonException ex)
            {
                throw Error($"invalid JSON: {ex.Message}", ex);
            }
            using (doc)
            {
                ParseLine(doc.RootElement);
            }
        }
        return _pending.Dequeue();
    }

    /// <inheritdoc/>
    public void Dispose()
    {
        if (!_leaveOpen)
        {
            _stream.Dispose();
        }
    }

    // ------------------------------------------------------------------ metadata

    private ExportMetadata ReadMetadata()
    {
        ReadOnlyMemory<byte> line;
        do
        {
            if (!_lines.TryReadLine(out line))
            {
                throw new Lean4ExportFormatException(0, "empty file: expected a 'meta' line");
            }
        }
        while (IsBlank(line.Span));

        try
        {
            using var doc = JsonDocument.Parse(line);
            var root = Object(doc.RootElement, "line");
            ExpectKeys(root, "meta");
            var meta = Object(Property(root, "meta"), "meta");
            ExpectKeys(meta, "exporter", "lean", "format");
            var exporter = Object(Property(meta, "exporter"), "exporter");
            ExpectKeys(exporter, "name", "version");
            var lean = Object(Property(meta, "lean"), "lean");
            ExpectKeys(lean, "githash", "version");
            var format = Object(Property(meta, "format"), "format");
            ExpectKeys(format, "version");
            var md = new ExportMetadata(
                String(exporter, "name"),
                String(exporter, "version"),
                String(lean, "githash"),
                String(lean, "version"),
                String(format, "version"));
            if (!SupportedFormatVersions.Contains(md.FormatVersion))
            {
                throw Error($"unsupported export format version '{md.FormatVersion}' (supported: {string.Join(", ", SupportedFormatVersions.Order(StringComparer.Ordinal))})");
            }
            return md;
        }
        catch (JsonException ex)
        {
            throw Error($"invalid JSON: {ex.Message}", ex);
        }
    }

    // ------------------------------------------------------------------ dispatch

    private void ParseLine(JsonElement root)
    {
        root = Object(root, "line");
        if (root.TryGetProperty("ie", out var ie))
        {
            var (key, payload) = SinglePayload(root, "ie");
            _exprs.Define(Index(ie, "ie"), ParseExpr(key, payload), _lines.LineNumber);
        }
        else if (root.TryGetProperty("in", out var inn))
        {
            var (key, payload) = SinglePayload(root, "in");
            _names.Define(Index(inn, "in"), ParseName(key, payload), _lines.LineNumber);
        }
        else if (root.TryGetProperty("il", out var il))
        {
            var (key, payload) = SinglePayload(root, "il");
            _levels.Define(Index(il, "il"), ParseLevel(key, payload), _lines.LineNumber);
        }
        else
        {
            var (key, payload) = SinglePayload(root, null);
            _declarationLines++;
            ParseDeclaration(key, payload);
        }
    }

    private (string Key, JsonElement Payload) SinglePayload(JsonElement root, string? indexKey)
    {
        string? key = null;
        JsonElement payload = default;
        foreach (var p in root.EnumerateObject())
        {
            if (p.NameEquals(indexKey))
            {
                continue;
            }
            if (key is not null)
            {
                throw Error($"unexpected key '{p.Name}' alongside '{key}'");
            }
            key = p.Name;
            payload = p.Value;
        }
        return key is null ? throw Error("record has no payload") : (key, payload);
    }

    // ------------------------------------------------------------------ names, levels, exprs

    private Name ParseName(string key, JsonElement payload)
    {
        var obj = Object(payload, key);
        switch (key)
        {
            case "str":
                ExpectKeys(obj, "pre", "str");
                return Name.Str(NameRef(obj, "pre"), String(obj, "str"));
            case "num":
                ExpectKeys(obj, "pre", "i");
                return Name.Num(NameRef(obj, "pre"), UInt64(obj, "i"));
            default:
                throw Error($"unknown name kind '{key}'");
        }
    }

    private Level ParseLevel(string key, JsonElement payload)
    {
        switch (key)
        {
            case "succ":
                return Level.Succ(_levels.Get(Index(payload, key), _lines.LineNumber));
            case "max":
            case "imax":
                if (payload.ValueKind != JsonValueKind.Array || payload.GetArrayLength() != 2)
                {
                    throw Error($"'{key}' must be an array of two level indices");
                }
                var l = _levels.Get(Index(payload[0], key), _lines.LineNumber);
                var r = _levels.Get(Index(payload[1], key), _lines.LineNumber);
                return key == "max" ? Level.Max(l, r) : Level.IMax(l, r);
            case "param":
                return Level.Param(_names.Get(Index(payload, key), _lines.LineNumber));
            default:
                throw Error($"unknown level kind '{key}'");
        }
    }

    private Expr ParseExpr(string key, JsonElement payload)
    {
        switch (key)
        {
            case "bvar":
                return Expr.BVar(Index(payload, key));
            case "sort":
                return Expr.Sort(_levels.Get(Index(payload, key), _lines.LineNumber));
            case "const":
            {
                var obj = Object(payload, key);
                ExpectKeys(obj, "name", "us");
                return Expr.Const(NameRef(obj, "name"), LevelRefs(obj, "us"));
            }
            case "app":
            {
                var obj = Object(payload, key);
                ExpectKeys(obj, "fn", "arg");
                return Expr.App(ExprRef(obj, "fn"), ExprRef(obj, "arg"));
            }
            case "lam":
            case "forallE":
            {
                var obj = Object(payload, key);
                ExpectKeys(obj, "name", "type", "body", "binderInfo");
                var name = NameRef(obj, "name");
                var type = ExprRef(obj, "type");
                var body = ExprRef(obj, "body");
                var bi = ParseBinderInfo(String(obj, "binderInfo"));
                return key == "lam" ? Expr.Lam(name, type, body, bi) : Expr.Forall(name, type, body, bi);
            }
            case "letE":
            {
                var obj = Object(payload, key);
                ExpectKeys(obj, "name", "type", "value", "body", "nondep");
                return Expr.Let(NameRef(obj, "name"), ExprRef(obj, "type"), ExprRef(obj, "value"), ExprRef(obj, "body"), Bool(obj, "nondep"));
            }
            case "proj":
            {
                var obj = Object(payload, key);
                ExpectKeys(obj, "typeName", "idx", "struct");
                return Expr.Proj(NameRef(obj, "typeName"), Index(Property(obj, "idx"), "idx"), ExprRef(obj, "struct"));
            }
            case "natVal":
            {
                var text = payload.ValueKind == JsonValueKind.String ? payload.GetString()! : throw Error("'natVal' must be a string");
                if (text.Length == 0 || !text.All(char.IsAsciiDigit)
                    || !BigInteger.TryParse(text, NumberStyles.None, CultureInfo.InvariantCulture, out var n))
                {
                    throw Error($"invalid natural-number literal '{text}'");
                }
                return Expr.NatLit(n);
            }
            case "strVal":
                return Expr.StrLit(payload.ValueKind == JsonValueKind.String ? payload.GetString()! : throw Error("'strVal' must be a string"));
            case "mdata":
            {
                var obj = Object(payload, key);
                ExpectKeys(obj, "expr", "data");
                var data = Object(Property(obj, "data"), "data");
                var entries = new List<KVMapEntry>();
                foreach (var p in data.EnumerateObject())
                {
                    if (p.Value.ValueKind != JsonValueKind.String)
                    {
                        throw Error($"mdata value for '{p.Name}' must be a string");
                    }
                    entries.Add(new KVMapEntry(p.Name, p.Value.GetString()!));
                }
                return Expr.MData(new KVMap(entries.ToEquatableArray()), ExprRef(obj, "expr"));
            }
            default:
                throw Error($"unknown expression kind '{key}'");
        }
    }

    private BinderInfo ParseBinderInfo(string s) => s switch
    {
        "default" => BinderInfo.Default,
        "implicit" => BinderInfo.Implicit,
        "strictImplicit" => BinderInfo.StrictImplicit,
        "instImplicit" => BinderInfo.InstImplicit,
        _ => throw Error($"unknown binder info '{s}'"),
    };

    // ------------------------------------------------------------------ declarations

    private void ParseDeclaration(string key, JsonElement payload)
    {
        switch (key)
        {
            case "axiom" when !_v30:
            case "axiomInfo" when _v30:
            {
                var obj = Object(payload, key);
                ExpectKeys(obj, "name", "levelParams", "type", "isUnsafe");
                Emit(new AxiomInfo(NameRef(obj, "name"), NameRefs(obj, "levelParams"), ExprRef(obj, "type"), Bool(obj, "isUnsafe")));
                break;
            }
            case "def" when !_v30:
                Emit(ParseDefinition(Object(payload, key)));
                break;
            case "def" when _v30:
                // 3.0.0 groups a mutual block in an array; opaques are distinguished by 'isUnsafe'.
                foreach (var item in Items(payload, key))
                {
                    var obj = Object(item, key);
                    Emit(obj.TryGetProperty("isUnsafe", out _) ? ParseOpaque(obj) : ParseDefinition(obj));
                }
                break;
            case "opaque" when !_v30:
                Emit(ParseOpaque(Object(payload, key)));
                break;
            case "thm" when !_v30:
                Emit(ParseTheorem(Object(payload, key)));
                break;
            case "thm" when _v30:
                foreach (var item in Items(payload, key))
                {
                    Emit(ParseTheorem(Object(item, key)));
                }
                break;
            case "quot" when !_v30:
            case "quotInfo" when _v30:
            {
                var obj = Object(payload, key);
                ExpectKeys(obj, "name", "levelParams", "type", "kind");
                var kind = String(obj, "kind") switch
                {
                    "type" => QuotKind.Type,
                    "ctor" => QuotKind.Ctor,
                    "lift" => QuotKind.Lift,
                    "ind" => QuotKind.Ind,
                    var k => throw Error($"unknown quotient kind '{k}'"),
                };
                Emit(new QuotInfo(NameRef(obj, "name"), NameRefs(obj, "levelParams"), ExprRef(obj, "type"), kind));
                break;
            }
            case "inductive":
                _pending.Enqueue(ParseInductive(Object(payload, key)));
                break;
            default:
                throw Error($"unknown declaration kind '{key}' for format {Metadata.FormatVersion}");
        }
    }

    private void Emit(ConstantInfo c) => _pending.Enqueue(new ConstantDeclaration(c));

    private DefinitionInfo ParseDefinition(JsonElement obj)
    {
        ExpectKeys(obj, "name", "levelParams", "type", "value", "hints", "safety", "all");
        var hints = Property(obj, "hints");
        var parsedHints = hints.ValueKind switch
        {
            JsonValueKind.String when hints.ValueEquals("opaque") => ReducibilityHints.Opaque,
            JsonValueKind.String when hints.ValueEquals("abbrev") => ReducibilityHints.Abbrev,
            JsonValueKind.Object => ParseRegularHint(hints),
            _ => throw Error($"invalid reducibility hints {hints.GetRawText()}"),
        };
        var safety = String(obj, "safety") switch
        {
            "safe" => DefinitionSafety.Safe,
            "unsafe" => DefinitionSafety.Unsafe,
            "partial" => DefinitionSafety.Partial,
            var s => throw Error($"unknown definition safety '{s}'"),
        };
        return new DefinitionInfo(
            NameRef(obj, "name"), NameRefs(obj, "levelParams"), ExprRef(obj, "type"), ExprRef(obj, "value"),
            parsedHints, safety, NameRefs(obj, "all"));
    }

    private ReducibilityHints ParseRegularHint(JsonElement hints)
    {
        ExpectKeys(hints, "regular");
        var h = Property(hints, "regular");
        return h.ValueKind == JsonValueKind.Number && h.TryGetUInt32(out var height)
            ? ReducibilityHints.Regular(height)
            : throw Error($"invalid definitional height {h.GetRawText()}");
    }

    private OpaqueInfo ParseOpaque(JsonElement obj)
    {
        ExpectKeys(obj, "name", "levelParams", "type", "value", "isUnsafe", "all");
        return new OpaqueInfo(
            NameRef(obj, "name"), NameRefs(obj, "levelParams"), ExprRef(obj, "type"), ExprRef(obj, "value"),
            Bool(obj, "isUnsafe"), NameRefs(obj, "all"));
    }

    private TheoremInfo ParseTheorem(JsonElement obj)
    {
        ExpectKeys(obj, "name", "levelParams", "type", "value", "all");
        return new TheoremInfo(
            NameRef(obj, "name"), NameRefs(obj, "levelParams"), ExprRef(obj, "type"), ExprRef(obj, "value"),
            NameRefs(obj, "all"));
    }

    private InductiveDeclaration ParseInductive(JsonElement obj)
    {
        var (typesKey, ctorsKey, recsKey) = _v30
            ? ("inductiveVals", "constructorVals", "recursorVals")
            : ("types", "ctors", "recs");
        ExpectKeys(obj, typesKey, ctorsKey, recsKey);

        var types = new List<InductiveInfo>();
        foreach (var t in Items(Property(obj, typesKey), typesKey))
        {
            var o = Object(t, typesKey);
            ExpectKeys(o, "name", "levelParams", "type", "numParams", "numIndices", "all", "ctors", "numNested", "isRec", "isUnsafe", "isReflexive");
            types.Add(new InductiveInfo(
                NameRef(o, "name"), NameRefs(o, "levelParams"), ExprRef(o, "type"),
                Count(o, "numParams"), Count(o, "numIndices"), NameRefs(o, "all"), NameRefs(o, "ctors"),
                Count(o, "numNested"), Bool(o, "isRec"), Bool(o, "isUnsafe"), Bool(o, "isReflexive")));
        }

        var ctors = new List<ConstructorInfo>();
        foreach (var c in Items(Property(obj, ctorsKey), ctorsKey))
        {
            var o = Object(c, ctorsKey);
            ExpectKeys(o, "name", "levelParams", "type", "induct", "cidx", "numParams", "numFields", "isUnsafe");
            ctors.Add(new ConstructorInfo(
                NameRef(o, "name"), NameRefs(o, "levelParams"), ExprRef(o, "type"), NameRef(o, "induct"),
                Count(o, "cidx"), Count(o, "numParams"), Count(o, "numFields"), Bool(o, "isUnsafe")));
        }

        var recs = new List<RecursorInfo>();
        foreach (var r in Items(Property(obj, recsKey), recsKey))
        {
            var o = Object(r, recsKey);
            ExpectKeys(o, "name", "levelParams", "type", "all", "numParams", "numIndices", "numMotives", "numMinors", "rules", "k", "isUnsafe");
            var rules = new List<RecursorRule>();
            foreach (var rule in Items(Property(o, "rules"), "rules"))
            {
                var ro = Object(rule, "rules");
                ExpectKeys(ro, "ctor", "nfields", "rhs");
                rules.Add(new RecursorRule(NameRef(ro, "ctor"), Count(ro, "nfields"), ExprRef(ro, "rhs")));
            }
            recs.Add(new RecursorInfo(
                NameRef(o, "name"), NameRefs(o, "levelParams"), ExprRef(o, "type"), NameRefs(o, "all"),
                Count(o, "numParams"), Count(o, "numIndices"), Count(o, "numMotives"), Count(o, "numMinors"),
                rules.ToEquatableArray(), Bool(o, "k"), Bool(o, "isUnsafe")));
        }

        return new InductiveDeclaration(types.ToEquatableArray(), ctors.ToEquatableArray(), recs.ToEquatableArray());
    }

    // ------------------------------------------------------------------ JSON helpers

    private Name NameRef(JsonElement obj, string key) => _names.Get(Index(Property(obj, key), key), _lines.LineNumber);

    private Expr ExprRef(JsonElement obj, string key) => _exprs.Get(Index(Property(obj, key), key), _lines.LineNumber);

    private EquatableArray<Name> NameRefs(JsonElement obj, string key)
    {
        var arr = Array(Property(obj, key), key);
        var result = new Name[arr.GetArrayLength()];
        int i = 0;
        foreach (var item in arr.EnumerateArray())
        {
            result[i++] = _names.Get(Index(item, key), _lines.LineNumber);
        }
        return result;
    }

    private EquatableArray<Level> LevelRefs(JsonElement obj, string key)
    {
        var arr = Array(Property(obj, key), key);
        var result = new Level[arr.GetArrayLength()];
        int i = 0;
        foreach (var item in arr.EnumerateArray())
        {
            result[i++] = _levels.Get(Index(item, key), _lines.LineNumber);
        }
        return result;
    }

    private JsonElement Property(JsonElement obj, string key) =>
        obj.TryGetProperty(key, out var value) ? value : throw Error($"missing field '{key}'");

    private JsonElement Object(JsonElement e, string what) =>
        e.ValueKind == JsonValueKind.Object ? e : throw Error($"'{what}' must be an object");

    private JsonElement Array(JsonElement e, string what) =>
        e.ValueKind == JsonValueKind.Array ? e : throw Error($"'{what}' must be an array");

    private JsonElement.ArrayEnumerator Items(JsonElement e, string what) => Array(e, what).EnumerateArray();

    private string String(JsonElement obj, string key)
    {
        var v = Property(obj, key);
        return v.ValueKind == JsonValueKind.String ? v.GetString()! : throw Error($"field '{key}' must be a string");
    }

    private bool Bool(JsonElement obj, string key) => Property(obj, key).ValueKind switch
    {
        JsonValueKind.True => true,
        JsonValueKind.False => false,
        _ => throw Error($"field '{key}' must be a boolean"),
    };

    private ulong UInt64(JsonElement obj, string key)
    {
        var v = Property(obj, key);
        return v.ValueKind == JsonValueKind.Number && v.TryGetUInt64(out var n) ? n : throw Error($"field '{key}' must be a non-negative 64-bit integer");
    }

    private int Count(JsonElement obj, string key) => Index(Property(obj, key), key);

    private int Index(JsonElement v, string what) =>
        v.ValueKind == JsonValueKind.Number && v.TryGetInt32(out var n) && n >= 0
            ? n
            : throw Error($"'{what}' must be a non-negative 32-bit integer, got {v.GetRawText()}");

    private void ExpectKeys(JsonElement obj, params ReadOnlySpan<string> keys)
    {
        int count = 0;
        foreach (var p in obj.EnumerateObject())
        {
            count++;
            bool known = false;
            foreach (var k in keys)
            {
                if (p.NameEquals(k))
                {
                    known = true;
                    break;
                }
            }
            if (!known)
            {
                throw Error($"unexpected field '{p.Name}'");
            }
        }
        if (count != keys.Length)
        {
            foreach (var k in keys)
            {
                if (!obj.TryGetProperty(k, out _))
                {
                    throw Error($"missing field '{k}'");
                }
            }
            throw Error("duplicate field");
        }
    }

    private static bool IsBlank(ReadOnlySpan<byte> line) => line.Trim(" \t"u8).IsEmpty;

    private Lean4ExportFormatException Error(string message, Exception? inner = null) =>
        new(_lines.LineNumber, message, inner);
}
