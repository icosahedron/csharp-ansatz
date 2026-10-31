using System.Reflection;
using System.Text.Encodings.Web;
using System.Text.Json;
using LeanSharp.Cic;

namespace LeanSharp.Lean4Export;

/// <summary>
/// Writes declarations in lean4export NDJSON format 3.1.0, so other kernels (Lean's own, Ansatz,
/// the kernel-arena checkers) can re-check exactly the terms LeanSharp produced.
/// </summary>
/// <remarks>
/// Names, levels and expressions are deduplicated structurally, each is written once, before its
/// first use, and indices are assigned contiguously from 1 (names, levels) and 0 (expressions).
/// Object keys are written in sorted order, as Lean's JSON printer does. Declarations are written
/// in the order given; the caller is responsible for dependency order.
/// </remarks>
public sealed class Lean4ExportWriter : IDisposable
{
    /// <summary>The format version this writer produces.</summary>
    public const string FormatVersion = "3.1.0";

    private static readonly JsonWriterOptions WriterOptions = new()
    {
        Encoder = JavaScriptEncoder.UnsafeRelaxedJsonEscaping,
        Indented = false,
        SkipValidation = false,
    };

    private readonly Stream _stream;
    private readonly bool _leaveOpen;
    private readonly Utf8JsonWriter _json;
    private readonly Dictionary<Name, int> _names = new() { [Name.Anonymous] = 0 };
    private readonly Dictionary<Level, int> _levels = new() { [Level.Zero] = 0 };
    private readonly Dictionary<Expr, int> _exprsByRef = new(ReferenceEqualityComparer.Instance);
    private readonly Dictionary<Expr, int> _exprs = [];
    private readonly Stack<(Expr Expr, bool ChildrenDone)> _work = new();
    private int _declarationLines;

    /// <summary>Creates a writer and writes the metadata line.</summary>
    /// <param name="stream">The output stream.</param>
    /// <param name="source">
    /// Metadata of the data's origin; its Lean version and githash are carried over. When
    /// <see langword="null"/>, they are written as empty strings.
    /// </param>
    /// <param name="leaveOpen">Whether to leave <paramref name="stream"/> open on dispose.</param>
    public Lean4ExportWriter(Stream stream, ExportMetadata? source = null, bool leaveOpen = false)
    {
        ArgumentNullException.ThrowIfNull(stream);
        _stream = stream;
        _leaveOpen = leaveOpen;
        _json = new Utf8JsonWriter(stream, WriterOptions);
        Metadata = new ExportMetadata("LeanSharp", ToolVersion, source?.LeanGithash ?? "", source?.LeanVersion ?? "", FormatVersion);
        WriteMetadata();
    }

    /// <summary>The metadata written at the start of the file.</summary>
    public ExportMetadata Metadata { get; }

    /// <summary>Counts of the records written so far.</summary>
    public ExportStatistics Statistics => new(_names.Count - 1, _levels.Count - 1, _exprs.Count, _declarationLines);

    private static string ToolVersion =>
        typeof(Lean4ExportWriter).Assembly.GetCustomAttribute<AssemblyInformationalVersionAttribute>()?.InformationalVersion.Split('+')[0]
        ?? "0.0.0";

    /// <summary>Writes a declaration, preceded by any names, levels and expressions it needs.</summary>
    public void Write(Declaration declaration)
    {
        ArgumentNullException.ThrowIfNull(declaration);
        switch (declaration)
        {
            case ConstantDeclaration { Constant: var c }:
                WriteConstant(c);
                break;
            case InductiveDeclaration ind:
                WriteInductive(ind);
                break;
            default:
                throw new ArgumentException($"Unsupported declaration type {declaration.GetType().Name}.", nameof(declaration));
        }
        _declarationLines++;
    }

    /// <summary>Writes several declarations.</summary>
    public void WriteAll(IEnumerable<Declaration> declarations)
    {
        ArgumentNullException.ThrowIfNull(declarations);
        foreach (var d in declarations)
        {
            Write(d);
        }
    }

    /// <summary>Flushes buffered output to the stream.</summary>
    public void Flush()
    {
        _json.Flush();
        _stream.Flush();
    }

    /// <inheritdoc/>
    public void Dispose()
    {
        Flush();
        _json.Dispose();
        if (!_leaveOpen)
        {
            _stream.Dispose();
        }
    }

    // ------------------------------------------------------------------ declarations

    private void WriteConstant(ConstantInfo c)
    {
        int name = EmitName(c.Name);
        int[] lps = EmitNames(c.LevelParams);
        int type = EmitExpr(c.Type);
        switch (c)
        {
            case AxiomInfo a:
                Line(w =>
                {
                    w.WriteStartObject("axiom");
                    w.WriteBoolean("isUnsafe", a.IsUnsafe);
                    WriteIndexArray(w, "levelParams", lps);
                    w.WriteNumber("name", name);
                    w.WriteNumber("type", type);
                    w.WriteEndObject();
                });
                break;
            case DefinitionInfo d:
            {
                int value = EmitExpr(d.DefinitionValue);
                int[] all = EmitNames(d.All);
                Line(w =>
                {
                    w.WriteStartObject("def");
                    WriteIndexArray(w, "all", all);
                    WriteHints(w, d.Hints);
                    WriteIndexArray(w, "levelParams", lps);
                    w.WriteNumber("name", name);
                    w.WriteString("safety", d.Safety switch
                    {
                        DefinitionSafety.Safe => "safe",
                        DefinitionSafety.Unsafe => "unsafe",
                        _ => "partial",
                    });
                    w.WriteNumber("type", type);
                    w.WriteNumber("value", value);
                    w.WriteEndObject();
                });
                break;
            }
            case TheoremInfo t:
            {
                int value = EmitExpr(t.Proof);
                int[] all = EmitNames(t.All);
                Line(w =>
                {
                    w.WriteStartObject("thm");
                    WriteIndexArray(w, "all", all);
                    WriteIndexArray(w, "levelParams", lps);
                    w.WriteNumber("name", name);
                    w.WriteNumber("type", type);
                    w.WriteNumber("value", value);
                    w.WriteEndObject();
                });
                break;
            }
            case OpaqueInfo o:
            {
                int value = EmitExpr(o.OpaqueValue);
                int[] all = EmitNames(o.All);
                Line(w =>
                {
                    w.WriteStartObject("opaque");
                    WriteIndexArray(w, "all", all);
                    w.WriteBoolean("isUnsafe", o.IsUnsafe);
                    WriteIndexArray(w, "levelParams", lps);
                    w.WriteNumber("name", name);
                    w.WriteNumber("type", type);
                    w.WriteNumber("value", value);
                    w.WriteEndObject();
                });
                break;
            }
            case QuotInfo q:
                Line(w =>
                {
                    w.WriteStartObject("quot");
                    w.WriteString("kind", q.QuotKind switch
                    {
                        QuotKind.Type => "type",
                        QuotKind.Ctor => "ctor",
                        QuotKind.Lift => "lift",
                        _ => "ind",
                    });
                    WriteIndexArray(w, "levelParams", lps);
                    w.WriteNumber("name", name);
                    w.WriteNumber("type", type);
                    w.WriteEndObject();
                });
                break;
            default:
                throw new ArgumentException(
                    $"{c.Kind} constant '{c.Name}' must be written as part of an inductive declaration.", nameof(c));
        }
    }

    private void WriteInductive(InductiveDeclaration ind)
    {
        // Emit every dependency first, then write the block as one line.
        var types = ind.Types.Select(t => new
        {
            Info = t,
            Name = EmitName(t.Name),
            Lps = EmitNames(t.LevelParams),
            Type = EmitExpr(t.Type),
            All = EmitNames(t.All),
            Ctors = EmitNames(t.Constructors),
        }).ToList();
        var ctors = ind.Constructors.Select(c => new
        {
            Info = c,
            Name = EmitName(c.Name),
            Lps = EmitNames(c.LevelParams),
            Type = EmitExpr(c.Type),
            Induct = EmitName(c.Inductive),
        }).ToList();
        var recs = ind.Recursors.Select(r => new
        {
            Info = r,
            Name = EmitName(r.Name),
            Lps = EmitNames(r.LevelParams),
            Type = EmitExpr(r.Type),
            All = EmitNames(r.All),
            Rules = r.Rules.Select(rule => (Ctor: EmitName(rule.Constructor), rule.NumFields, Rhs: EmitExpr(rule.Rhs))).ToList(),
        }).ToList();

        Line(w =>
        {
            w.WriteStartObject("inductive");

            w.WriteStartArray("ctors");
            foreach (var c in ctors)
            {
                w.WriteStartObject();
                w.WriteNumber("cidx", c.Info.Index);
                w.WriteNumber("induct", c.Induct);
                w.WriteBoolean("isUnsafe", c.Info.IsUnsafe);
                WriteIndexArray(w, "levelParams", c.Lps);
                w.WriteNumber("name", c.Name);
                w.WriteNumber("numFields", c.Info.NumFields);
                w.WriteNumber("numParams", c.Info.NumParams);
                w.WriteNumber("type", c.Type);
                w.WriteEndObject();
            }
            w.WriteEndArray();

            w.WriteStartArray("recs");
            foreach (var r in recs)
            {
                w.WriteStartObject();
                WriteIndexArray(w, "all", r.All);
                w.WriteBoolean("isUnsafe", r.Info.IsUnsafe);
                w.WriteBoolean("k", r.Info.K);
                WriteIndexArray(w, "levelParams", r.Lps);
                w.WriteNumber("name", r.Name);
                w.WriteNumber("numIndices", r.Info.NumIndices);
                w.WriteNumber("numMinors", r.Info.NumMinors);
                w.WriteNumber("numMotives", r.Info.NumMotives);
                w.WriteNumber("numParams", r.Info.NumParams);
                w.WriteStartArray("rules");
                foreach (var rule in r.Rules)
                {
                    w.WriteStartObject();
                    w.WriteNumber("ctor", rule.Ctor);
                    w.WriteNumber("nfields", rule.NumFields);
                    w.WriteNumber("rhs", rule.Rhs);
                    w.WriteEndObject();
                }
                w.WriteEndArray();
                w.WriteNumber("type", r.Type);
                w.WriteEndObject();
            }
            w.WriteEndArray();

            w.WriteStartArray("types");
            foreach (var t in types)
            {
                w.WriteStartObject();
                WriteIndexArray(w, "all", t.All);
                WriteIndexArray(w, "ctors", t.Ctors);
                w.WriteBoolean("isRec", t.Info.IsRec);
                w.WriteBoolean("isReflexive", t.Info.IsReflexive);
                w.WriteBoolean("isUnsafe", t.Info.IsUnsafe);
                WriteIndexArray(w, "levelParams", t.Lps);
                w.WriteNumber("name", t.Name);
                w.WriteNumber("numIndices", t.Info.NumIndices);
                w.WriteNumber("numNested", t.Info.NumNested);
                w.WriteNumber("numParams", t.Info.NumParams);
                w.WriteNumber("type", t.Type);
                w.WriteEndObject();
            }
            w.WriteEndArray();

            w.WriteEndObject();
        });
    }

    private static void WriteHints(Utf8JsonWriter w, ReducibilityHints hints)
    {
        switch (hints.Kind)
        {
            case ReducibilityHintsKind.Opaque:
                w.WriteString("hints", "opaque");
                break;
            case ReducibilityHintsKind.Abbrev:
                w.WriteString("hints", "abbrev");
                break;
            default:
                w.WriteStartObject("hints");
                w.WriteNumber("regular", hints.Height);
                w.WriteEndObject();
                break;
        }
    }

    // ------------------------------------------------------------------ table entries

    private int EmitName(Name name)
    {
        if (_names.TryGetValue(name, out int idx))
        {
            return idx;
        }
        // Emit missing prefixes from the root down.
        var chain = new Stack<Name>();
        for (var n = name; !_names.ContainsKey(n); n = n.Prefix!)
        {
            chain.Push(n);
        }
        while (chain.Count > 0)
        {
            var n = chain.Pop();
            int pre = _names[n.Prefix!];
            idx = _names.Count;
            _names.Add(n, idx);
            Line(w =>
            {
                w.WriteNumber("in", idx);
                if (n.Kind == NameKind.Str)
                {
                    w.WriteStartObject("str");
                    w.WriteNumber("pre", pre);
                    w.WriteString("str", n.StringComponent);
                }
                else
                {
                    w.WriteStartObject("num");
                    w.WriteNumber("i", n.NumericComponent);
                    w.WriteNumber("pre", pre);
                }
                w.WriteEndObject();
            });
        }
        return idx;
    }

    private int[] EmitNames(EquatableArray<Name> names)
    {
        var result = new int[names.Count];
        for (int i = 0; i < result.Length; i++)
        {
            result[i] = EmitName(names[i]);
        }
        return result;
    }

    private int EmitLevel(Level level)
    {
        if (_levels.TryGetValue(level, out int idx))
        {
            return idx;
        }
        switch (level.Kind)
        {
            case LevelKind.Succ:
            {
                int inner = EmitLevel(level.Lhs!);
                idx = AddLevel(level);
                Line(w =>
                {
                    w.WriteNumber("il", idx);
                    w.WriteNumber("succ", inner);
                });
                break;
            }
            case LevelKind.Max:
            case LevelKind.IMax:
            {
                int l = EmitLevel(level.Lhs!);
                int r = EmitLevel(level.Rhs!);
                idx = AddLevel(level);
                string key = level.Kind == LevelKind.Max ? "max" : "imax";
                Line(w =>
                {
                    w.WriteNumber("il", idx);
                    w.WriteStartArray(key);
                    w.WriteNumberValue(l);
                    w.WriteNumberValue(r);
                    w.WriteEndArray();
                });
                break;
            }
            case LevelKind.Param:
            {
                int n = EmitName(level.ParamName!);
                idx = AddLevel(level);
                Line(w =>
                {
                    w.WriteNumber("il", idx);
                    w.WriteNumber("param", n);
                });
                break;
            }
            default:
                throw new InvalidOperationException($"Unexpected level {level}.");
        }
        return idx;
    }

    private int AddLevel(Level level)
    {
        int idx = _levels.Count;
        _levels.Add(level, idx);
        return idx;
    }

    private int EmitExpr(Expr root)
    {
        if (TryGetExpr(root, out int existing))
        {
            return existing;
        }
        _work.Push((root, false));
        while (_work.Count > 0)
        {
            var (e, childrenDone) = _work.Pop();
            if (TryGetExpr(e, out _))
            {
                continue;
            }
            if (!childrenDone)
            {
                // Names and levels of the node itself first (as lean4export does), then children.
                PrepareLocal(e);
                _work.Push((e, true));
                PushChildren(e);
                continue;
            }
            WriteExprLine(e);
        }
        return _exprsByRef[root];
    }

    private bool TryGetExpr(Expr e, out int idx)
    {
        if (_exprsByRef.TryGetValue(e, out idx))
        {
            return true;
        }
        if (_exprs.TryGetValue(e, out idx))
        {
            _exprsByRef[e] = idx;
            return true;
        }
        return false;
    }

    private void PrepareLocal(Expr e)
    {
        switch (e)
        {
            case SortExpr s:
                EmitLevel(s.Level);
                break;
            case ConstExpr c:
                EmitName(c.Name);
                foreach (var l in c.Levels)
                {
                    EmitLevel(l);
                }
                break;
            case BindingExpr b:
                EmitName(b.BinderName);
                break;
            case LetExpr l:
                EmitName(l.BinderName);
                break;
            case ProjExpr p:
                EmitName(p.TypeName);
                break;
        }
    }

    private void PushChildren(Expr e)
    {
        // Pushed in reverse so they are emitted in field order.
        switch (e)
        {
            case AppExpr a:
                _work.Push((a.Arg, false));
                _work.Push((a.Fn, false));
                break;
            case BindingExpr b:
                _work.Push((b.Body, false));
                _work.Push((b.BinderType, false));
                break;
            case LetExpr l:
                _work.Push((l.Body, false));
                _work.Push((l.Value, false));
                _work.Push((l.BinderType, false));
                break;
            case MDataExpr m:
                _work.Push((m.Expr, false));
                break;
            case ProjExpr p:
                _work.Push((p.Struct, false));
                break;
        }
    }

    private void WriteExprLine(Expr e)
    {
        int idx = _exprs.Count;
        switch (e)
        {
            case BVarExpr b:
                Line(w =>
                {
                    w.WriteNumber("bvar", b.Index);
                    w.WriteNumber("ie", idx);
                });
                break;
            case SortExpr s:
            {
                int l = _levels[s.Level];
                Line(w =>
                {
                    w.WriteNumber("ie", idx);
                    w.WriteNumber("sort", l);
                });
                break;
            }
            case ConstExpr c:
            {
                int n = _names[c.Name];
                var us = c.Levels.Select(l => _levels[l]).ToArray();
                Line(w =>
                {
                    w.WriteStartObject("const");
                    w.WriteNumber("name", n);
                    WriteIndexArray(w, "us", us);
                    w.WriteEndObject();
                    w.WriteNumber("ie", idx);
                });
                break;
            }
            case AppExpr a:
            {
                int fn = _exprsByRef[a.Fn], arg = _exprsByRef[a.Arg];
                Line(w =>
                {
                    w.WriteStartObject("app");
                    w.WriteNumber("arg", arg);
                    w.WriteNumber("fn", fn);
                    w.WriteEndObject();
                    w.WriteNumber("ie", idx);
                });
                break;
            }
            case BindingExpr b:
            {
                int n = _names[b.BinderName], type = _exprsByRef[b.BinderType], body = _exprsByRef[b.Body];
                string key = b.Kind == ExprKind.Lam ? "lam" : "forallE";
                string bi = b.BinderInfo switch
                {
                    BinderInfo.Implicit => "implicit",
                    BinderInfo.StrictImplicit => "strictImplicit",
                    BinderInfo.InstImplicit => "instImplicit",
                    _ => "default",
                };
                Line(w =>
                {
                    // Keys in sorted order: "forallE" < "ie" < "lam".
                    if (b.Kind == ExprKind.Lam)
                    {
                        w.WriteNumber("ie", idx);
                    }
                    w.WriteStartObject(key);
                    w.WriteString("binderInfo", bi);
                    w.WriteNumber("body", body);
                    w.WriteNumber("name", n);
                    w.WriteNumber("type", type);
                    w.WriteEndObject();
                    if (b.Kind != ExprKind.Lam)
                    {
                        w.WriteNumber("ie", idx);
                    }
                });
                break;
            }
            case LetExpr l:
            {
                int n = _names[l.BinderName], type = _exprsByRef[l.BinderType], value = _exprsByRef[l.Value], body = _exprsByRef[l.Body];
                Line(w =>
                {
                    w.WriteNumber("ie", idx);
                    w.WriteStartObject("letE");
                    w.WriteNumber("body", body);
                    w.WriteNumber("name", n);
                    w.WriteBoolean("nondep", l.NonDependent);
                    w.WriteNumber("type", type);
                    w.WriteNumber("value", value);
                    w.WriteEndObject();
                });
                break;
            }
            case NatLitExpr n:
                Line(w =>
                {
                    w.WriteNumber("ie", idx);
                    w.WriteString("natVal", n.Value.ToString(System.Globalization.CultureInfo.InvariantCulture));
                });
                break;
            case StrLitExpr s:
                Line(w =>
                {
                    w.WriteNumber("ie", idx);
                    w.WriteString("strVal", s.Value);
                });
                break;
            case MDataExpr m:
            {
                int inner = _exprsByRef[m.Expr];
                Line(w =>
                {
                    w.WriteNumber("ie", idx);
                    w.WriteStartObject("mdata");
                    w.WriteStartObject("data");
                    foreach (var entry in m.Data.Entries)
                    {
                        w.WriteString(entry.Key, entry.Value);
                    }
                    w.WriteEndObject();
                    w.WriteNumber("expr", inner);
                    w.WriteEndObject();
                });
                break;
            }
            case ProjExpr p:
            {
                int typeName = _names[p.TypeName], structure = _exprsByRef[p.Struct];
                Line(w =>
                {
                    w.WriteNumber("ie", idx);
                    w.WriteStartObject("proj");
                    w.WriteNumber("idx", p.Index);
                    w.WriteNumber("struct", structure);
                    w.WriteNumber("typeName", typeName);
                    w.WriteEndObject();
                });
                break;
            }
            case FVarExpr f:
                throw new ArgumentException($"Free variable '{f.Id}' cannot be exported: exported terms must be closed.");
            default:
                throw new ArgumentException($"Unsupported expression kind {e.Kind}.");
        }
        _exprs.Add(e, idx);
        _exprsByRef[e] = idx;
    }

    // ------------------------------------------------------------------ output

    private void WriteMetadata() => Line(w =>
    {
        w.WriteStartObject("meta");
        w.WriteStartObject("exporter");
        w.WriteString("name", Metadata.ExporterName);
        w.WriteString("version", Metadata.ExporterVersion);
        w.WriteEndObject();
        w.WriteStartObject("format");
        w.WriteString("version", Metadata.FormatVersion);
        w.WriteEndObject();
        w.WriteStartObject("lean");
        w.WriteString("githash", Metadata.LeanGithash);
        w.WriteString("version", Metadata.LeanVersion);
        w.WriteEndObject();
        w.WriteEndObject();
    });

    private void Line(Action<Utf8JsonWriter> body)
    {
        _json.WriteStartObject();
        body(_json);
        _json.WriteEndObject();
        _json.Flush();
        _json.Reset();
        _stream.WriteByte((byte)'\n');
    }

    private static void WriteIndexArray(Utf8JsonWriter w, string key, int[] values)
    {
        w.WriteStartArray(key);
        foreach (int v in values)
        {
            w.WriteNumberValue(v);
        }
        w.WriteEndArray();
    }
}
