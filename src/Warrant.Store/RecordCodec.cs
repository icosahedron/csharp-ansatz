using System.Collections.Concurrent;
using System.Numerics;
using Warrant.Cic;

namespace Warrant.Store;

/// <summary>
/// Shares one <see cref="Name"/> object per distinct name across the records a store materializes (KTD18), so a name the
/// kernel compares often is hashed and compared once. Thread-safe.
/// </summary>
public sealed class NameInterner
{
    private readonly ConcurrentDictionary<Name, Name> _names = new();

    /// <summary>The shared name equal to <paramref name="name"/>.</summary>
    public Name Intern(Name name) => _names.GetOrAdd(name, name);
}

/// <summary>
/// One declaration as one self-contained record (KTD17, docs/m5b/05): its own tables of names, levels and expressions,
/// each entry referring only to earlier entries, the way lean4export's lines refer to earlier lines; then the declaration,
/// referring to the tables. Sharing inside a declaration is kept (a repeated subterm is stored once), and a record can be
/// read without reading any other.
/// </summary>
/// <remarks>
/// <para>Layout, with every number a LEB128 varint unless marked as a byte:</para>
/// <code>
/// record      = kind:byte names levels exprs body
/// names       = count { tag:byte(1 str | 2 num) prefix:nameRef (str:string | num:varint) }
/// nameRef     = 0 for the anonymous name, else 1 + an index into names
/// levels      = count { kind:byte(0 zero | 1 succ | 2 max | 3 imax | 4 param) operands }
/// exprs       = count { kind:byte(ExprKind) operands }
/// body        = constant (kind 0), or types ctors recursors counts and their constants (kind 1)
/// </code>
/// <para>
/// Decoding checks every index, enumeration value and length, and that the record ends where its last field does, so a
/// malformed record is a <see cref="StoreFormatException"/>, never a wrong declaration. Free variables and metavariables
/// cannot be encoded: no admitted declaration has them.
/// </para>
/// </remarks>
public static class RecordCodec
{
    private const byte ConstantRecord = 0;
    private const byte InductiveRecord = 1;
    private const byte NameStr = 1;
    private const byte NameNum = 2;

    /// <summary>Encodes a declaration.</summary>
    /// <param name="declaration">The declaration.</param>
    /// <returns>The record's bytes.</returns>
    /// <exception cref="ArgumentException">The declaration has a free variable or a metavariable.</exception>
    public static byte[] Encode(Declaration declaration)
    {
        ArgumentNullException.ThrowIfNull(declaration);
        return new Encoder().Encode(declaration);
    }

    /// <summary>Decodes a record.</summary>
    /// <param name="record">The record's bytes.</param>
    /// <param name="interner">Shares names across records; null for none.</param>
    /// <param name="path">The file the record came from, for messages.</param>
    /// <param name="offset">Where in the file the record starts, for messages.</param>
    /// <returns>The declaration.</returns>
    /// <exception cref="StoreFormatException">The record is malformed.</exception>
    public static Declaration Decode(ReadOnlySpan<byte> record, NameInterner? interner = null, string path = "record", long offset = 0)
    {
        var reader = new ByteReader(record, path, offset);
        var declaration = Decoder.Decode(ref reader, interner);
        if (!reader.AtEnd)
        {
            throw reader.Malformed("bytes follow the declaration");
        }
        return declaration;
    }

    private sealed class Encoder
    {
        private readonly ByteWriter _names = new();
        private readonly ByteWriter _levels = new();
        private readonly ByteWriter _exprs = new();
        private readonly ByteWriter _body = new();
        private readonly Dictionary<Name, int> _nameIndex = [];
        private readonly Dictionary<Level, int> _levelIndex = [];
        private readonly Dictionary<Expr, int> _exprByRef = new(ReferenceEqualityComparer.Instance);
        private readonly Dictionary<Expr, int> _exprIndex = [];
        private readonly Stack<(Expr Expr, bool ChildrenDone)> _work = new();

        public byte[] Encode(Declaration declaration)
        {
            byte kind;
            switch (declaration)
            {
                case ConstantDeclaration c:
                    kind = ConstantRecord;
                    Constant(c.Constant);
                    break;
                case InductiveDeclaration ind:
                    kind = InductiveRecord;
                    _body.VarInt(ind.Types.Count);
                    _body.VarInt(ind.Constructors.Count);
                    _body.VarInt(ind.Recursors.Count);
                    foreach (var c in ind.Constants)
                    {
                        Constant(c);
                    }
                    break;
                default:
                    throw new ArgumentException($"Unsupported declaration {declaration.GetType().Name}.", nameof(declaration));
            }
            var record = new ByteWriter();
            record.Byte(kind);
            record.VarInt(_nameIndex.Count);
            record.Append(_names.WrittenSpan);
            record.VarInt(_levelIndex.Count);
            record.Append(_levels.WrittenSpan);
            record.VarInt(_exprIndex.Count);
            record.Append(_exprs.WrittenSpan);
            record.Append(_body.WrittenSpan);
            return record.WrittenSpan.ToArray();
        }

        private void Constant(ConstantInfo c)
        {
            _body.Byte((byte)c.Kind);
            _body.VarInt(NameRef(c.Name));
            Names(c.LevelParams);
            _body.VarInt(ExprRef(c.Type));
            switch (c)
            {
                case AxiomInfo a:
                    _body.Bool(a.IsUnsafeFlag);
                    break;
                case DefinitionInfo d:
                    _body.VarInt(ExprRef(d.DefinitionValue));
                    _body.Byte((byte)d.Hints.Kind);
                    _body.VarUInt(d.Hints.Height);
                    _body.Byte((byte)d.Safety);
                    Names(d.All);
                    break;
                case TheoremInfo t:
                    _body.VarInt(ExprRef(t.Proof));
                    Names(t.All);
                    break;
                case OpaqueInfo o:
                    _body.VarInt(ExprRef(o.OpaqueValue));
                    _body.Bool(o.IsUnsafeFlag);
                    Names(o.All);
                    break;
                case QuotInfo q:
                    _body.Byte((byte)q.QuotKind);
                    break;
                case InductiveInfo i:
                    _body.VarInt(i.NumParams);
                    _body.VarInt(i.NumIndices);
                    Names(i.All);
                    Names(i.Constructors);
                    _body.VarInt(i.NumNested);
                    _body.Bool(i.IsRec);
                    _body.Bool(i.IsUnsafeFlag);
                    _body.Bool(i.IsReflexive);
                    break;
                case ConstructorInfo k:
                    _body.VarInt(NameRef(k.Inductive));
                    _body.VarInt(k.Index);
                    _body.VarInt(k.NumParams);
                    _body.VarInt(k.NumFields);
                    _body.Bool(k.IsUnsafeFlag);
                    break;
                case RecursorInfo r:
                    Names(r.All);
                    _body.VarInt(r.NumParams);
                    _body.VarInt(r.NumIndices);
                    _body.VarInt(r.NumMotives);
                    _body.VarInt(r.NumMinors);
                    _body.VarInt(r.Rules.Count);
                    foreach (var rule in r.Rules)
                    {
                        _body.VarInt(NameRef(rule.Constructor));
                        _body.VarInt(rule.NumFields);
                        _body.VarInt(ExprRef(rule.Rhs));
                    }
                    _body.Bool(r.K);
                    _body.Bool(r.IsUnsafeFlag);
                    break;
                default:
                    throw new ArgumentException($"Unsupported constant {c.GetType().Name}.", nameof(c));
            }
        }

        private void Names(EquatableArray<Name> names)
        {
            _body.VarInt(names.Count);
            foreach (var n in names)
            {
                _body.VarInt(NameRef(n));
            }
        }

        /// <summary>0 for the anonymous name, else 1 + its index; the name and its prefixes are added first.</summary>
        private int NameRef(Name name)
        {
            if (name.IsAnonymous)
            {
                return 0;
            }
            if (_nameIndex.TryGetValue(name, out int index))
            {
                return index + 1;
            }
            int prefix = NameRef(name.Prefix!);
            index = _nameIndex.Count;
            _nameIndex.Add(name, index);
            if (name.Kind == NameKind.Str)
            {
                _names.Byte(NameStr);
                _names.VarInt(prefix);
                _names.String(name.StringComponent);
            }
            else
            {
                _names.Byte(NameNum);
                _names.VarInt(prefix);
                _names.VarUInt(name.NumericComponent);
            }
            return index + 1;
        }

        private int LevelRef(Level level)
        {
            if (_levelIndex.TryGetValue(level, out int index))
            {
                return index;
            }
            switch (level.Kind)
            {
                case LevelKind.Zero:
                    _levels.Byte(0);
                    break;
                case LevelKind.Succ:
                {
                    int inner = LevelRef(level.Lhs!);
                    _levels.Byte(1);
                    _levels.VarInt(inner);
                    break;
                }
                case LevelKind.Max:
                case LevelKind.IMax:
                {
                    int l = LevelRef(level.Lhs!);
                    int r = LevelRef(level.Rhs!);
                    _levels.Byte(level.Kind == LevelKind.Max ? (byte)2 : (byte)3);
                    _levels.VarInt(l);
                    _levels.VarInt(r);
                    break;
                }
                case LevelKind.Param:
                {
                    int n = NameRef(level.ParamName!);
                    _levels.Byte(4);
                    _levels.VarInt(n);
                    break;
                }
                default:
                    throw new ArgumentException($"The universe metavariable '{level}' cannot be stored: no admitted declaration has one.");
            }
            index = _levelIndex.Count;
            _levelIndex.Add(level, index);
            return index;
        }

        private bool TryGetExpr(Expr e, out int index)
        {
            if (_exprByRef.TryGetValue(e, out index))
            {
                return true;
            }
            if (_exprIndex.TryGetValue(e, out index))
            {
                _exprByRef[e] = index;
                return true;
            }
            return false;
        }

        /// <summary>The expression's index, adding it and every subterm not yet in the table, children first.</summary>
        private int ExprRef(Expr root)
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
                    _work.Push((e, true));
                    foreach (var child in Children(e))
                    {
                        _work.Push((child, false));
                    }
                    continue;
                }
                WriteExpr(e);
            }
            return _exprByRef[root];
        }

        private static IEnumerable<Expr> Children(Expr e) => e switch
        {
            AppExpr a => [a.Arg, a.Fn],
            BindingExpr b => [b.Body, b.BinderType],
            LetExpr l => [l.Body, l.Value, l.BinderType],
            MDataExpr m => [m.Expr],
            ProjExpr p => [p.Struct],
            _ => [],
        };

        private void WriteExpr(Expr e)
        {
            // Operands are resolved before the kind byte is written, so a name or level they add goes into its own table.
            switch (e)
            {
                case BVarExpr b:
                    _exprs.Byte((byte)ExprKind.BVar);
                    _exprs.VarInt(b.Index);
                    break;
                case SortExpr s:
                {
                    int level = LevelRef(s.Level);
                    _exprs.Byte((byte)ExprKind.Sort);
                    _exprs.VarInt(level);
                    break;
                }
                case ConstExpr c:
                {
                    int name = NameRef(c.Name);
                    var levels = c.Levels.Select(LevelRef).ToArray();
                    _exprs.Byte((byte)ExprKind.Const);
                    _exprs.VarInt(name);
                    _exprs.VarInt(levels.Length);
                    foreach (int l in levels)
                    {
                        _exprs.VarInt(l);
                    }
                    break;
                }
                case AppExpr a:
                    _exprs.Byte((byte)ExprKind.App);
                    _exprs.VarInt(_exprByRef[a.Fn]);
                    _exprs.VarInt(_exprByRef[a.Arg]);
                    break;
                case BindingExpr b:
                {
                    int name = NameRef(b.BinderName);
                    _exprs.Byte((byte)b.Kind);
                    _exprs.VarInt(name);
                    _exprs.Byte((byte)b.BinderInfo);
                    _exprs.VarInt(_exprByRef[b.BinderType]);
                    _exprs.VarInt(_exprByRef[b.Body]);
                    break;
                }
                case LetExpr l:
                {
                    int name = NameRef(l.BinderName);
                    _exprs.Byte((byte)ExprKind.Let);
                    _exprs.VarInt(name);
                    _exprs.VarInt(_exprByRef[l.BinderType]);
                    _exprs.VarInt(_exprByRef[l.Value]);
                    _exprs.VarInt(_exprByRef[l.Body]);
                    _exprs.Bool(l.NonDependent);
                    break;
                }
                case NatLitExpr n:
                    _exprs.Byte((byte)ExprKind.NatLit);
                    _exprs.Bytes(n.Value.ToByteArray(isUnsigned: true, isBigEndian: false));
                    break;
                case StrLitExpr s:
                    _exprs.Byte((byte)ExprKind.StrLit);
                    _exprs.String(s.Value);
                    break;
                case MDataExpr m:
                    _exprs.Byte((byte)ExprKind.MData);
                    _exprs.VarInt(m.Data.Entries.Count);
                    foreach (var entry in m.Data.Entries)
                    {
                        _exprs.String(entry.Key);
                        _exprs.String(entry.Value);
                    }
                    _exprs.VarInt(_exprByRef[m.Expr]);
                    break;
                case ProjExpr p:
                {
                    int name = NameRef(p.TypeName);
                    _exprs.Byte((byte)ExprKind.Proj);
                    _exprs.VarInt(name);
                    _exprs.VarInt(p.Index);
                    _exprs.VarInt(_exprByRef[p.Struct]);
                    break;
                }
                default:
                    throw new ArgumentException($"The {e.Kind} expression '{e}' cannot be stored: no admitted declaration has one.");
            }
            int index = _exprIndex.Count;
            _exprIndex.Add(e, index);
            _exprByRef[e] = index;
        }
    }

    private static class Decoder
    {
        public static Declaration Decode(ref ByteReader r, NameInterner? interner)
        {
            byte kind = r.Byte();
            if (kind is not (ConstantRecord or InductiveRecord))
            {
                throw r.Malformed($"{kind} is not a record kind");
            }
            var names = ReadNames(ref r, interner);
            var levels = ReadLevels(ref r, names);
            var exprs = ReadExprs(ref r, names, levels);
            var tables = new Tables(names, exprs);
            if (kind == ConstantRecord)
            {
                return new ConstantDeclaration(ReadConstant(ref r, tables));
            }
            int types = r.VarInt(), ctors = r.VarInt(), recursors = r.VarInt();
            var typeInfos = ImmutableList<InductiveInfo>(ref r, tables, types, "an inductive type");
            var ctorInfos = ImmutableList<ConstructorInfo>(ref r, tables, ctors, "a constructor");
            var recInfos = ImmutableList<RecursorInfo>(ref r, tables, recursors, "a recursor");
            return new InductiveDeclaration(typeInfos, ctorInfos, recInfos);
        }

        private static EquatableArray<T> ImmutableList<T>(ref ByteReader r, Tables tables, int count, string what)
            where T : ConstantInfo
        {
            var items = new T[count];
            for (int i = 0; i < count; i++)
            {
                items[i] = ReadConstant(ref r, tables) as T ?? throw r.Malformed($"an inductive block's constant is not {what}");
            }
            return items.ToEquatableArray();
        }

        private sealed record Tables(Name[] Names, Expr[] Exprs);

        private static Name[] ReadNames(ref ByteReader r, NameInterner? interner)
        {
            int count = r.VarInt();
            var names = new Name[count];
            for (int i = 0; i < count; i++)
            {
                byte tag = r.Byte();
                var prefix = NameAt(ref r, names, i);
                var name = tag switch
                {
                    NameStr => Name.Str(prefix, r.String()),
                    NameNum => Name.Num(prefix, r.VarUInt()),
                    _ => throw r.Malformed($"{tag} is not a name tag"),
                };
                names[i] = interner is null ? name : interner.Intern(name);
            }
            return names;
        }

        /// <summary>A name reference to one of the first <paramref name="limit"/> names.</summary>
        private static Name NameAt(ref ByteReader r, Name[] names, int limit)
        {
            int reference = r.Index(limit + 1, "name");
            return reference == 0 ? Name.Anonymous : names[reference - 1];
        }

        private static Level[] ReadLevels(ref ByteReader r, Name[] names)
        {
            int count = r.VarInt();
            var levels = new Level[count];
            for (int i = 0; i < count; i++)
            {
                byte kind = r.Byte();
                levels[i] = kind switch
                {
                    0 => Level.Zero,
                    1 => Level.Succ(levels[r.Index(i, "level")]),
                    2 => Level.Max(levels[r.Index(i, "level")], levels[r.Index(i, "level")]),
                    3 => Level.IMax(levels[r.Index(i, "level")], levels[r.Index(i, "level")]),
                    4 => Level.Param(NameAt(ref r, names, names.Length)),
                    _ => throw r.Malformed($"{kind} is not a level kind"),
                };
            }
            return levels;
        }

        private static Expr[] ReadExprs(ref ByteReader r, Name[] names, Level[] levels)
        {
            int count = r.VarInt();
            var exprs = new Expr[count];
            for (int i = 0; i < count; i++)
            {
                byte kind = r.Byte();
                exprs[i] = (ExprKind)kind switch
                {
                    ExprKind.BVar => Expr.BVar(Checked(ref r, r.VarInt(), int.MaxValue - 1, "a bound variable index")),
                    ExprKind.Sort => Expr.Sort(levels[r.Index(levels.Length, "level")]),
                    ExprKind.Const => Const(ref r, names, levels),
                    ExprKind.App => Expr.App(exprs[r.Index(i, "expression")], exprs[r.Index(i, "expression")]),
                    ExprKind.Lam or ExprKind.Forall => Binding(ref r, (ExprKind)kind, names, exprs, i),
                    ExprKind.Let => Expr.Let(NameAt(ref r, names, names.Length), exprs[r.Index(i, "expression")], exprs[r.Index(i, "expression")], exprs[r.Index(i, "expression")], r.Bool()),
                    ExprKind.NatLit => Expr.NatLit(new BigInteger(r.Bytes(), isUnsigned: true, isBigEndian: false)),
                    ExprKind.StrLit => Expr.StrLit(r.String()),
                    ExprKind.MData => MData(ref r, exprs, i),
                    ExprKind.Proj => Expr.Proj(NameAt(ref r, names, names.Length), r.VarInt(), exprs[r.Index(i, "expression")]),
                    _ => throw r.Malformed($"{kind} is not an expression kind a record holds"),
                };
            }
            return exprs;
        }

        private static int Checked(ref ByteReader r, int value, int max, string what) =>
            value <= max ? value : throw r.Malformed($"{what} {value} is out of range");

        private static ConstExpr Const(ref ByteReader r, Name[] names, Level[] levels)
        {
            var name = NameAt(ref r, names, names.Length);
            int count = r.VarInt();
            var args = new Level[count];
            for (int j = 0; j < count; j++)
            {
                args[j] = levels[r.Index(levels.Length, "level")];
            }
            return Expr.Const(name, args.ToEquatableArray());
        }

        private static Expr Binding(ref ByteReader r, ExprKind kind, Name[] names, Expr[] exprs, int limit)
        {
            var name = NameAt(ref r, names, names.Length);
            byte info = r.Byte();
            if (info > (byte)BinderInfo.InstImplicit)
            {
                throw r.Malformed($"{info} is not a binder annotation");
            }
            var type = exprs[r.Index(limit, "expression")];
            var body = exprs[r.Index(limit, "expression")];
            return kind == ExprKind.Lam
                ? Expr.Lam(name, type, body, (BinderInfo)info)
                : Expr.Forall(name, type, body, (BinderInfo)info);
        }

        private static MDataExpr MData(ref ByteReader r, Expr[] exprs, int limit)
        {
            int count = r.VarInt();
            var entries = new KVMapEntry[count];
            for (int j = 0; j < count; j++)
            {
                entries[j] = new KVMapEntry(r.String(), r.String());
            }
            return Expr.MData(new KVMap(entries.ToEquatableArray()), exprs[r.Index(limit, "expression")]);
        }

        private static EquatableArray<Name> NameList(ref ByteReader r, Name[] names)
        {
            int count = r.VarInt();
            var list = new Name[count];
            for (int j = 0; j < count; j++)
            {
                list[j] = NameAt(ref r, names, names.Length);
            }
            return list.ToEquatableArray();
        }

        private static Expr ExprAt(ref ByteReader r, Expr[] exprs) => exprs[r.Index(exprs.Length, "expression")];

        private static ConstantInfo ReadConstant(ref ByteReader r, Tables t)
        {
            byte kind = r.Byte();
            var name = NameAt(ref r, t.Names, t.Names.Length);
            var levelParams = NameList(ref r, t.Names);
            var type = ExprAt(ref r, t.Exprs);
            switch ((ConstantKind)kind)
            {
                case ConstantKind.Axiom:
                    return new AxiomInfo(name, levelParams, type, r.Bool());
                case ConstantKind.Definition:
                {
                    var value = ExprAt(ref r, t.Exprs);
                    byte hints = r.Byte();
                    if (hints > (byte)ReducibilityHintsKind.Regular)
                    {
                        throw r.Malformed($"{hints} is not a reducibility hint");
                    }
                    ulong height = r.VarUInt();
                    if (height > uint.MaxValue)
                    {
                        throw r.Malformed($"the definitional height {height} is out of range");
                    }
                    byte safety = r.Byte();
                    if (safety > (byte)DefinitionSafety.Partial)
                    {
                        throw r.Malformed($"{safety} is not a definition safety");
                    }
                    return new DefinitionInfo(name, levelParams, type, value, new ReducibilityHints((ReducibilityHintsKind)hints, (uint)height), (DefinitionSafety)safety, NameList(ref r, t.Names));
                }
                case ConstantKind.Theorem:
                    return new TheoremInfo(name, levelParams, type, ExprAt(ref r, t.Exprs), NameList(ref r, t.Names));
                case ConstantKind.Opaque:
                    return new OpaqueInfo(name, levelParams, type, ExprAt(ref r, t.Exprs), r.Bool(), NameList(ref r, t.Names));
                case ConstantKind.Quot:
                {
                    byte quot = r.Byte();
                    return quot <= (byte)QuotKind.Ind
                        ? new QuotInfo(name, levelParams, type, (QuotKind)quot)
                        : throw r.Malformed($"{quot} is not a quotient kind");
                }
                case ConstantKind.Inductive:
                    return new InductiveInfo(name, levelParams, type, r.VarInt(), r.VarInt(), NameList(ref r, t.Names), NameList(ref r, t.Names), r.VarInt(), r.Bool(), r.Bool(), r.Bool());
                case ConstantKind.Constructor:
                    return new ConstructorInfo(name, levelParams, type, NameAt(ref r, t.Names, t.Names.Length), r.VarInt(), r.VarInt(), r.VarInt(), r.Bool());
                case ConstantKind.Recursor:
                {
                    var all = NameList(ref r, t.Names);
                    int numParams = r.VarInt(), numIndices = r.VarInt(), numMotives = r.VarInt(), numMinors = r.VarInt();
                    int ruleCount = r.VarInt();
                    var rules = new RecursorRule[ruleCount];
                    for (int j = 0; j < ruleCount; j++)
                    {
                        rules[j] = new RecursorRule(NameAt(ref r, t.Names, t.Names.Length), r.VarInt(), ExprAt(ref r, t.Exprs));
                    }
                    return new RecursorInfo(name, levelParams, type, all, numParams, numIndices, numMotives, numMinors, rules.ToEquatableArray(), r.Bool(), r.Bool());
                }
                default:
                    throw r.Malformed($"{kind} is not a constant kind");
            }
        }
    }
}
