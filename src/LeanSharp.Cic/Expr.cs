using System.Numerics;
using System.Runtime.CompilerServices;
using System.Text;

namespace LeanSharp.Cic;

/// <summary>The twelve expression kinds of the CIC kernel.</summary>
/// <remarks>
/// Metavariables are deliberately absent: they are an elaborator concept, and the kernel only
/// checks fully elaborated terms.
/// </remarks>
public enum ExprKind : byte
{
    /// <summary>A bound variable (de Bruijn index).</summary>
    BVar,

    /// <summary>A free variable from the local context.</summary>
    FVar,

    /// <summary>A universe: <c>Sort u</c>.</summary>
    Sort,

    /// <summary>A reference to a global constant, with universe arguments.</summary>
    Const,

    /// <summary>Function application.</summary>
    App,

    /// <summary>Lambda abstraction.</summary>
    Lam,

    /// <summary>Dependent function type (Π / ∀).</summary>
    Forall,

    /// <summary>Local definition.</summary>
    Let,

    /// <summary>Natural-number literal.</summary>
    NatLit,

    /// <summary>String literal.</summary>
    StrLit,

    /// <summary>Metadata annotation (ignored by type checking).</summary>
    MData,

    /// <summary>Structure projection.</summary>
    Proj,
}

/// <summary>How a binder's argument is supplied, mirroring Lean's <c>BinderInfo</c>.</summary>
public enum BinderInfo : byte
{
    /// <summary>Explicit argument: <c>(x : A)</c>.</summary>
    Default,

    /// <summary>Implicit argument: <c>{x : A}</c>.</summary>
    Implicit,

    /// <summary>Strict implicit argument: <c>⦃x : A⦄</c>.</summary>
    StrictImplicit,

    /// <summary>Instance-implicit argument: <c>[x : A]</c>.</summary>
    InstImplicit,
}

/// <summary>The identity of a free variable.</summary>
/// <param name="Name">A name unique within the local context.</param>
public readonly record struct FVarId(Name Name)
{
    /// <inheritdoc/>
    public override string ToString() => Name.ToString();
}

/// <summary>
/// A CIC expression, mirroring Lean 4's kernel <c>Expr</c>.
/// </summary>
/// <remarks>
/// <para>
/// Expressions are immutable DAGs. Each node caches, at construction, a deterministic hash and the
/// flags the kernel needs constantly (<see cref="LooseBVarRange"/>, <see cref="HasFVar"/>,
/// <see cref="HasLevelParam"/>), as Lean does.
/// </para>
/// <para>
/// <see cref="Equals(Expr)"/> is exact structural equality, including binder names, binder info and
/// metadata. The hash ignores binder names, binder info and metadata contents, so it is also
/// compatible with equality up to those annotations. Equality is iterative (no recursion limit) and
/// visits each pair of shared subterms once, so comparing large DAGs stays linear in their size.
/// </para>
/// </remarks>
public abstract class Expr : IEquatable<Expr>
{
    /// <summary><c>Prop</c>, i.e. <c>Sort 0</c>.</summary>
    public static readonly SortExpr Prop = new(Level.Zero);

    /// <summary><c>Type</c>, i.e. <c>Sort 1</c>.</summary>
    public static readonly SortExpr Type = new(Level.One);

    private protected Expr(ExprKind kind, ulong hash, int looseBVarRange, bool hasFVar, bool hasLevelParam)
    {
        Kind = kind;
        Hash64 = hash;
        LooseBVarRange = looseBVarRange;
        HasFVar = hasFVar;
        HasLevelParam = hasLevelParam;
    }

    /// <summary>Which kind of node this is.</summary>
    public ExprKind Kind { get; }

    /// <summary>
    /// One more than the largest loose bound-variable index, or 0 if the expression is closed under
    /// binders (for example <c>#2</c> has range 3; <c>fun x => #0</c> has range 0).
    /// </summary>
    public int LooseBVarRange { get; }

    /// <summary>Whether a loose bound variable occurs.</summary>
    public bool HasLooseBVars => LooseBVarRange > 0;

    /// <summary>Whether a free variable occurs.</summary>
    public bool HasFVar { get; }

    /// <summary>Whether a universe parameter occurs (in a <c>Sort</c> or constant's levels).</summary>
    public bool HasLevelParam { get; }

    internal ulong Hash64 { get; }

    // ---------------------------------------------------------------- factories

    /// <summary>Bound variable <c>#index</c>.</summary>
    public static BVarExpr BVar(int index) => new(index);

    /// <summary>Free variable.</summary>
    public static FVarExpr FVar(FVarId id) => new(id);

    /// <summary><c>Sort level</c>.</summary>
    public static SortExpr Sort(Level level) => new(level);

    /// <summary>Constant <paramref name="name"/> instantiated at <paramref name="levels"/>.</summary>
    public static ConstExpr Const(Name name, EquatableArray<Level> levels) => new(name, levels);

    /// <summary>Constant <paramref name="name"/> instantiated at <paramref name="levels"/>.</summary>
    public static ConstExpr Const(Name name, params ReadOnlySpan<Level> levels) => new(name, EquatableArray.Create(levels));

    /// <summary>Application <c>fn arg</c>.</summary>
    public static AppExpr App(Expr fn, Expr arg) => new(fn, arg);

    /// <summary>Left-nested application <c>fn a₁ … aₙ</c>; returns <paramref name="fn"/> when there are no arguments.</summary>
    public static Expr App(Expr fn, params ReadOnlySpan<Expr> args)
    {
        var e = fn;
        foreach (var a in args)
        {
            e = new AppExpr(e, a);
        }
        return e;
    }

    /// <summary>Lambda <c>fun (name : type) => body</c>.</summary>
    public static LamExpr Lam(Name name, Expr type, Expr body, BinderInfo info = BinderInfo.Default) =>
        new(name, type, body, info);

    /// <summary>Pi type <c>(name : type) → body</c>.</summary>
    public static ForallExpr Forall(Name name, Expr type, Expr body, BinderInfo info = BinderInfo.Default) =>
        new(name, type, body, info);

    /// <summary>Let binding <c>let name : type := value; body</c>.</summary>
    public static LetExpr Let(Name name, Expr type, Expr value, Expr body, bool nonDependent = false) =>
        new(name, type, value, body, nonDependent);

    /// <summary>Natural-number literal.</summary>
    public static NatLitExpr NatLit(BigInteger value) => new(value);

    /// <summary>String literal.</summary>
    public static StrLitExpr StrLit(string value) => new(value);

    /// <summary>Metadata annotation around <paramref name="expr"/>.</summary>
    public static MDataExpr MData(KVMap data, Expr expr) => new(data, expr);

    /// <summary>Projection of field <paramref name="index"/> of structure <paramref name="typeName"/>.</summary>
    public static ProjExpr Proj(Name typeName, int index, Expr structure) => new(typeName, index, structure);

    // ---------------------------------------------------------------- application spines

    /// <summary>The head of an application spine (<c>f</c> in <c>f a b c</c>).</summary>
    public Expr GetAppFn()
    {
        var e = this;
        while (e is AppExpr app)
        {
            e = app.Fn;
        }
        return e;
    }

    /// <summary>The number of arguments in an application spine.</summary>
    public int GetAppNumArgs()
    {
        int n = 0;
        var e = this;
        while (e is AppExpr app)
        {
            n++;
            e = app.Fn;
        }
        return n;
    }

    /// <summary>The arguments of an application spine, outermost function first.</summary>
    public Expr[] GetAppArgs()
    {
        var args = new Expr[GetAppNumArgs()];
        var e = this;
        for (int i = args.Length - 1; i >= 0; i--)
        {
            var app = (AppExpr)e;
            args[i] = app.Arg;
            e = app.Fn;
        }
        return args;
    }

    // ---------------------------------------------------------------- equality

    /// <inheritdoc/>
    public bool Equals(Expr? other)
    {
        if (ReferenceEquals(this, other))
        {
            return true;
        }
        if (other is null || Hash64 != other.Hash64 || Kind != other.Kind)
        {
            return false;
        }
        return StructuralEquality.AreEqual(this, other, strict: true);
    }

    /// <summary>
    /// Equality up to binder annotations: binder names (of lambdas, Pis and lets) and binder info are
    /// ignored; everything else, including metadata, must match. This is the Lean kernel's notion of
    /// expression equality (its <c>==</c>, <c>is_equal</c>), and Lean's <c>BEq Expr</c>.
    /// </summary>
    public bool AlphaEquals(Expr? other)
    {
        if (ReferenceEquals(this, other))
        {
            return true;
        }
        if (other is null || Hash64 != other.Hash64 || Kind != other.Kind)
        {
            return false;
        }
        return StructuralEquality.AreEqual(this, other, strict: false);
    }

    /// <summary>A comparer that uses <see cref="AlphaEquals"/>, for kernel caches.</summary>
    public static IEqualityComparer<Expr> AlphaComparer { get; } = new AlphaEqualityComparer();

    private sealed class AlphaEqualityComparer : IEqualityComparer<Expr>
    {
        public bool Equals(Expr? x, Expr? y) => x is null ? y is null : x.AlphaEquals(y);

        public int GetHashCode(Expr obj) => obj.GetHashCode();
    }

    /// <inheritdoc/>
    public override bool Equals(object? obj) => obj is Expr e && Equals(e);

    /// <inheritdoc/>
    public override int GetHashCode() => Hashing.Fold(Hash64);

    /// <summary>Equality operator (structural).</summary>
    public static bool operator ==(Expr? left, Expr? right) =>
        left is null ? right is null : left.Equals(right);

    /// <summary>Inequality operator (structural).</summary>
    public static bool operator !=(Expr? left, Expr? right) => !(left == right);

    /// <summary>
    /// Compares the node-local data of two nodes of the same kind and pushes their children.
    /// Returns false on a local mismatch.
    /// </summary>
    private protected abstract bool LocalEquals(Expr other, Stack<(Expr, Expr)> pending, bool strict);

    private static class StructuralEquality
    {
        // After this many compound nodes, start remembering visited pairs so shared subterms
        // are compared once (a DAG's tree unfolding can be exponentially larger than the DAG).
        private const int VisitedThreshold = 256;

        [ThreadStatic]
        private static Stack<(Expr, Expr)>? s_pending;

        [ThreadStatic]
        private static HashSet<(Expr, Expr)>? s_visited;

        public static bool AreEqual(Expr a, Expr b, bool strict)
        {
            var pending = s_pending ?? new Stack<(Expr, Expr)>();
            s_pending = null; // guard against reentrancy: a nested call allocates its own
            var visited = s_visited ?? new HashSet<(Expr, Expr)>(PairComparer.Instance);
            s_visited = null;
            try
            {
                pending.Push((a, b));
                int compound = 0;
                while (pending.Count > 0)
                {
                    var (x, y) = pending.Pop();
                    if (ReferenceEquals(x, y))
                    {
                        continue;
                    }
                    if (x.Hash64 != y.Hash64 || x.Kind != y.Kind || x.LooseBVarRange != y.LooseBVarRange)
                    {
                        return false;
                    }
                    if (x.Kind is ExprKind.App or ExprKind.Lam or ExprKind.Forall or ExprKind.Let
                        or ExprKind.MData or ExprKind.Proj)
                    {
                        if (++compound > VisitedThreshold && !visited.Add((x, y)))
                        {
                            continue;
                        }
                    }
                    if (!x.LocalEquals(y, pending, strict))
                    {
                        return false;
                    }
                }
                return true;
            }
            finally
            {
                pending.Clear();
                visited.Clear();
                if (visited.Count == 0 && visited.EnsureCapacity(0) > 4096)
                {
                    visited.TrimExcess();
                }
                s_pending = pending;
                s_visited = visited;
            }
        }
    }

    private sealed class PairComparer : IEqualityComparer<(Expr, Expr)>
    {
        public static readonly PairComparer Instance = new();

        public bool Equals((Expr, Expr) x, (Expr, Expr) y) =>
            ReferenceEquals(x.Item1, y.Item1) && ReferenceEquals(x.Item2, y.Item2);

        public int GetHashCode((Expr, Expr) obj) =>
            HashCode.Combine(RuntimeHelpers.GetHashCode(obj.Item1), RuntimeHelpers.GetHashCode(obj.Item2));
    }

    // ---------------------------------------------------------------- printing

    /// <summary>
    /// A compact debugging rendering: bound variables print as <c>#i</c>, binders show their names.
    /// Deep terms are elided.
    /// </summary>
    public override string ToString()
    {
        var sb = new StringBuilder();
        Print(sb, this, 0);
        return sb.ToString();
    }

    private const int MaxPrintDepth = 64;

    private static void Print(StringBuilder sb, Expr e, int depth)
    {
        if (depth > MaxPrintDepth)
        {
            sb.Append('…');
            return;
        }
        switch (e)
        {
            case BVarExpr b:
                sb.Append('#').Append(b.Index);
                break;
            case FVarExpr f:
                sb.Append(f.Id);
                break;
            case SortExpr s:
                if (s.Level.Kind == LevelKind.Zero)
                {
                    sb.Append("Prop");
                }
                else
                {
                    sb.Append("Sort ").Append(s.Level.Kind is LevelKind.Max or LevelKind.IMax ? $"({s.Level})" : s.Level.ToString());
                }
                break;
            case ConstExpr c:
                sb.Append(c.Name);
                if (c.Levels.Count > 0)
                {
                    sb.Append(".{").Append(string.Join(", ", c.Levels)).Append('}');
                }
                break;
            case AppExpr:
                sb.Append('(');
                Print(sb, e.GetAppFn(), depth + 1);
                foreach (var arg in e.GetAppArgs())
                {
                    sb.Append(' ');
                    Print(sb, arg, depth + 1);
                }
                sb.Append(')');
                break;
            case BindingExpr bnd:
                sb.Append(bnd.Kind == ExprKind.Lam ? "(fun " : "(");
                var (open, close) = bnd.BinderInfo switch
                {
                    BinderInfo.Implicit => ("{", "}"),
                    BinderInfo.StrictImplicit => ("⦃", "⦄"),
                    BinderInfo.InstImplicit => ("[", "]"),
                    _ => ("(", ")"),
                };
                sb.Append(open).Append(bnd.BinderName).Append(" : ");
                Print(sb, bnd.BinderType, depth + 1);
                sb.Append(close).Append(bnd.Kind == ExprKind.Lam ? " => " : " → ");
                Print(sb, bnd.Body, depth + 1);
                sb.Append(')');
                break;
            case LetExpr l:
                sb.Append("(let ").Append(l.BinderName).Append(" : ");
                Print(sb, l.BinderType, depth + 1);
                sb.Append(" := ");
                Print(sb, l.Value, depth + 1);
                sb.Append("; ");
                Print(sb, l.Body, depth + 1);
                sb.Append(')');
                break;
            case NatLitExpr n:
                sb.Append(n.Value);
                break;
            case StrLitExpr s:
                sb.Append('"').Append(s.Value.Replace("\\", "\\\\", StringComparison.Ordinal).Replace("\"", "\\\"", StringComparison.Ordinal)).Append('"');
                break;
            case MDataExpr m:
                Print(sb, m.Expr, depth);
                break;
            case ProjExpr p:
                Print(sb, p.Struct, depth + 1);
                sb.Append('.').Append(p.Index + 1);
                break;
        }
    }

    private protected static ulong LevelsHash(EquatableArray<Level> levels)
    {
        ulong h = 0x0F1E2D3C4B5A6978UL;
        foreach (var l in levels)
        {
            h = Hashing.Mix(h, l.Hash64);
        }
        return h;
    }

    private protected static bool AnyHasParam(EquatableArray<Level> levels)
    {
        foreach (var l in levels)
        {
            if (l.HasParam)
            {
                return true;
            }
        }
        return false;
    }
}

/// <summary>A bound variable, identified by its de Bruijn index.</summary>
public sealed class BVarExpr : Expr
{
    internal BVarExpr(int index)
        : base(ExprKind.BVar, Hashing.Mix(1, (ulong)index), CheckIndex(index) + 1, false, false) => Index = index;

    /// <summary>The de Bruijn index: 0 is the innermost enclosing binder.</summary>
    public int Index { get; }

    private static int CheckIndex(int index)
    {
        ArgumentOutOfRangeException.ThrowIfNegative(index);
        ArgumentOutOfRangeException.ThrowIfEqual(index, int.MaxValue);
        return index;
    }

    private protected override bool LocalEquals(Expr other, Stack<(Expr, Expr)> pending, bool strict) =>
        Index == ((BVarExpr)other).Index;
}

/// <summary>A free variable of the local context.</summary>
public sealed class FVarExpr : Expr
{
    internal FVarExpr(FVarId id)
        : base(ExprKind.FVar, Hashing.Mix(2, (id.Name ?? throw new ArgumentNullException(nameof(id))).Hash64), 0, true, false) => Id = id;

    /// <summary>The variable's identity.</summary>
    public FVarId Id { get; }

    private protected override bool LocalEquals(Expr other, Stack<(Expr, Expr)> pending, bool strict) =>
        Id == ((FVarExpr)other).Id;
}

/// <summary><c>Sort u</c>.</summary>
public sealed class SortExpr : Expr
{
    internal SortExpr(Level level)
        : base(ExprKind.Sort, Hashing.Mix(3, (level ?? throw new ArgumentNullException(nameof(level))).Hash64), 0, false, level.HasParam) => Level = level;

    /// <summary>The universe level.</summary>
    public Level Level { get; }

    private protected override bool LocalEquals(Expr other, Stack<(Expr, Expr)> pending, bool strict) =>
        Level.Equals(((SortExpr)other).Level);
}

/// <summary>A reference to a global constant, instantiated at universe levels.</summary>
public sealed class ConstExpr : Expr
{
    internal ConstExpr(Name name, EquatableArray<Level> levels)
        : base(ExprKind.Const, Hashing.Mix(4, (name ?? throw new ArgumentNullException(nameof(name))).Hash64, LevelsHash(levels)), 0, false, AnyHasParam(levels))
    {
        Name = name;
        Levels = levels;
    }

    /// <summary>The constant's name.</summary>
    public Name Name { get; }

    /// <summary>The universe arguments.</summary>
    public EquatableArray<Level> Levels { get; }

    private protected override bool LocalEquals(Expr other, Stack<(Expr, Expr)> pending, bool strict)
    {
        var o = (ConstExpr)other;
        return Name.Equals(o.Name) && Levels.Equals(o.Levels);
    }
}

/// <summary>Function application.</summary>
public sealed class AppExpr : Expr
{
    internal AppExpr(Expr fn, Expr arg)
        : base(
            ExprKind.App,
            Hashing.Mix(5, (fn ?? throw new ArgumentNullException(nameof(fn))).Hash64, (arg ?? throw new ArgumentNullException(nameof(arg))).Hash64),
            Math.Max(fn.LooseBVarRange, arg.LooseBVarRange),
            fn.HasFVar || arg.HasFVar,
            fn.HasLevelParam || arg.HasLevelParam)
    {
        Fn = fn;
        Arg = arg;
    }

    /// <summary>The function.</summary>
    public Expr Fn { get; }

    /// <summary>The argument.</summary>
    public Expr Arg { get; }

    private protected override bool LocalEquals(Expr other, Stack<(Expr, Expr)> pending, bool strict)
    {
        var o = (AppExpr)other;
        pending.Push((Arg, o.Arg));
        pending.Push((Fn, o.Fn));
        return true;
    }
}

/// <summary>A binder: lambda or Pi.</summary>
public abstract class BindingExpr : Expr
{
    private protected BindingExpr(ExprKind kind, Name name, Expr type, Expr body, BinderInfo info)
        : base(
            kind,
            Hashing.Mix((ulong)kind + 100, (type ?? throw new ArgumentNullException(nameof(type))).Hash64, (body ?? throw new ArgumentNullException(nameof(body))).Hash64),
            Math.Max(type.LooseBVarRange, Math.Max(body.LooseBVarRange - 1, 0)),
            type.HasFVar || body.HasFVar,
            type.HasLevelParam || body.HasLevelParam)
    {
        BinderName = name ?? throw new ArgumentNullException(nameof(name));
        BinderType = type;
        Body = body;
        BinderInfo = info;
    }

    /// <summary>The binder's display name (irrelevant to typing).</summary>
    public Name BinderName { get; }

    /// <summary>The binder's type (domain).</summary>
    public Expr BinderType { get; }

    /// <summary>The body, in which <c>#0</c> refers to this binder.</summary>
    public Expr Body { get; }

    /// <summary>How the argument is supplied.</summary>
    public BinderInfo BinderInfo { get; }

    private protected override bool LocalEquals(Expr other, Stack<(Expr, Expr)> pending, bool strict)
    {
        var o = (BindingExpr)other;
        if (strict && (BinderInfo != o.BinderInfo || !BinderName.Equals(o.BinderName)))
        {
            return false;
        }
        pending.Push((Body, o.Body));
        pending.Push((BinderType, o.BinderType));
        return true;
    }
}

/// <summary>Lambda abstraction <c>fun (x : A) => b</c>.</summary>
public sealed class LamExpr : BindingExpr
{
    internal LamExpr(Name name, Expr type, Expr body, BinderInfo info)
        : base(ExprKind.Lam, name, type, body, info)
    {
    }
}

/// <summary>Dependent function type <c>(x : A) → B</c>.</summary>
public sealed class ForallExpr : BindingExpr
{
    internal ForallExpr(Name name, Expr type, Expr body, BinderInfo info)
        : base(ExprKind.Forall, name, type, body, info)
    {
    }
}

/// <summary>Local definition <c>let x : A := v; b</c>.</summary>
public sealed class LetExpr : Expr
{
    internal LetExpr(Name name, Expr type, Expr value, Expr body, bool nonDependent)
        : base(
            ExprKind.Let,
            Hashing.Mix(
                Hashing.Mix(8, (type ?? throw new ArgumentNullException(nameof(type))).Hash64),
                (value ?? throw new ArgumentNullException(nameof(value))).Hash64,
                (body ?? throw new ArgumentNullException(nameof(body))).Hash64),
            Math.Max(Math.Max(type.LooseBVarRange, value.LooseBVarRange), Math.Max(body.LooseBVarRange - 1, 0)),
            type.HasFVar || value.HasFVar || body.HasFVar,
            type.HasLevelParam || value.HasLevelParam || body.HasLevelParam)
    {
        BinderName = name ?? throw new ArgumentNullException(nameof(name));
        BinderType = type;
        Value = value;
        Body = body;
        NonDependent = nonDependent;
    }

    /// <summary>The bound name (irrelevant to typing).</summary>
    public Name BinderName { get; }

    /// <summary>The declared type.</summary>
    public Expr BinderType { get; }

    /// <summary>The value.</summary>
    public Expr Value { get; }

    /// <summary>The body, in which <c>#0</c> refers to the binding.</summary>
    public Expr Body { get; }

    /// <summary>Lean's <c>nonDep</c> flag: the body's type does not depend on the value.</summary>
    public bool NonDependent { get; }

    private protected override bool LocalEquals(Expr other, Stack<(Expr, Expr)> pending, bool strict)
    {
        var o = (LetExpr)other;
        if (NonDependent != o.NonDependent || (strict && !BinderName.Equals(o.BinderName)))
        {
            return false;
        }
        pending.Push((Body, o.Body));
        pending.Push((Value, o.Value));
        pending.Push((BinderType, o.BinderType));
        return true;
    }
}

/// <summary>A natural-number literal.</summary>
public sealed class NatLitExpr : Expr
{
    internal NatLitExpr(BigInteger value)
        : base(ExprKind.NatLit, Hashing.Mix(9, HashBig(value)), 0, false, false) => Value = value;

    /// <summary>The value (never negative).</summary>
    public BigInteger Value { get; }

    private static ulong HashBig(BigInteger value)
    {
        if (value.Sign < 0)
        {
            throw new ArgumentOutOfRangeException(nameof(value), value, "Natural-number literals cannot be negative.");
        }
        if (value <= ulong.MaxValue)
        {
            return (ulong)value;
        }
        ulong h = 0x77;
        foreach (byte b in value.ToByteArray())
        {
            h = Hashing.Mix(h, b);
        }
        return h;
    }

    private protected override bool LocalEquals(Expr other, Stack<(Expr, Expr)> pending, bool strict) =>
        Value == ((NatLitExpr)other).Value;
}

/// <summary>A string literal.</summary>
public sealed class StrLitExpr : Expr
{
    internal StrLitExpr(string value)
        : base(ExprKind.StrLit, Hashing.Mix(10, Hashing.String(value ?? throw new ArgumentNullException(nameof(value)))), 0, false, false) => Value = value;

    /// <summary>The value.</summary>
    public string Value { get; }

    private protected override bool LocalEquals(Expr other, Stack<(Expr, Expr)> pending, bool strict) =>
        string.Equals(Value, ((StrLitExpr)other).Value, StringComparison.Ordinal);
}

/// <summary>A metadata annotation; transparent to type checking.</summary>
public sealed class MDataExpr : Expr
{
    internal MDataExpr(KVMap data, Expr expr)
        : base(
            ExprKind.MData,
            Hashing.Mix(11, (expr ?? throw new ArgumentNullException(nameof(expr))).Hash64),
            expr.LooseBVarRange,
            expr.HasFVar,
            expr.HasLevelParam)
    {
        Data = data ?? throw new ArgumentNullException(nameof(data));
        Expr = expr;
    }

    /// <summary>The annotation.</summary>
    public KVMap Data { get; }

    /// <summary>The annotated expression.</summary>
    public Expr Expr { get; }

    private protected override bool LocalEquals(Expr other, Stack<(Expr, Expr)> pending, bool strict)
    {
        var o = (MDataExpr)other;
        if (!Data.Equals(o.Data))
        {
            return false;
        }
        pending.Push((Expr, o.Expr));
        return true;
    }
}

/// <summary>Projection of a structure field: <c>s.idx</c> for structure type <c>TypeName</c>.</summary>
public sealed class ProjExpr : Expr
{
    internal ProjExpr(Name typeName, int index, Expr structure)
        : base(
            ExprKind.Proj,
            Hashing.Mix(12, (typeName ?? throw new ArgumentNullException(nameof(typeName))).Hash64, (ulong)CheckIndex(index), (structure ?? throw new ArgumentNullException(nameof(structure))).Hash64),
            structure.LooseBVarRange,
            structure.HasFVar,
            structure.HasLevelParam)
    {
        TypeName = typeName;
        Index = index;
        Struct = structure;
    }

    /// <summary>The structure type's name.</summary>
    public Name TypeName { get; }

    /// <summary>The zero-based field index.</summary>
    public int Index { get; }

    /// <summary>The structure value being projected.</summary>
    public Expr Struct { get; }

    private static int CheckIndex(int index)
    {
        ArgumentOutOfRangeException.ThrowIfNegative(index);
        return index;
    }

    private protected override bool LocalEquals(Expr other, Stack<(Expr, Expr)> pending, bool strict)
    {
        var o = (ProjExpr)other;
        if (Index != o.Index || !TypeName.Equals(o.TypeName))
        {
            return false;
        }
        pending.Push((Struct, o.Struct));
        return true;
    }
}
