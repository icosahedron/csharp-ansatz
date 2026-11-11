using System.Globalization;
using Warrant.Cic;
using Warrant.Kernel;
using Warrant.Semantics;
using Warrant.Vir;

namespace Warrant.Engine.Tests.Differential;

/// <summary>
/// .NET values as CIC terms (docs/m4/07): an <c>int</c>, <c>long</c> or <c>bool</c> is its literal; an open enum is the
/// literal of its underlying value, typed at the enum by the theorem; a closed enum or closed-class value is the member
/// constant (a closed-class instance found by reference identity among the static instances); a record is <c>$mk</c>
/// applied to its fields; a nullable value (M6) is <c>Option.none</c> or <c>Option.some</c> of its value.
/// </summary>
internal sealed class Values(CorpusAssembly assembly, IReadOnlyDictionary<string, VirDefinition> definitions)
{
    public CorpusAssembly Assembly { get; } = assembly;

    public VirDefinition Definition(string typeKey) => definitions[typeKey];

    /// <summary>The CIC type of a VIR type.</summary>
    public static Expr CicType(VirType type) => type switch
    {
        PrimitiveType p => Literals.Type(p.Kind),
        RefType r => Expr.Const(LeanNames.ForKey(r.Key)),
        NullableType n => Expr.App(Option, CicType(n.Value)),
        _ => throw new ArgumentOutOfRangeException(nameof(type), type, null),
    };

    /// <summary><c>Option.{0}</c>: a nullable value <c>T?</c> is <c>Option T</c> (M6 KTD5).</summary>
    private static readonly Expr Option = Expr.Const(Name.Parse("Option"), Level.Zero);

    private static readonly Name OptionNone = Name.Parse("Option.none");

    private static readonly Name OptionSome = Name.Parse("Option.some");

    /// <summary>
    /// The term for a .NET value of a VIR type; for a nullable type, <c>@Option.none T</c> for null and
    /// <c>@Option.some T v</c> otherwise.
    /// </summary>
    /// <exception cref="ModelGapException">The value has no counterpart in the model: null of a non-nullable type, or an unnamed closed value.</exception>
    public Expr Term(VirType type, object? value)
    {
        if (type is NullableType nullable)
        {
            var valueType = CicType(nullable.Value);
            return value is null
                ? Expr.App(Expr.Const(OptionNone, Level.Zero), valueType)
                : Expr.App(Expr.Const(OptionSome, Level.Zero), valueType, Term(nullable.Value, value));
        }
        if (value is null)
        {
            throw new ModelGapException($"null has no counterpart of type {Describe(type)} in the model");
        }
        switch (type)
        {
            case PrimitiveType { Kind: VirPrimitive.Int32 }:
                return Literals.Int32((int)value);
            case PrimitiveType { Kind: VirPrimitive.Int64 }:
                return Literals.Int64((long)value);
            case PrimitiveType { Kind: VirPrimitive.Bool }:
                return Literals.Bool((bool)value);
        }
        var key = ((RefType)type).Key;
        switch (definitions[key])
        {
            case EnumDefinition e:
                return Literals.Of(((PrimitiveType)e.Underlying).Kind, Convert.ToInt64(value, CultureInfo.InvariantCulture));
            case ClosedDefinition c:
                return Expr.Const(LeanNames.Member(key, ClosedMember(key, c, value)));
            case RecordDefinition r:
                {
                    var clr = Assembly.TypeOf(key);
                    var fields = r.Fields.Select(f => Term(f.Type, clr.GetProperty(f.Name)!.GetValue(value))).ToArray();
                    return Expr.App(Expr.Const(LeanNames.Constructor(key)), fields);
                }
            default:
                throw new InvalidOperationException($"unknown definition for {key}");
        }
    }

    /// <summary>A .NET value as C# would write it, for messages.</summary>
    public string Display(VirType type, object? value)
    {
        if (value is null)
        {
            return "null";
        }
        switch (type)
        {
            case PrimitiveType { Kind: VirPrimitive.Bool }:
                return (bool)value ? "true" : "false";
            case PrimitiveType:
                return Convert.ToString(value, CultureInfo.InvariantCulture)!;
            case NullableType n:
                return Display(n.Value, value);
        }
        var key = ((RefType)type).Key;
        var name = key[(key.LastIndexOf('.') + 1)..];
        switch (definitions[key])
        {
            case EnumDefinition e:
                {
                    var v = Convert.ToInt64(value, CultureInfo.InvariantCulture);
                    return e.Members.FirstOrDefault(m => m.Value == v) is { } member
                        ? $"{name}.{member.Name}"
                        : $"({name}){v.ToString(CultureInfo.InvariantCulture)}";
                }
            case ClosedDefinition c:
                try
                {
                    return $"{name}.{ClosedMember(key, c, value)}";
                }
                catch (ModelGapException)
                {
                    return $"({name}){value}";
                }
            case RecordDefinition r:
                {
                    var clr = Assembly.TypeOf(key);
                    return $"new {name}({string.Join(", ", r.Fields.Select(f => Display(f.Type, clr.GetProperty(f.Name)!.GetValue(value))))})";
                }
            default:
                throw new InvalidOperationException($"unknown definition for {key}");
        }
    }

    /// <summary>
    /// The model's value of <paramref name="term"/>, for messages only (docs/m4/07): integers and Booleans through the
    /// engine's read-back, records field by field through their projections, and closed values as the constructor the term
    /// reduces to. Must run on a kernel thread.
    /// </summary>
    public string ReadBackDisplay(KernelEnvironment env, VirType type, Expr term, KernelLimits limits)
    {
        if (type is PrimitiveType p)
        {
            return ReadBack.Value(env, term, Literals.Type(p.Kind), limits).ToString()!;
        }
        if (type is NullableType nullable)
        {
            try
            {
                var whnf = new TypeChecker(env, limits: limits).Whnf(term);
                return whnf.GetAppFn() is ConstExpr { Name: var ctor } && ctor == OptionNone
                    ? "null"
                    : whnf.GetAppFn() is ConstExpr { Name: var some } && some == OptionSome
                        ? ReadBackDisplay(env, nullable.Value, whnf.GetAppArgs()[1], limits)
                        : "unknown";
            }
            catch (KernelException)
            {
                return "unknown";
            }
        }
        var key = ((RefType)type).Key;
        var name = key[(key.LastIndexOf('.') + 1)..];
        switch (definitions[key])
        {
            case EnumDefinition e:
                {
                    var value = ReadBack.Value(env, term, CicType(type), limits);
                    long? v = value switch { Int32Value i => i.Value, Int64Value l => l.Value, _ => null };
                    return v is { } n && e.Members.FirstOrDefault(m => m.Value == n) is { } member
                        ? $"{name}.{member.Name}"
                        : $"({name}){value}";
                }
            case ClosedDefinition:
                try
                {
                    return new TypeChecker(env, limits: limits).Whnf(term) is ConstExpr { Name: var ctor }
                        ? $"{name}.{ctor.StringComponent}"
                        : "unknown";
                }
                catch (KernelException)
                {
                    return "unknown";
                }
            case RecordDefinition r:
                {
                    var record = LeanNames.ForKey(key);
                    var fields = r.Fields.Select((f, i) => ReadBackDisplay(env, f.Type, Expr.Proj(record, i, term), limits));
                    return $"new {name}({string.Join(", ", fields)})";
                }
            default:
                throw new InvalidOperationException($"unknown definition for {key}");
        }
    }

    private string ClosedMember(string key, ClosedDefinition closed, object value)
    {
        var clr = Assembly.TypeOf(key);
        if (clr.IsEnum)
        {
            var v = Convert.ToInt64(value, CultureInfo.InvariantCulture);
            return closed.Members.FirstOrDefault(m => m.Value == v)?.Name
                ?? throw new ModelGapException($"{v} names no member of the closed enum {key}");
        }
        return closed.Members.FirstOrDefault(m => ReferenceEquals(CorpusAssembly.ReadStatic(clr, m.Name), value))?.Name
            ?? throw new ModelGapException($"{value} is not a static instance of the closed class {key}");
    }

    private static string Describe(VirType type) => type is RefType r ? r.Key : type.ToString();
}

/// <summary>A .NET value the model has no counterpart for.</summary>
internal sealed class ModelGapException : Exception
{
    public ModelGapException()
    {
    }

    public ModelGapException(string message)
        : base(message)
    {
    }

    public ModelGapException(string message, Exception innerException)
        : base(message, innerException)
    {
    }
}
