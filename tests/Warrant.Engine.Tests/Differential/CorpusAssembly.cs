using System.Reflection;
using System.Runtime.Loader;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Warrant.Frontend;
using Warrant.Vir;

namespace Warrant.Engine.Tests.Differential;

/// <summary>
/// A compilation emitted to memory and loaded into a collectible <see cref="AssemblyLoadContext"/> (docs/m4/07, KTD14).
/// Differential tests emit the same <see cref="CSharpCompilation"/> extraction read, so the two sides cannot drift. The
/// context resolves <c>Warrant</c> to the package image the compilation referenced, embedded in <c>Warrant.Frontend</c>.
/// </summary>
internal sealed class CorpusAssembly : IDisposable
{
    private const BindingFlags AnyStatic = BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Static;

    private readonly Context _context;

    private CorpusAssembly(Context context, Assembly assembly)
    {
        _context = context;
        Assembly = assembly;
    }

    public Assembly Assembly { get; }

    /// <summary>Emits <paramref name="compilation"/>, which must emit without errors, and loads it.</summary>
    public static CorpusAssembly Load(CSharpCompilation compilation)
    {
        using var image = new MemoryStream();
        var emitted = compilation.Emit(image);
        Assert.True(
            emitted.Success,
            string.Join("\n", emitted.Diagnostics.Where(d => d.Severity == DiagnosticSeverity.Error).Select(d => d.ToString())));
        image.Position = 0;
        var context = new Context();
        return new CorpusAssembly(context, context.LoadFromStream(image));
    }

    /// <summary>The CLR type of a type unit, by its documentation-comment ID (<c>T:Claims.Payment</c>).</summary>
    public Type TypeOf(string typeKey) =>
        Assembly.GetType(typeKey[2..], throwOnError: true)!;

    /// <summary>The CLR type of a VIR type.</summary>
    public Type TypeOf(VirType type) => type switch
    {
        PrimitiveType { Kind: VirPrimitive.Int32 } => typeof(int),
        PrimitiveType { Kind: VirPrimitive.Int64 } => typeof(long),
        PrimitiveType { Kind: VirPrimitive.Bool } => typeof(bool),
        PrimitiveType { Kind: VirPrimitive.Decimal } => typeof(decimal),
        RefType r => TypeOf(r.Key),
        // int? is Nullable<int>; a nullable reference is the reference type itself (M6 KTD5).
        NullableType { Value: PrimitiveType } n => typeof(Nullable<>).MakeGenericType(TypeOf(n.Value)),
        NullableType n => TypeOf(n.Value),
        OpaqueType { Key: "T:System.Threading.CancellationToken" } => typeof(CancellationToken),
        _ => throw new ArgumentOutOfRangeException(nameof(type), type, null),
    };

    /// <summary>
    /// The method a function unit was extracted from: a static method, an instance method or a property getter. For an
    /// instance member the receiver is the first argument (as on the model side).
    /// </summary>
    public MethodInfo MethodOf(VirUnit unit)
    {
        var body = unit.Key[2..];
        var paren = body.IndexOf('(', StringComparison.Ordinal);
        var path = paren < 0 ? body : body[..paren];
        var dot = path.LastIndexOf('.');
        var type = Assembly.GetType(path[..dot], throwOnError: true)!;
        var member = path[(dot + 1)..];
        const BindingFlags any = AnyStatic | BindingFlags.Instance;
        if (unit.Key.StartsWith("P:", StringComparison.Ordinal))
        {
            return type.GetProperty(member, any)?.GetMethod ?? throw new InvalidOperationException($"no getter for {unit.Key}");
        }
        var parameters = (unit.Params ?? VirList<VirParam>.Empty).Select(p => TypeOf(p.Type)).ToArray();
        return type.GetMethod(member, any, parameters) ?? throw new InvalidOperationException($"no method for {unit.Key}");
    }

    /// <summary>Calls a method; for an instance method the first argument is the receiver. Exceptions are not wrapped.</summary>
    public static object? Invoke(MethodInfo method, IReadOnlyList<object?> args)
    {
        var (target, rest) = method.IsStatic ? (null, args.ToArray()) : (args[0], args.Skip(1).ToArray());
        return method.Invoke(target, BindingFlags.DoNotWrapExceptions, binder: null, rest, culture: null);
    }

    /// <summary>
    /// Calls a method on a receiver (null for a static one) and, when it returns a <c>Task</c>, <c>Task&lt;T&gt;</c>,
    /// <c>ValueTask</c> or <c>ValueTask&lt;T&gt;</c>, waits for it with <c>GetAwaiter().GetResult()</c> (plan M6 U22): the
    /// awaited value, null for a non-generic task, and the task's own exception rather than an aggregate. Exceptions are
    /// not wrapped.
    /// </summary>
    public static object? InvokeAndAwait(MethodInfo method, object? target, IReadOnlyList<object?> args)
    {
        var result = method.Invoke(target, BindingFlags.DoNotWrapExceptions, binder: null, args.ToArray(), culture: null);
        if (!IsTask(method.ReturnType))
        {
            return result;
        }
        var awaiter = method.ReturnType.GetMethod("GetAwaiter", Type.EmptyTypes)!.Invoke(result, BindingFlags.DoNotWrapExceptions, binder: null, [], culture: null)!;
        return awaiter.GetType().GetMethod("GetResult", Type.EmptyTypes)!.Invoke(awaiter, BindingFlags.DoNotWrapExceptions, binder: null, [], culture: null);
    }

    /// <summary>Whether a type is <c>Task</c>, <c>Task&lt;T&gt;</c>, <c>ValueTask</c> or <c>ValueTask&lt;T&gt;</c>.</summary>
    public static bool IsTask(Type type) =>
        type == typeof(Task) || type == typeof(ValueTask)
        || (type.IsGenericType && (type.GetGenericTypeDefinition() == typeof(Task<>) || type.GetGenericTypeDefinition() == typeof(ValueTask<>)));

    /// <summary>A static instance of a closed class, read through its property or field.</summary>
    public static object? ReadStatic(Type type, string member) =>
        type.GetProperty(member, AnyStatic) is { } property ? property.GetValue(null) : type.GetField(member, AnyStatic)!.GetValue(null);

    public void Dispose() => _context.Unload();

    private sealed class Context : AssemblyLoadContext
    {
        private readonly Assembly _warrant;

        public Context()
            : base("Warrant differential tests", isCollectible: true)
        {
            using var image = typeof(CompilationFactory).Assembly.GetManifestResourceStream("Warrant.dll")
                ?? throw new InvalidOperationException("Warrant.Frontend has no embedded Warrant.dll.");
            _warrant = LoadFromStream(image);
        }

        protected override Assembly? Load(AssemblyName assemblyName) =>
            string.Equals(assemblyName.Name, "Warrant", StringComparison.OrdinalIgnoreCase) ? _warrant : null;
    }
}
