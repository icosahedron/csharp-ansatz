using System.IO.Compression;
using Warrant.Cic;
using Warrant.Kernel;
using Warrant.Lean4Export;

namespace Warrant.Engine;

/// <summary>
/// The semantics bundle (docs/m4/01): Init's constants and the library, checked by the kernel declaration by declaration
/// and frozen, so every run admits into its own fork of it (KTD17).
/// </summary>
public sealed class SemanticsBundle
{
    /// <summary>The bundle's file name as the repository commits it (<c>tests/data/warrant-semantics.ndjson.gz</c>).</summary>
    public const string FileName = "warrant-semantics.ndjson.gz";

    /// <summary>The attribute sidecar made for the bundle, which ships beside it.</summary>
    public const string SidecarFileName = "warrant-attributes.ndjson.gz";

    /// <summary>Wraps a bundle that has already been checked and frozen.</summary>
    /// <param name="declarations">The bundle's declarations, in file order; NDJSON export writes them first.</param>
    /// <param name="env">The environment the declarations were checked into; must be frozen.</param>
    /// <param name="metadata">The file's metadata, whose Lean version export carries over; null if unknown.</param>
    /// <exception cref="ArgumentException"><paramref name="env"/> is not frozen.</exception>
    public SemanticsBundle(IReadOnlyList<Declaration> declarations, KernelEnvironment env, ExportMetadata? metadata = null)
    {
        ArgumentNullException.ThrowIfNull(declarations);
        ArgumentNullException.ThrowIfNull(env);
        if (!env.IsFrozen)
        {
            throw new ArgumentException("The bundle's environment must be frozen.", nameof(env));
        }
        Declarations = declarations;
        Env = env;
        Metadata = metadata;
    }

    /// <summary>The bundle's declarations, in file order.</summary>
    public IReadOnlyList<Declaration> Declarations { get; }

    /// <summary>The checked, frozen environment.</summary>
    public KernelEnvironment Env { get; }

    /// <summary>The metadata of the file the bundle was read from, or null.</summary>
    public ExportMetadata? Metadata { get; }

    /// <summary>
    /// The only axioms a bundle may declare: Lean's three standard ones (#26). The kernel admits any well-typed axiom, so
    /// a bundle with another one, such as <c>sorryAx</c> or <c>axiom bad : False</c>, would make every proof check.
    /// </summary>
    public static IReadOnlyList<string> StandardAxioms { get; } = ["propext", "Classical.choice", "Quot.sound"];

    /// <summary>
    /// Reads a bundle file (gzip or plain NDJSON), rejects it if it declares an axiom other than
    /// <see cref="StandardAxioms"/>, checks every declaration with <see cref="ExportChecker"/> into a new environment, and
    /// freezes it.
    /// </summary>
    /// <param name="path">The bundle file.</param>
    /// <returns>The checked bundle.</returns>
    /// <exception cref="InvalidDataException">The bundle declares another axiom, or the kernel rejects a declaration of it.</exception>
    /// <exception cref="Lean4ExportFormatException">The file is malformed.</exception>
    public static SemanticsBundle Load(string path)
    {
        var file = Lean4Export.Lean4Export.ReadFile(path);
        if (AxiomProblem(file.Declarations) is { } problem)
        {
            throw new InvalidDataException($"The semantics bundle {path} {problem}");
        }
        var env = new KernelEnvironment();
        var results = new ExportChecker(env).CheckAll(file.Declarations);
        if (results.FirstOrDefault(r => !r.Accepted) is { } rejected)
        {
            throw new InvalidDataException($"The semantics bundle {path} does not check: {rejected.Name}: {rejected.Error}");
        }
        env.Freeze();
        return new SemanticsBundle(file.Declarations, env, file.Metadata);
    }

    /// <summary>
    /// The constants the kernel computes with by name rather than by unfolding their definitions (<see cref="KernelNames"/>):
    /// <c>Nat</c> arithmetic on literals, string literals, <c>Bool</c> results, <c>Eq</c>, and the reduction hints. If a
    /// bundle defined one of them differently, the kernel's computed value and the definition would disagree, and that
    /// disagreement proves <c>False</c> without any axiom (#26).
    /// </summary>
    public static IReadOnlyList<Name> KernelReducedNames { get; } =
    [
        KernelNames.Nat, KernelNames.NatZero, KernelNames.NatSucc, KernelNames.NatAdd, KernelNames.NatSub, KernelNames.NatMul,
        KernelNames.NatPow, KernelNames.NatGcd, KernelNames.NatMod, KernelNames.NatDiv, KernelNames.NatBeq, KernelNames.NatBle,
        KernelNames.NatLand, KernelNames.NatLor, KernelNames.NatXor, KernelNames.NatShiftLeft, KernelNames.NatShiftRight,
        KernelNames.StringType, KernelNames.StringOfList, KernelNames.CharType, KernelNames.CharOfNat,
        KernelNames.ListNil, KernelNames.ListCons, KernelNames.Bool, KernelNames.BoolTrue, KernelNames.BoolFalse, KernelNames.Eq,
        KernelNames.EagerReduce, KernelNames.ReduceBool, KernelNames.ReduceNat,
        KernelNames.OptParam, KernelNames.AutoParam, KernelNames.OutParam, KernelNames.SemiOutParam,
    ];

    /// <summary>The file name of the pinned declarations, embedded in this assembly.</summary>
    public const string PinnedFileName = "PinnedDeclarations.ndjson.gz";

    /// <summary>
    /// Why declarations cannot be a bundle's, or null if they can (#26). Every axiom must be a standard one. A name alone
    /// fixes nothing: an axiom named <c>propext</c> could state <c>False</c>, and the kernel computes <c>Nat.add</c> on
    /// literals whatever the bundle defines it to be. So every declaration of a standard axiom or of a
    /// <see cref="KernelReducedNames"/> constant, and of every constant those mention, transitively, must be exactly Lean
    /// 4.35.0's: <see cref="PinnedFileName"/>, made from the committed bundle by <see cref="PinnedClosure"/>. A
    /// kernel-reduced name that Lean's bundle does not declare may not be declared at all. Every other declaration is a
    /// definition, theorem or inductive type the kernel checks, which adds no axiom and which the kernel does not compute
    /// with by name.
    /// </summary>
    /// <param name="declarations">The declarations, in file order.</param>
    /// <returns>The reason, as the end of a sentence, or null.</returns>
    public static string? AxiomProblem(IEnumerable<Declaration> declarations)
    {
        ArgumentNullException.ThrowIfNull(declarations);
        foreach (var declaration in declarations)
        {
            if (declaration is ConstantDeclaration { Constant: AxiomInfo axiom } && !StandardAxioms.Contains(axiom.Name.ToString(), StringComparer.Ordinal))
            {
                return $"declares the axiom {axiom.Name}, which is not one of {string.Join(", ", StandardAxioms)}.";
            }
            foreach (var constant in declaration.Constants)
            {
                if (Pinned.Value.TryGetValue(constant.Name.ToString(), out var expected))
                {
                    if (!expected.Equals(declaration))
                    {
                        return $"declares {constant.Name} differently from Lean 4.35.0.";
                    }
                }
                else if (KernelReducedNames.Contains(constant.Name))
                {
                    return $"declares {constant.Name}, which the kernel computes with by name and Lean 4.35.0's bundle does not declare.";
                }
            }
        }
        return null;
    }

    /// <summary>
    /// The declarations that fix what the standard axioms and the <see cref="KernelReducedNames"/> constants mean: those
    /// that declare them and, transitively, every declaration a constant mentions in its type, value, proof or recursor
    /// rules, a projection's structure, and <c>Nat</c> or the string-literal constants for a literal. In file order.
    /// <c>scripts/pin-kernel-declarations.cs</c> writes this for the committed bundle to <see cref="PinnedFileName"/>.
    /// </summary>
    /// <param name="declarations">A bundle's declarations, in file order.</param>
    /// <returns>The closure, in file order.</returns>
    public static IReadOnlyList<Declaration> PinnedClosure(IReadOnlyList<Declaration> declarations)
    {
        ArgumentNullException.ThrowIfNull(declarations);
        var owner = new Dictionary<Name, Declaration>();
        foreach (var declaration in declarations)
        {
            foreach (var constant in declaration.Constants)
            {
                owner[constant.Name] = declaration;
            }
        }
        Name[] stringLiteral = [KernelNames.StringType, KernelNames.StringOfList, KernelNames.CharType, KernelNames.CharOfNat, KernelNames.ListNil, KernelNames.ListCons];
        var picked = new HashSet<Declaration>(ReferenceEqualityComparer.Instance);
        var seen = new HashSet<Expr>(ReferenceEqualityComparer.Instance);
        var pending = new Stack<Name>(StandardAxioms.Select(Name.Parse).Concat(KernelReducedNames));
        var exprs = new Stack<Expr>();
        while (pending.Count > 0)
        {
            if (!owner.TryGetValue(pending.Pop(), out var declaration) || !picked.Add(declaration))
            {
                continue;
            }
            foreach (var constant in declaration.Constants)
            {
                exprs.Push(constant.Type);
                switch (constant)
                {
                    case DefinitionInfo d:
                        exprs.Push(d.DefinitionValue);
                        break;
                    case TheoremInfo t:
                        exprs.Push(t.Proof);
                        break;
                    case OpaqueInfo o:
                        exprs.Push(o.OpaqueValue);
                        break;
                    case RecursorInfo r:
                        foreach (var rule in r.Rules)
                        {
                            exprs.Push(rule.Rhs);
                        }
                        break;
                }
            }
            while (exprs.Count > 0)
            {
                var e = exprs.Pop();
                if (!seen.Add(e))
                {
                    continue;
                }
                switch (e)
                {
                    case ConstExpr c:
                        pending.Push(c.Name);
                        break;
                    case AppExpr a:
                        exprs.Push(a.Fn);
                        exprs.Push(a.Arg);
                        break;
                    case BindingExpr b:
                        exprs.Push(b.BinderType);
                        exprs.Push(b.Body);
                        break;
                    case LetExpr l:
                        exprs.Push(l.BinderType);
                        exprs.Push(l.Value);
                        exprs.Push(l.Body);
                        break;
                    case MDataExpr m:
                        exprs.Push(m.Expr);
                        break;
                    case ProjExpr p:
                        pending.Push(p.TypeName);
                        exprs.Push(p.Struct);
                        break;
                    case NatLitExpr:
                        pending.Push(KernelNames.Nat);
                        break;
                    case StrLitExpr:
                        foreach (var name in stringLiteral)
                        {
                            pending.Push(name);
                        }
                        break;
                }
            }
        }
        return [.. declarations.Where(picked.Contains)];
    }

    /// <summary>Reads the embedded <see cref="PinnedFileName"/>.</summary>
    /// <returns>Its declarations, in file order.</returns>
    public static IReadOnlyList<Declaration> PinnedDeclarations()
    {
        using var stream = typeof(SemanticsBundle).Assembly.GetManifestResourceStream("Warrant.Engine." + PinnedFileName)
            ?? throw new InvalidOperationException($"The {PinnedFileName} resource is missing.");
        using var reader = new Lean4ExportReader(new GZipStream(stream, CompressionMode.Decompress));
        return [.. reader.ReadDeclarations()];
    }

    /// <summary>Lean 4.35.0's <see cref="PinnedClosure"/>, by each constant's name.</summary>
    private static readonly Lazy<Dictionary<string, Declaration>> Pinned = new(() =>
    {
        var result = new Dictionary<string, Declaration>(StringComparer.Ordinal);
        foreach (var declaration in PinnedDeclarations())
        {
            foreach (var constant in declaration.Constants)
            {
                result.Add(constant.Name.ToString(), declaration);
            }
        }
        return result;
    });
}
