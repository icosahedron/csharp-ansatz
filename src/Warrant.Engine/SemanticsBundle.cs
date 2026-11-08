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
    /// Why declarations cannot be a bundle's, or null if they can (#26). The names alone are not enough: an axiom named
    /// <c>propext</c> could state <c>False</c>, and <c>propext</c>'s statement means what it should only if <c>Iff</c> and
    /// <c>Eq</c> are Lean's. So every axiom must be a standard one, and every declaration of a standard axiom, or of a type
    /// its statement mentions, must be exactly Lean 4.35.0's (<c>StandardAxioms.ndjson</c>, taken from the committed bundle).
    /// Other declarations are definitions, theorems and inductive types, which the kernel checks and which add no axioms.
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
                if (Standard.Value.TryGetValue(constant.Name.ToString(), out var expected) && !expected.Equals(declaration))
                {
                    return $"declares {constant.Name} differently from Lean 4.35.0.";
                }
            }
        }
        return null;
    }

    /// <summary>Lean's declarations of the standard axioms and of the types they mention, by each constant's name.</summary>
    private static readonly Lazy<Dictionary<string, Declaration>> Standard = new(() =>
    {
        using var stream = typeof(SemanticsBundle).Assembly.GetManifestResourceStream("Warrant.Engine.StandardAxioms.ndjson")
            ?? throw new InvalidOperationException("The StandardAxioms.ndjson resource is missing.");
        using var reader = new Lean4ExportReader(stream);
        var result = new Dictionary<string, Declaration>(StringComparer.Ordinal);
        foreach (var declaration in reader.ReadDeclarations())
        {
            foreach (var constant in declaration.Constants)
            {
                result.Add(constant.Name.ToString(), declaration);
            }
        }
        return result;
    });
}
