using Microsoft.CodeAnalysis;

namespace Warrant.Extraction;

/// <summary>
/// The compilation's <c>[ContractFor(typeof(I))]</c> classes (plan M6 KTD9, KTD10): which class states the contract of each
/// interface, and what is wrong with each class that has not the contract shape. Contract classes are found only in the
/// compilation of the verified method, so a full extraction and the analyzer, which checks one member at a time, read the
/// same index; the interface itself may come from any assembly. Read-only once built.
/// </summary>
internal sealed class ContractIndex
{
    private const string ContractForAttribute = "Warrant.ContractForAttribute";

    private readonly Dictionary<string, Rejection> _problems;
    private readonly Dictionary<string, INamedTypeSymbol> _byInterface;

    private ContractIndex(List<INamedTypeSymbol> classes, Dictionary<string, Rejection> problems, Dictionary<string, INamedTypeSymbol> byInterface)
    {
        Classes = classes;
        _problems = problems;
        _byInterface = byInterface;
    }

    /// <summary>The <c>[ContractFor]</c> classes, by key.</summary>
    public IReadOnlyList<INamedTypeSymbol> Classes { get; }

    /// <summary>Whether a symbol is a type marked <c>[ContractFor]</c>.</summary>
    public static bool IsContractClass(ISymbol symbol) => symbol is INamedTypeSymbol && Symbols.Has(symbol, ContractForAttribute);

    /// <summary>Why a <c>[ContractFor]</c> class has not the contract shape, or null when it has it.</summary>
    /// <param name="classKey">The class's key.</param>
    /// <returns>The rejection, keyed by the class.</returns>
    public Rejection? ProblemOf(string classKey) => _problems.TryGetValue(classKey, out var r) ? r : null;

    /// <summary>
    /// The contract class of an interface, the first in source order that names it, whether or not it has the contract
    /// shape; null when the compilation has none.
    /// </summary>
    /// <param name="interfaceKey">The interface's key.</param>
    /// <returns>The class.</returns>
    public INamedTypeSymbol? ClassFor(string interfaceKey) => _byInterface.TryGetValue(interfaceKey, out var c) ? c : null;

    /// <summary>
    /// The contract classes with the contract shape whose interface has <paramref name="member"/>, itself or through an
    /// interface it inherits; two of them would give the member's one contract unit two contracts.
    /// </summary>
    /// <param name="member">An interface member.</param>
    /// <returns>The classes, by key.</returns>
    public List<INamedTypeSymbol> ClassesCovering(ISymbol member) =>
        Classes
            .Where(c => !_problems.ContainsKey(Symbols.Key(c)) && Interface(c) is { } i
                && (SymbolEqualityComparer.Default.Equals(i, member.ContainingType) || i.AllInterfaces.Contains(member.ContainingType, SymbolEqualityComparer.Default)))
            .ToList();

    /// <summary>The type a <c>[ContractFor]</c> class names, or null when it names none.</summary>
    public static INamedTypeSymbol? Interface(INamedTypeSymbol contractClass)
    {
        var attribute = contractClass.GetAttributes().First(a => a.AttributeClass?.ToDisplayString() == ContractForAttribute);
        return attribute.ConstructorArguments.Length == 1 ? attribute.ConstructorArguments[0].Value as INamedTypeSymbol : null;
    }

    /// <summary>Indexes the <c>[ContractFor]</c> classes of the given types and checks each one's shape.</summary>
    /// <param name="compilation">The compilation the types are from.</param>
    /// <param name="types">The compilation's source types.</param>
    /// <param name="cancellationToken">Cancels the build.</param>
    /// <returns>The index.</returns>
    public static ContractIndex Build(Compilation compilation, IEnumerable<INamedTypeSymbol> types, CancellationToken cancellationToken)
    {
        var classes = types.Where(IsContractClass).OrderBy(Symbols.Key, StringComparer.Ordinal).ToList();
        var problems = new Dictionary<string, Rejection>(StringComparer.Ordinal);
        var byInterface = new Dictionary<string, INamedTypeSymbol>(StringComparer.Ordinal);

        // In source order, so the first class for an interface is the one that counts and a second one names it.
        var ordered = classes.ToList();
        ordered.Sort(Symbols.CompareByLocation);
        foreach (var type in ordered)
        {
            cancellationToken.ThrowIfCancellationRequested();
            var key = Symbols.Key(type);
            if (TypeChecks.ContractShape(compilation, type, cancellationToken) is { } problem)
            {
                problems.Add(key, problem);
            }
            if (Interface(type) is not { TypeKind: TypeKind.Interface } named)
            {
                continue;
            }
            var interfaceKey = Symbols.Key(named);
            if (byInterface.TryGetValue(interfaceKey, out var earlier))
            {
                // A shape problem is reported first; a well-shaped twin is the second class.
                if (!problems.ContainsKey(key))
                {
                    problems.Add(key, new Rejection(
                        DiagnosticIds.Unsupported,
                        "second contract class for an interface",
                        Symbols.FirstLocation(type),
                        $"{Symbols.Display(type)}: {Symbols.Display(named)} already has a contract class, {Symbols.Display(earlier)}; an interface takes one, so the contract each member is assumed to keep is unambiguous."));
                }
                continue;
            }
            byInterface.Add(interfaceKey, type);
        }
        return new ContractIndex(classes, problems, byInterface);
    }
}
