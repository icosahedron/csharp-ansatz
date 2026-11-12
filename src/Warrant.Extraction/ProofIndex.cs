using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Operations;

namespace Warrant.Extraction;

/// <summary>
/// The compilation's <c>[ProofFor(nameof(M))]</c> methods (plan M6 KTD16, #179): which script each <c>[Verified]</c>
/// member's contract obligation takes, and what is wrong with each one that supplies none. A <c>[ProofFor]</c> method is a
/// static, parameterless method in <c>M</c>'s class whose body is <c>Prove.Contract().By(...)</c>; it must name exactly
/// one <c>[Verified]</c> member, and be the only <c>[ProofFor]</c> for it. Built once per compilation from every source
/// type, so a full extraction and the analyzer, which checks one member at a time, read the same index. Read-only once built.
/// </summary>
internal sealed class ProofIndex
{
    private const string ProofForAttribute = "Warrant.ProofForAttribute";

    private readonly Dictionary<string, Rejection> _problems;
    private readonly Dictionary<string, IInvocationOperation> _scripts;

    private ProofIndex(List<IMethodSymbol> methods, Dictionary<string, Rejection> problems, Dictionary<string, IInvocationOperation> scripts)
    {
        Methods = methods;
        _problems = problems;
        _scripts = scripts;
    }

    /// <summary>The <c>[ProofFor]</c> methods, by key.</summary>
    public IReadOnlyList<IMethodSymbol> Methods { get; }

    /// <summary>Whether a symbol is a method marked <c>[ProofFor]</c>.</summary>
    public static bool IsProofFor(ISymbol symbol) => symbol is IMethodSymbol && Symbols.Has(symbol, ProofForAttribute);

    /// <summary>Why a <c>[ProofFor]</c> method supplies no script, or null when it supplies one.</summary>
    /// <param name="proofKey">The <c>[ProofFor]</c> method's key.</param>
    /// <returns>The rejection, keyed by the <c>[ProofFor]</c> method.</returns>
    public Rejection? ProblemOf(string proofKey) => _problems.TryGetValue(proofKey, out var r) ? r : null;

    /// <summary>The <c>.By(...)</c> call whose script proves a member's contract obligation, or null when it has none.</summary>
    /// <param name="memberKey">The <c>[Verified]</c> member's key.</param>
    /// <returns>The call.</returns>
    public IInvocationOperation? ScriptFor(string memberKey) => _scripts.TryGetValue(memberKey, out var by) ? by : null;

    /// <summary>Indexes the <c>[ProofFor]</c> methods of the given types.</summary>
    /// <param name="compilation">The compilation the types are from.</param>
    /// <param name="types">The compilation's source types.</param>
    /// <param name="cancellationToken">Cancels the build.</param>
    /// <returns>The index.</returns>
    public static ProofIndex Build(Compilation compilation, IEnumerable<INamedTypeSymbol> types, CancellationToken cancellationToken)
    {
        var methods = types
            .SelectMany(t => t.GetMembers())
            .Where(IsProofFor)
            .Cast<IMethodSymbol>()
            .OrderBy(Symbols.Key, StringComparer.Ordinal)
            .ToList();
        var problems = new Dictionary<string, Rejection>(StringComparer.Ordinal);
        var scripts = new Dictionary<string, IInvocationOperation>(StringComparer.Ordinal);

        // The methods that name one verified member, in source order, so the first for a member is the one that counts.
        var targeted = new List<(IMethodSymbol Proof, ISymbol Target)>();
        foreach (var proof in methods)
        {
            cancellationToken.ThrowIfCancellationRequested();
            var (target, problem) = Target(proof);
            if (problem is not null)
            {
                problems.Add(Symbols.Key(proof), problem);
            }
            else
            {
                targeted.Add((proof, target!));
            }
        }
        targeted.Sort((a, b) => Symbols.CompareByLocation(a.Proof, b.Proof));
        var first = new Dictionary<string, IMethodSymbol>(StringComparer.Ordinal);
        foreach (var (proof, target) in targeted)
        {
            var key = Symbols.Key(proof);
            var targetKey = Symbols.Key(target);
            if (first.TryGetValue(targetKey, out var earlier))
            {
                problems.Add(key, new Rejection(
                    DiagnosticIds.Unsupported,
                    "second [ProofFor] for a method",
                    Symbols.FirstLocation(proof),
                    $"{Symbols.Display(proof)}: {Symbols.Display(target)} already has a [ProofFor] method, {Symbols.Display(earlier)}; a member's contract takes one script."));
                continue;
            }
            first.Add(targetKey, proof);
            var (by, shape) = Script(compilation, proof, cancellationToken);
            if (shape is not null)
            {
                problems.Add(key, shape);
            }
            else
            {
                scripts.Add(targetKey, by!);
            }
        }
        return new ProofIndex(methods, problems, scripts);
    }

    /// <summary>The member a <c>[ProofFor]</c> method names: one <c>[Verified]</c> member of its own class.</summary>
    private static (ISymbol? Target, Rejection? Problem) Target(IMethodSymbol proof)
    {
        var attribute = proof.GetAttributes().First(a => a.AttributeClass?.ToDisplayString() == ProofForAttribute);
        var at = attribute.ApplicationSyntaxReference?.GetSyntax().GetLocation() ?? Symbols.FirstLocation(proof);
        var name = attribute.ConstructorArguments.Length == 1 ? attribute.ConstructorArguments[0].Value as string : null;
        var type = proof.ContainingType;
        var members = name is null
            ? new List<ISymbol>()
            : type.GetMembers(name)
                .Where(m => m is IMethodSymbol { MethodKind: MethodKind.Ordinary } or IPropertySymbol)
                .ToList();
        if (members.Count == 0)
        {
            return (null, new Rejection(
                DiagnosticIds.Unsupported,
                "[ProofFor] naming no method",
                at,
                $"{Symbols.Display(proof)}: [ProofFor] names {name ?? "nothing"}, which is not a method of {Symbols.Display(type)}; write [ProofFor(nameof(M))] in M's class."));
        }
        if (members.Count > 1)
        {
            return (null, new Rejection(
                DiagnosticIds.Unsupported,
                "[ProofFor] of an overloaded method",
                at,
                $"{Symbols.Display(proof)}: {Symbols.Display(type)} has {members.Count} members named {name}, which nameof cannot tell apart; a [ProofFor] method proves a member without overloads."));
        }
        var target = members[0];
        if (!Symbols.IsVerified(target))
        {
            return (null, new Rejection(
                DiagnosticIds.Unsupported,
                "[ProofFor] of a member that is not verified",
                at,
                $"{Symbols.Display(proof)}: {Symbols.Display(target)} is not [Verified], so it has no contract obligation to prove."));
        }
        return (target, null);
    }

    /// <summary>The <c>.By(...)</c> of a static, parameterless method whose body is <c>Prove.Contract().By(...)</c>.</summary>
    private static (IInvocationOperation? By, Rejection? Problem) Script(Compilation compilation, IMethodSymbol proof, CancellationToken cancellationToken)
    {
        if (!proof.IsStatic || proof.Parameters.Length > 0 || proof.IsGenericMethod)
        {
            return (null, new Rejection(
                DiagnosticIds.Unsupported,
                "[ProofFor] method that is not static and parameterless",
                Symbols.FirstLocation(proof),
                $"{Symbols.Display(proof)}: a [ProofFor] method is static, takes no parameters and is not generic; it is never called."));
        }
        var syntax = proof.DeclaringSyntaxReferences.Select(r => r.GetSyntax(cancellationToken)).OfType<MethodDeclarationSyntax>().FirstOrDefault();
        var body = syntax is null ? null : compilation.GetSemanticModel(syntax.SyntaxTree).GetOperation(syntax, cancellationToken) as IMethodBodyOperation;
        var block = body?.ExpressionBody ?? body?.BlockBody;
        if (block is { Operations.Length: 1 } && block.Operations[0] is IReturnOperation { ReturnedValue: IInvocationOperation by }
            && Symbols.IsNamed(by.TargetMethod, "Warrant.Proof", "By")
            && by.Instance is IInvocationOperation contract && Symbols.IsNamed(contract.TargetMethod, "Warrant.Prove", "Contract"))
        {
            return (by, null);
        }
        return (null, new Rejection(
            DiagnosticIds.Unsupported,
            "[ProofFor] body that is not Prove.Contract().By(...)",
            (block?.Syntax ?? (SyntaxNode?)syntax)?.GetLocation() ?? Symbols.FirstLocation(proof),
            $"{Symbols.Display(proof)}: the body of a [ProofFor] method is Prove.Contract().By(...), the script that proves the contract."));
    }
}
