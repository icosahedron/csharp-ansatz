using System.Reflection;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Warrant.Frontend;
using Warrant.Kernel;
using Warrant.Vir;
using static Microsoft.CodeAnalysis.CSharp.SyntaxFactory;

namespace Warrant.Engine.Tests.Differential;

/// <summary>
/// Theorem statements against the CLR (docs/m4/07, "Theorems"): every M4 claim is a closed <c>bool</c> expression, so a
/// copy of the compilation in which each <c>[Theorem] static Proof M() =&gt; Prove.That(e);</c> becomes
/// <c>static bool M() =&gt; e;</c> computes it. The engine must report the theorem proved exactly when that is
/// <c>true</c>, and false (WRT0001) exactly when it is <c>false</c>. This checks the trusted statement translation
/// (<c>Spec.Implies</c> as <c>∀</c>, <c>&gt;</c> as a flipped <c>&lt;</c>, record <c>==</c> as <c>$eq</c>) as the
/// differential tests check function bodies.
/// </summary>
[Collection(DifferentialGroup.Name)]
public sealed class TheoremStatementTests(DifferentialFixture corpus)
{
    [Fact]
    public void EveryAcceptedTheoremIsProvedExactlyWhenItsClaimIsTrueOnTheClr()
    {
        var claims = Agree(corpus.Compilation, corpus.Extraction, corpus.Run);
        Assert.Equal(33, claims.Count);
        Assert.All(claims, c => Assert.True(c.Value));
    }

    [Fact]
    public void EveryRefutedTheoremIsFalseExactlyWhenItsClaimIsFalseOnTheClr()
    {
        var compilation = EngineCorpus.Compile("refuted");
        var extraction = EngineCorpus.Extract(compilation);
        var claims = Agree(compilation, extraction, Pipeline.Run(EngineCorpus.Inputs(extraction), corpus.Bundle, KernelLimits.Corpus));
        Assert.Equal(2, claims.Count);
        Assert.All(claims, c => Assert.False(c.Value));
    }

    [Fact]
    public void ImplicationClaimsAgreeForEveryCombinationOfPremiseAndConclusion()
    {
        var compilation = CompilationFactory.Create(
            [new SourceFile("Implications.cs", """
                using Warrant;

                public static class Implications
                {
                    [Verified] public static int Inc(int x) => x + 1;

                    [Theorem] static Proof TrueImpliesTrue() => Prove.That(Spec.Implies(Inc(1) == 2, Inc(2) == 3));
                    [Theorem] static Proof TrueImpliesFalse() => Prove.That(Spec.Implies(Inc(1) == 2, Inc(2) == 4));
                    [Theorem] static Proof FalseImpliesTrue() => Prove.That(Spec.Implies(Inc(1) == 5, Inc(2) == 3));
                    [Theorem] static Proof FalseImpliesFalse() => Prove.That(Spec.Implies(Inc(1) == 5, Inc(2) > 3));

                    [Theorem]
                    static Proof BlockBodied()
                    {
                        return Prove.That(Spec.Implies(Inc(int.MaxValue) < 0, Inc(int.MaxValue) == int.MinValue));
                    }

                    [Theorem]
                    static Proof BlockBodiedFalse()
                    {
                        return Prove.That(Spec.Implies(Inc(int.MaxValue) < 0, Inc(int.MaxValue) > 0));
                    }
                }
                """)],
            checkOverflow: false);
        var extraction = EngineCorpus.Extract(compilation);
        Assert.Empty(extraction.Diagnostics);
        var claims = Agree(compilation, extraction, Pipeline.Run(EngineCorpus.Inputs(extraction), corpus.Bundle, KernelLimits.Corpus));
        Assert.Equal(
            new Dictionary<string, bool>
            {
                ["M:Implications.TrueImpliesTrue"] = true,
                ["M:Implications.TrueImpliesFalse"] = false,
                ["M:Implications.FalseImpliesTrue"] = true,
                ["M:Implications.FalseImpliesFalse"] = true,
                ["M:Implications.BlockBodied"] = true,
                ["M:Implications.BlockBodiedFalse"] = false,
            },
            claims);
    }

    /// <summary>
    /// Computes every theorem's claim on the CLR and requires the engine's outcome to match it: proved when true, false
    /// (WRT0001) when false. Returns each claim's value by key.
    /// </summary>
    private static Dictionary<string, bool> Agree(CSharpCompilation compilation, Extraction.ExtractionResult extraction, EngineResult run)
    {
        var (claimsCompilation, methods) = ClaimsCompilation(compilation);
        var theorems = extraction.Units.Where(u => u.Unit.Kind == VirUnitKind.Theorem).Select(u => u.Key).ToList();
        Assert.Equal(theorems.Order(StringComparer.Ordinal), methods.Keys.Order(StringComparer.Ordinal));

        using var assembly = CorpusAssembly.Load(claimsCompilation);
        var claims = new Dictionary<string, bool>(StringComparer.Ordinal);
        foreach (var (key, (typeName, methodName)) in methods)
        {
            var method = assembly.Assembly.GetType(typeName, throwOnError: true)!
                .GetMethod(methodName, BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Static, Type.EmptyTypes)!;
            Assert.Equal(typeof(bool), method.ReturnType);
            var claim = (bool)CorpusAssembly.Invoke(method, [])!;
            var outcome = run.Find(key);
            Assert.True(
                claim ? outcome is ProvedOutcome : outcome is FalseOutcome,
                $"{key}: the claim is {(claim ? "true" : "false")} on the CLR, but the engine reports {Describe(outcome)}");
            claims.Add(key, claim);
        }
        return claims;
    }

    /// <summary>An outcome in a few words; records' own ToString would print whole certificates.</summary>
    private static string Describe(UnitOutcome? outcome) => outcome switch
    {
        null => "no outcome",
        ProvedOutcome p => $"proved by {p.By}",
        FalseOutcome => "false (WRT0001)",
        UndecidedOutcome u => $"undecided (WRT0006): {u.Reason}",
        FailedOutcome f => $"failed: {f.Reason}",
        SkippedOutcome s => $"skipped: {s.Reason}",
        _ => outcome.GetType().Name,
    };

    /// <summary>
    /// A copy of the compilation with every theorem's claim as a <c>bool</c> method, and each theorem's key mapped to its
    /// type's metadata name and its method's name.
    /// </summary>
    private static (CSharpCompilation Compilation, Dictionary<string, (string Type, string Method)> Methods) ClaimsCompilation(CSharpCompilation compilation)
    {
        var methods = new Dictionary<string, (string, string)>(StringComparer.Ordinal);
        var result = compilation;
        foreach (var tree in compilation.SyntaxTrees)
        {
            var model = compilation.GetSemanticModel(tree);
            var rewriter = new ClaimRewriter(model, methods);
            result = result.ReplaceSyntaxTree(tree, tree.WithRootAndOptions(rewriter.Visit(tree.GetRoot()), tree.Options));
        }
        return (result, methods);
    }

    /// <summary>Turns <c>[Theorem] static Proof M() =&gt; Prove.That(e);</c>, or its block-bodied form, into <c>static bool M() =&gt; e;</c>.</summary>
    private sealed class ClaimRewriter(SemanticModel model, Dictionary<string, (string, string)> methods) : CSharpSyntaxRewriter
    {
        public override SyntaxNode? VisitMethodDeclaration(MethodDeclarationSyntax node)
        {
            var symbol = model.GetDeclaredSymbol(node)!;
            if (!symbol.GetAttributes().Any(a => a.AttributeClass?.ToDisplayString() == "Warrant.TheoremAttribute"))
            {
                return base.VisitMethodDeclaration(node);
            }
            var body = node.ExpressionBody?.Expression
                ?? (node.Body is { Statements: [ReturnStatementSyntax { Expression: { } returned }] } ? returned : null);
            if (body is not InvocationExpressionSyntax { Expression: MemberAccessExpressionSyntax { Name.Identifier.Text: "That" }, ArgumentList.Arguments: [var claim] })
            {
                throw new InvalidOperationException($"{symbol} is not a Prove.That theorem: {node}");
            }
            var type = symbol.ContainingType;
            var typeName = type.ContainingNamespace.IsGlobalNamespace ? type.MetadataName : $"{type.ContainingNamespace.ToDisplayString()}.{type.MetadataName}";
            methods.Add(symbol.GetDocumentationCommentId()!, (typeName, symbol.Name));
            return node
                .WithAttributeLists(default)
                .WithReturnType(PredefinedType(Token(SyntaxKind.BoolKeyword)).WithTriviaFrom(node.ReturnType))
                .WithBody(null)
                .WithExpressionBody(ArrowExpressionClause(claim.Expression))
                .WithSemicolonToken(Token(SyntaxKind.SemicolonToken));
        }
    }
}
