using System.Reflection;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Warrant.Cic;
using Warrant.Engine.Reports;
using Warrant.Frontend;
using Warrant.Kernel;
using Warrant.Semantics;
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
    /// A theorem with parameters states its claim for all of them (M5a KTD17): its statement is
    /// <c>∀ (x₁ : T₁) … (xₙ : Tₙ), P</c>. Instantiating the binders with each combination of the parameters' boundary
    /// values gives a closed proposition, which the kernel decides with a <c>Decidable</c> instance built here from the
    /// proposition's shape (independently of the translator's table); the result must be the C# claim's value on the
    /// CLR at the same arguments. With no script, the engine reports each such theorem not proved with its goal (U11), with
    /// a counterexample exactly when a boundary instance is false (KTD25).
    /// </summary>
    [Fact]
    public void AQuantifiedStatementAgreesWithTheClrAtEveryBoundaryInstance()
    {
        var compilation = CompilationFactory.Create(
            [new SourceFile("Quantified.cs", """
                using Warrant;

                public enum PaymentStatus { Pending, Processed, Failed }

                public sealed record Payment(int Id, int Amount, PaymentStatus Status);

                public enum PaymentResult { Valid, InvalidAmount, InvalidStatus }

                public static class Quantified
                {
                    [Verified] public static int Increment(int x) => x + 1;

                    [Verified] public static bool Flip(bool b) => !b;

                    [Verified]
                    public static PaymentResult Validate(Payment p)
                    {
                        if (p.Amount <= 0) return PaymentResult.InvalidAmount;
                        if (p.Status != PaymentStatus.Pending) return PaymentResult.InvalidStatus;
                        return PaymentResult.Valid;
                    }

                    [Theorem] static Proof AlwaysLarger(int x) => Prove.That(Increment(x) > x);

                    [Theorem] static Proof LargerBelowMax(int x) => Prove.That(Spec.Implies(x < int.MaxValue, Increment(x) > x));

                    [Theorem] static Proof FlipTwice(bool b) => Prove.That(Flip(Flip(b)) == b);

                    [Theorem]
                    static Proof ValidImpliesPositive(Payment p) =>
                        Prove.That(Spec.Implies(Validate(p) == PaymentResult.Valid, p.Amount > 0));

                    [Theorem] static Proof Ordered(long a, long b) => Prove.That(a >= b || b > unchecked(a + 1));
                }
                """)],
            checkOverflow: false);
        var extraction = EngineCorpus.Extract(compilation);
        Assert.Empty(extraction.Diagnostics);
        var run = Pipeline.Run(EngineCorpus.Inputs(extraction), corpus.Bundle, KernelLimits.Corpus);
        var translation = Translator.Translate(extraction.Units.Select(u => u.Unit), corpus.Bundle.Env);

        var (claimsCompilation, _) = ClaimsCompilation(compilation);
        using var assembly = CorpusAssembly.Load(claimsCompilation);
        var definitions = extraction.Units.Where(u => u.Unit.Definition is not null).ToDictionary(u => u.Key, u => u.Unit.Definition!, StringComparer.Ordinal);
        var values = new Values(assembly, definitions);
        var inputs = new Inputs(values);

        var instances = new Dictionary<string, (int True, int False)>(StringComparer.Ordinal);
        foreach (var theorem in extraction.Units.Where(u => u.Unit.Kind == VirUnitKind.Theorem))
        {
            var outcome = run.Find(theorem.Key);
            var notProved = outcome as NotProvedOutcome ?? throw new Xunit.Sdk.XunitException($"{theorem.Key}: {Describe(outcome)}");
            Assert.Equal("unsolved goals", notProved.Message);
            var shell = translation.Find(theorem.Key)!.Theorem!;
            var types = (theorem.Unit.Params ?? VirList<VirParam>.Empty).Select(p => p.Type).ToList();
            var method = assembly.MethodOf(theorem.Unit);
            var counts = (True: 0, False: 0);
            KernelThread.Run(() =>
            {
                foreach (var args in inputs.BoundaryInputs(types))
                {
                    var claim = (bool)CorpusAssembly.Invoke(method, args)!;
                    var instance = shell.Type;
                    for (int i = 0; i < types.Count; i++)
                    {
                        instance = ExprOps.Instantiate(Assert.IsType<ForallExpr>(instance).Body, values.Term(types[i], args[i]));
                    }
                    var decide = Expr.App(Expr.Const(Name.Parse("Decidable.decide")), instance, DecidableInstance(instance));
                    var checker = new TypeChecker(run.Environment, limits: KernelLimits.Corpus);
                    checker.Check(decide);
                    var decided = checker.Whnf(decide);
                    var description = $"{theorem.DisplayName}({string.Join(", ", args.Select((a, i) => values.Display(types[i], a)))})";
                    Assert.True(decided.Equals(Literals.Bool(claim)), $"{description}: the CLR computes {claim}, the statement decides to {decided}");
                    counts = claim ? (counts.True + 1, counts.False) : (counts.True, counts.False + 1);
                }
            });
            instances.Add(theorem.Key, counts);
            Assert.True(counts.False > 0 == !notProved.Counterexample.IsEmpty, $"{theorem.Key}: {counts.False} false instance(s), counterexample [{OutcomeText.Counterexample(notProved.Counterexample)}]");
        }

        // Each claim's true and false instances among the boundary values.
        Assert.Equal(
            new Dictionary<string, (int, int)>
            {
                ["M:Quantified.AlwaysLarger(System.Int32)"] = (6, 1),
                ["M:Quantified.LargerBelowMax(System.Int32)"] = (7, 0),
                ["M:Quantified.FlipTwice(System.Boolean)"] = (2, 0),
                // Id and Amount at the int boundaries, Status at its three members and four unnamed values.
                ["M:Quantified.ValidImpliesPositive(Payment)"] = (7 * 7 * 7, 0),
                ["M:Quantified.Ordered(System.Int64,System.Int64)"] = (7 * 7 - 4, 4),
            },
            instances);
    }

    private static readonly Dictionary<string, (string Eq, string Lt, string Le)> Decidables = new(StringComparer.Ordinal)
    {
        ["Int32"] = ("instDecidableEqInt32", "Int32.decLt", "Int32.decLe"),
        ["Int64"] = ("instDecidableEqInt64", "Int64.decLt", "Int64.decLe"),
        ["Bool"] = ("instDecidableEqBool", "", ""),
    };

    /// <summary>
    /// A <c>Decidable P</c> instance for a closed, quantifier-free proposition, by its head: the instances Lean's
    /// instance resolution finds for <c>=</c>, <c>&lt;</c>, <c>≤</c>, <c>&gt;</c>, <c>≥</c>, <c>¬</c>, <c>∧</c>, <c>∨</c> and
    /// <c>→</c> on the types C# compares.
    /// </summary>
    private static Expr DecidableInstance(Expr p)
    {
        Expr C(string name) => Expr.Const(Name.Parse(name));
        if (p is ForallExpr f)
        {
            Assert.False(f.Body.HasLooseBVars, $"{p} is not an implication");
            return Expr.App(
                C("forall_prop_decidable"), f.BinderType, Expr.Lam(f.BinderName, f.BinderType, f.Body), DecidableInstance(f.BinderType), Expr.Lam(f.BinderName, f.BinderType, DecidableInstance(f.Body)));
        }
        var head = Assert.IsType<ConstExpr>(p.GetAppFn()).Name.ToString();
        var args = p.GetAppArgs();
        string Type() => Assert.IsType<ConstExpr>(args[0]).Name.ToString();
        return head switch
        {
            "Eq" => Expr.App(C(Decidables[Type()].Eq), args[1], args[2]),
            "LT.lt" => Expr.App(C(Decidables[Type()].Lt), args[2], args[3]),
            "LE.le" => Expr.App(C(Decidables[Type()].Le), args[2], args[3]),
            "GT.gt" => Expr.App(C(Decidables[Type()].Lt), args[3], args[2]),
            "GE.ge" => Expr.App(C(Decidables[Type()].Le), args[3], args[2]),
            "Not" => Expr.App(C("instDecidableNot"), args[0], DecidableInstance(args[0])),
            "And" => Expr.App(C("instDecidableAnd"), args[0], args[1], DecidableInstance(args[0]), DecidableInstance(args[1])),
            "Or" => Expr.App(C("instDecidableOr"), args[0], args[1], DecidableInstance(args[0]), DecidableInstance(args[1])),
            _ => throw new InvalidOperationException($"no Decidable instance for {p}"),
        };
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
        NotProvedOutcome n => $"not proved (WRT0001): {n.Message}",
        UndecidedOutcome u => $"undecided (WRT0006): {u.Reason}",
        InternalErrorOutcome i => $"internal error (WRT0010): {i.Reason}",
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
