using Warrant.Cic;
using Warrant.Kernel;
using Warrant.Meta;
using Warrant.Semantics;
using Warrant.Vir;

namespace Warrant.Engine.Tests;

/// <summary>
/// Contract obligations in the pipeline (plan M6 U10, KTD12, KTD16, KTD25, KTD26): each is admitted after its method's
/// definition, as a recursive method's decrease proofs are; a <c>[ProofFor]</c> script proves it from the triple; an
/// obligation that waits for the default procedure (M6 U11) is not proved; and a method whose contract is not proved is
/// not usable as a lemma, so its callers report that.
/// </summary>
public sealed class ContractTests(EngineFixture engine) : IClassFixture<EngineFixture>
{
    private EngineResult Run(string source) =>
        Pipeline.Run(EngineCorpus.Inputs(EngineCorpus.Inline(source)), engine.Bundle, engine.Options);

    private static string Names(UnitOutcome outcome) =>
        string.Join(", ", outcome.Declarations.Select(d => d switch
        {
            DefinitionDecl def => def.Value.Name.ToString(),
            TheoremDecl thm => thm.Value.Name.ToString(),
            _ => d.GetType().Name,
        }));

    /// <summary>The source text of a node of an inline source's unit.</summary>
    private static string Text(string source, string key, int? node)
    {
        var span = Reports.OutcomeText.SpanOf(EngineCorpus.Inline(source).Units.Single(u => u.Key == key).Spans, node);
        Assert.NotNull(span);
        var lines = ("using Warrant;\n" + source).Split('\n');
        Assert.Equal(span.StartLine, span.EndLine);
        return lines[span.StartLine - 1][(span.StartColumn - 1)..(span.EndColumn - 1)];
    }

    // ---- A [ProofFor] script proves the obligation (KTD16) ----

    private const string NonNegative = """
        public static class S
        {
            [Verified]
            public static int NonNegative(int x)
            {
                Spec.Ensures<int>(r => r >= 0);
                return x < 0 ? 0 : x;
            }

            [ProofFor(nameof(NonNegative))]
            static Proof NonNegativeProof() =>
                Prove.Contract().By(
                    Tactic.Apply(Lean.Const("Std.Do.Triple.pure")),
                    Tactic.Unfold(nameof(NonNegative)),
                    Tactic.Simp(Lean.Const("Std.Do.SPred.entails_1"), Lean.Const("Std.Do.SPred.apply_pure_cons"), Lean.Const("Std.Do.SPred.down_pure_nil")),
                    Tactic.Omega());

            [Theorem]
            static Proof NeverNegative(int x) =>
                Prove.That(NonNegative(x) >= 0).By(Tactic.Apply(Lean.Const("Cs.S.«NonNegative(System.Int32)».$contract_spec")));
        }
        """;

    [Fact]
    public void AProofForScriptProvesAPureMethodsContractAndItsSpecLemmaIsAvailableToCallers()
    {
        var result = Run(NonNegative);
        var outcome = Assert.IsType<TranslatedOutcome>(result.Find("M:S.NonNegative(System.Int32)"));
        Assert.Equal(
            "Cs.S.«NonNegative(System.Int32)», Cs.S.«NonNegative(System.Int32)».$contract, Cs.S.«NonNegative(System.Int32)».$contract_spec",
            Names(outcome));
        // The theorem uses the admitted spec lemma, not the method's body.
        Assert.True(result.Find("M:S.NeverNegative(System.Int32)") is ProvedOutcome { By: ProofKind.Script }, $"{result.Find("M:S.NeverNegative(System.Int32)")}");
    }

    [Fact]
    public void AScriptThatStartsWithVcGenWaitsForTheWalker()
    {
        const string source = """
            public static class S
            {
                [Verified]
                public static int Same(int x)
                {
                    Spec.Ensures<int>(r => r == x);
                    return x;
                }

                [ProofFor(nameof(Same))]
                static Proof SameProof() => Prove.Contract().By(Tactic.VcGen(), Tactic.Omega());
            }
            """;
        var outcome = Assert.IsType<NotProvedOutcome>(Run(source).Find("M:S.Same(System.Int32)"));
        Assert.Equal("Tactic `vcgen` is not available yet", outcome.Message);
        Assert.Equal("Tactic.VcGen()", Text(source, "M:S.Same(System.Int32)", outcome.TacticNode));
    }

    [Fact]
    public void AScriptThatDoesNotCloseTheObligationFailsAtItsTactic()
    {
        const string source = """
            public static class S
            {
                [Verified]
                public static int Identity(int x)
                {
                    Spec.Ensures<int>(r => r > x);
                    return x;
                }

                [Verified] public static int Caller(int x) => Identity(x) + 1;

                [ProofFor(nameof(Identity))]
                static Proof IdentityProof() =>
                    Prove.Contract().By(
                        Tactic.Apply(Lean.Const("Std.Do.Triple.pure")),
                        Tactic.Unfold(nameof(Identity)),
                        Tactic.Simp(Lean.Const("Std.Do.SPred.entails_1"), Lean.Const("Std.Do.SPred.apply_pure_cons"), Lean.Const("Std.Do.SPred.down_pure_nil")),
                        Tactic.Omega());
            }
            """;
        var result = Run(source);
        var outcome = Assert.IsType<NotProvedOutcome>(result.Find("M:S.Identity(System.Int32)"));
        Assert.Equal("Tactic.Omega()", Text(source, "M:S.Identity(System.Int32)", outcome.TacticNode));
        // An obligation that is not proved makes its callers report the dependency, not a second goal.
        var caller = Assert.IsType<SkippedOutcome>(result.Find("M:S.Caller(System.Int32)"));
        Assert.EndsWith("whose contract is not proved.", caller.Reason, StringComparison.Ordinal);
    }

    // ---- KTD25 and KTD26 ----

    [Fact]
    public void AnUnsatisfiableRequiresFailsAtItsLineBeforeAnyScriptRuns()
    {
        const string source = """
            public static class S
            {
                [Verified]
                public static int Never(int x)
                {
                    Spec.Requires(x > 0);
                    Spec.Requires(x < 0);
                    Spec.Ensures<int>(r => r == 42);
                    return x;
                }

                [ProofFor(nameof(Never))]
                static Proof NeverProof() =>
                    Prove.Contract().By(
                        Tactic.Apply(Lean.Const("Std.Do.Triple.pure")),
                        Tactic.Simp(Lean.Const("Std.Do.SPred.entails_1"), Lean.Const("Std.Do.SPred.apply_pure_cons"), Lean.Const("Std.Do.SPred.down_pure_nil")),
                        Tactic.Omega());
            }
            """;
        var outcome = Assert.IsType<NotProvedOutcome>(Run(source).Find("M:S.Never(System.Int32)"));
        Assert.StartsWith("The contract is unsatisfiable", outcome.Message, StringComparison.Ordinal);
        Assert.Equal("Spec.Requires(x < 0);", Text(source, "M:S.Never(System.Int32)", outcome.TacticNode));
    }

    [Fact]
    public void ACalleesPreconditionInASpecExpressionIsProvedOrFailsAtTheCall()
    {
        const string source = """
            public static class S
            {
                [Verified]
                public static int Positive(int x)
                {
                    Spec.Requires(x > 0);
                    return x;
                }

                // Proved, so its users are not skipped as depending on an unproved contract.
                [ProofFor(nameof(Positive))]
                static Proof PositiveProof() =>
                    Prove.Contract().By(
                        Tactic.Apply(Lean.Const("Std.Do.Triple.pure")),
                        Tactic.Simp(Lean.Const("Std.Do.SPred.entails_1"), Lean.Const("Std.Do.SPred.apply_pure_cons"), Lean.Const("Std.Do.SPred.down_pure_nil")));

                [Verified]
                public static int Inside(int x)
                {
                    Spec.Requires(x > 5);
                    Spec.Ensures<int>(r => r == Positive(x));
                    return x;
                }

                [Verified]
                public static int Outside(int x)
                {
                    Spec.Requires(x > -5);
                    Spec.Ensures<int>(r => r == Positive(x));
                    return x;
                }
            }
            """;
        var result = Run(source);
        // Inside's precondition obligation is proved; its own obligation then waits for the default procedure.
        var inside = Assert.IsType<NotProvedOutcome>(result.Find("M:S.Inside(System.Int32)"));
        Assert.StartsWith("The contract obligation was not proved", inside.Message, StringComparison.Ordinal);
        var outside = Assert.IsType<NotProvedOutcome>(result.Find("M:S.Outside(System.Int32)"));
        Assert.StartsWith("omega could not prove the goal", outside.Message, StringComparison.Ordinal);
        Assert.Equal("Positive(x)", Text(source, "M:S.Outside(System.Int32)", outside.TacticNode));
    }

    [Fact]
    public void APartialOperationInASpecExpressionWaitsForTheDefaultProcedureAtItsNode()
    {
        const string source = """
            public static class S
            {
                [Verified]
                public static int Ratio(int a, int b)
                {
                    Spec.Requires(b != 0 && a / b > 0);
                    return a;
                }
            }
            """;
        var outcome = Assert.IsType<NotProvedOutcome>(Run(source).Find("M:S.Ratio(System.Int32,System.Int32)"));
        Assert.StartsWith("The well-definedness of a Spec expression", outcome.Message, StringComparison.Ordinal);
        Assert.Equal("a / b", Text(source, "M:S.Ratio(System.Int32,System.Int32)", outcome.TacticNode));
    }

    // ---- The statement is the one Lean elaborates ----

    [Fact]
    public void TheTriplesWpInstanceIsTheOneInstanceResolutionFinds()
    {
        var units = EngineCorpus.Inputs(EngineCorpus.Inline("public static class S { [Verified] public static int Ratio(int a, int b) => a / b; }"));
        var translation = Translator.Translate(units.Select(u => u.Unit), engine.Bundle.Env);
        var statement = translation.Find("M:S.Ratio(System.Int32,System.Int32)")!.Contract!.Theorem.Type;
        var m = new MetaM(engine.Bundle.Env, MetaLimits.Default) { Attributes = EngineFixture.SharedSidecar.Value };
        KernelThread.Run(() => m.WithLocalDeclD(Name.From("σ"), Expr.Sort(Level.One), sigma =>
        {
            var triple = ExprOps.Instantiate(Assert.IsType<ForallExpr>(statement).Body, sigma);
            while (triple is ForallExpr forall)
            {
                triple = forall.Body;
            }
            var args = triple.GetAppArgs();
            var synthesized = m.SynthInstanceOrThrow(Expr.App(Expr.Const(Name.Parse("Std.Do.WP"), Level.Zero, Level.Zero), args[0], args[1]));
            Assert.Equal(m.InstantiateMVars(synthesized), args[2]);
            return sigma;
        }));
    }
}
