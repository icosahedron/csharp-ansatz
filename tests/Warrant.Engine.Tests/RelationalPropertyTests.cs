namespace Warrant.Engine.Tests;

/// <summary>
/// A property relating two calls of a method that can raise (#181): a theorem cannot call the method, so the relation is
/// the <c>Spec.Ensures</c> of a verified wrapper that makes both calls, proved by the default procedure from each
/// callee's contract, or, when the method's <c>Spec.Ensures</c> pins its result, a theorem about the pure expression.
/// docs/proving/proofs-that-work.md runs these examples.
/// </summary>
public sealed class RelationalPropertyTests(EngineFixture engine) : IClassFixture<EngineFixture>
{
    private const string Source = """
        public static class S
        {
            [Verified]
            public static int Scale(int x)
            {
                Spec.Requires(x <= 1000);
                Spec.Ensures<int>(r => r == x + x);
                if (x < 0)
                {
                    throw new System.ArgumentException("x");
                }
                return checked(x + x);
            }

            [Verified]
            public static bool Monotone(int x, int y)
            {
                Spec.Requires(0 <= x && x <= y && y <= 1000);
                Spec.Ensures<bool>(r => r);
                return Scale(x) <= Scale(y);
            }

            [Theorem]
            static Proof DoubleIsMonotone(int x, int y) =>
                Prove.That(Spec.Implies(0 <= x && x <= y && y <= 1000, x + x <= y + y)).By(Tactic.Simp(), Tactic.Omega());
        }
        """;

    private static string Describe(UnitOutcome? outcome) =>
        outcome is NotProvedOutcome n ? string.Join("\n----\n", n.Vcs.Select(v => $"{v.Kind}: {v.Message}\n{v.Goals}").Prepend(n.Message + "\n" + n.Goals)) : $"{outcome}";

    private EngineResult Run() => Pipeline.Run(EngineCorpus.Inputs(EngineCorpus.Inline(Source)), engine.Bundle, engine.Options);

    [Fact]
    public void AWrapperThatCallsARaisingMethodTwiceProvesTheRelationWithNoScript()
    {
        var result = Run();
        var scale = result.Find("M:S.Scale(System.Int32)");
        Assert.True(scale is TranslatedOutcome t && t.Declarations.Any(d => d is Kernel.TheoremDecl), Describe(scale));
        var monotone = result.Find("M:S.Monotone(System.Int32,System.Int32)");
        Assert.True(monotone is TranslatedOutcome m && m.Declarations.Any(d => d is Kernel.TheoremDecl), Describe(monotone));
        Assert.Contains(monotone!.Assumptions, a => a.Assumption.Kind == Vir.VirAssumptionKind.CalleeContract && a.Assumption.Subject == "M:S.Scale(System.Int32)");
    }

    [Fact]
    public void ATheoremAboutThePureExpressionAnExactEnsuresPinsIsProved()
    {
        var outcome = Run().Find("M:S.DoubleIsMonotone(System.Int32,System.Int32)");
        Assert.True(outcome is ProvedOutcome, Describe(outcome));
    }

    [Fact]
    public void TheSameWrapperWithAWrappingTimesThreeIsNotProvedYet()
    {
        // The limit the guide states: `r == x * 3` is Int32 multiplication, which wraps, and omega (Lean's as well as
        // Warrant's port: it has no dark shadow) cannot use the bounds to rule out the wrap, so `x * 3 <= y * 3` stays open.
        var source = Source.Replace("x + x", "x * 3", StringComparison.Ordinal);
        var outcome = Pipeline.Run(EngineCorpus.Inputs(EngineCorpus.Inline(source)), engine.Bundle, engine.Options).Find("M:S.Monotone(System.Int32,System.Int32)");
        var notProved = Assert.IsType<NotProvedOutcome>(outcome);
        Assert.Equal(Contracts.VcKind.Postcondition, Assert.Single(notProved.Vcs).Kind);
    }
}
