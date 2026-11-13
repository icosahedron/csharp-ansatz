using Warrant.Engine.Contracts;
using Warrant.Engine.Reports;
using Warrant.Vir;

namespace Warrant.Engine.Tests;

/// <summary>
/// <c>Spec.NoThrow</c> (#182): the contract allows only an exception propagated from a dependency, so the default
/// procedure must show every explicit throw unreachable under the <c>Requires</c>. A reachable one fails at the
/// <c>throw</c> instead of being listed as a <c>MayThrow</c> assumption; a dependency's exception is still allowed and
/// listed. Callers use a NoThrow callee's contract whether or not they have NoThrow themselves.
/// </summary>
public sealed class NoThrowTests(EngineFixture engine) : IClassFixture<EngineFixture>
{
    private EngineResult Run(string source) =>
        Pipeline.Run(EngineCorpus.Inputs(EngineCorpus.Inline(source)), engine.Bundle, engine.Options);

    private static string Wrap(string members) => $"public static class S\n{{\n{members}\n}}\n";

    /// <summary>The source text of a node of an inline source's unit.</summary>
    private static string Text(string source, string key, int? node)
    {
        var span = OutcomeText.SpanOf(EngineCorpus.Inline(source).Units.Single(u => u.Key == key).Spans, node);
        Assert.NotNull(span);
        var lines = ("using Warrant;\n" + source).Split('\n');
        Assert.Equal(span.StartLine, span.EndLine);
        return lines[span.StartLine - 1][(span.StartColumn - 1)..(span.EndColumn - 1)].Trim();
    }

    private static void Proved(UnitOutcome? outcome) =>
        Assert.True(outcome is TranslatedOutcome t && t.Declarations.Any(d => d is Kernel.TheoremDecl), Describe(outcome));

    private static string Describe(UnitOutcome? outcome) =>
        outcome is NotProvedOutcome n ? string.Join("\n----\n", n.Vcs.Select(v => $"{v.Kind}: {v.Message}\n{v.Goals}").Prepend(n.Message + "\n" + n.Goals)) : $"{outcome}";

    /// <summary>The one failing VC of a method: its kind, the source text at its node, and the outcome's message.</summary>
    private static (VcKind Kind, string Text, string Message) Failure(string source, string key, UnitOutcome? outcome)
    {
        var notProved = Assert.IsType<NotProvedOutcome>(outcome);
        Assert.True(notProved.Vcs.Length == 1, Describe(outcome));
        var vc = notProved.Vcs[0];
        Assert.StartsWith(VcKinds.Text(vc.Kind), notProved.Message, StringComparison.Ordinal);
        return (vc.Kind, Text(source, key, vc.Node), notProved.Message);
    }

    private static IEnumerable<UnitAssumption> MayThrow(UnitOutcome? outcome) =>
        outcome!.Assumptions.Where(a => a.Assumption.Kind == VirAssumptionKind.MayThrow);

    [Fact]
    public void AThrowRuledOutByTheRequiresProvesWithNoMayThrowAndItsTwinFailsAtTheThrow()
    {
        var source = Wrap("""
            [Verified]
            public static int Divide(int a, int b)
            {
                Spec.Requires(b != 0 && b != -1);
                Spec.NoThrow();
                if (b == 0)
                {
                    throw new System.ArgumentException("b");
                }
                return a / b;
            }

            [Verified]
            public static int DivideAny(int a, int b)
            {
                Spec.Requires(b != -1);
                Spec.NoThrow();
                if (b == 0)
                {
                    throw new System.ArgumentException("b");
                }
                return a / b;
            }
            """);
        var result = Run(source);
        var divide = result.Find("M:S.Divide(System.Int32,System.Int32)");
        Proved(divide);
        Assert.Empty(MayThrow(divide));
        const string any = "M:S.DivideAny(System.Int32,System.Int32)";
        var (kind, text, message) = Failure(source, any, result.Find(any));
        Assert.Equal(VcKind.ReachableThrow, kind);
        Assert.Equal("throw new System.ArgumentException(\"b\");", text);
        Assert.StartsWith("an explicit throw is reachable under the Requires (Spec.NoThrow)", message, StringComparison.Ordinal);
    }

    /// <summary>docs/proving/proofs-that-work.md, "No reachable throw: Spec.NoThrow".</summary>
    [Fact]
    public void TheGuideExampleProvesAndItsTwinWithoutTheRequiresFailsAtTheThrow()
    {
        var source = Wrap("""
            [Verified]
            public static int NonZero(int b)
            {
                Spec.Requires(b != 0);
                Spec.NoThrow();
                if (b == 0)
                {
                    throw new System.ArgumentException("b must not be zero");
                }
                return b;
            }

            [Verified]
            public static int NonZeroOfAny(int b)
            {
                Spec.NoThrow();
                if (b == 0)
                {
                    throw new System.ArgumentException("b must not be zero");
                }
                return b;
            }
            """);
        var result = Run(source);
        var proved = result.Find("M:S.NonZero(System.Int32)");
        Proved(proved);
        Assert.Empty(MayThrow(proved));
        const string any = "M:S.NonZeroOfAny(System.Int32)";
        var notProved = Assert.IsType<NotProvedOutcome>(result.Find(any));
        var (kind, text, message) = Failure(source, any, notProved);
        Assert.Equal(VcKind.ReachableThrow, kind);
        Assert.Equal("throw new System.ArgumentException(\"b must not be zero\");", text);
        Assert.Equal("an explicit throw is reachable under the Requires (Spec.NoThrow): omega could not prove the goal:", message.Split('\n')[0]);
        Assert.Equal("case ht\nb : Int32\nh : b = 0\n⊢ False", notProved.Vcs[0].Goals);
    }

    [Fact]
    public void AReachableThrowsGoalShowsNoHypothesisTheRequiresSimplifiedToTrue()
    {
        // #240: under b = 0 the Requires b != -1 simplifies to True, which says nothing and is not shown.
        var source = Wrap("""
            [Verified]
            public static int QuotientOfAny(int a, int b)
            {
                Spec.Requires(b != -1);
                Spec.NoThrow();
                if (b == 0)
                {
                    throw new System.ArgumentException("b");
                }
                return a / b;
            }
            """);
        const string key = "M:S.QuotientOfAny(System.Int32,System.Int32)";
        var notProved = Assert.IsType<NotProvedOutcome>(Run(source).Find(key));
        var (kind, _, _) = Failure(source, key, notProved);
        Assert.Equal(VcKind.ReachableThrow, kind);
        Assert.Equal("case ht\na b : Int32\nh : b = 0\n⊢ False", notProved.Vcs[0].Goals);
        Assert.Equal(notProved.Vcs[0].Goals, notProved.Goals);
    }

    [Fact]
    public void AThrowExpressionIsAnExplicitThrowToo()
    {
        var source = "#nullable enable\n" + Wrap("""
            [Verified]
            public static int Value(int? x)
            {
                Spec.Requires(x != null);
                Spec.NoThrow();
                return x ?? throw new System.ArgumentNullException("x");
            }

            [Verified]
            public static int ValueOfAny(int? x)
            {
                Spec.NoThrow();
                return x ?? throw new System.ArgumentNullException("x");
            }
            """);
        var result = Run(source);
        Proved(result.Find("M:S.Value(System.Nullable{System.Int32})"));
        const string any = "M:S.ValueOfAny(System.Nullable{System.Int32})";
        var (kind, text, _) = Failure(source, any, result.Find(any));
        Assert.Equal(VcKind.ReachableThrow, kind);
        Assert.Equal("throw new System.ArgumentNullException(\"x\")", text);
    }

    [Fact]
    public void AnImplicitExceptionUnderNoThrowKeepsItsOwnKind()
    {
        var source = Wrap("""
            [Verified]
            public static int Ratio(int a, int b)
            {
                Spec.Requires(b != -1);
                Spec.NoThrow();
                return a / b;
            }
            """);
        const string key = "M:S.Ratio(System.Int32,System.Int32)";
        var (kind, text, _) = Failure(source, key, Run(source).Find(key));
        Assert.Equal(VcKind.DivisionByZero, kind);
        Assert.Equal("a / b", text);
    }

    [Fact]
    public void CallersUseANoThrowCalleesContractAndANoThrowCallerNeedsNoThrowCallees()
    {
        var source = Wrap("""
            [Verified]
            public static int Checked(int a, int b)
            {
                Spec.Requires(b > 0);
                Spec.NoThrow();
                Spec.Ensures<int>(r => r == a);
                if (b <= 0)
                {
                    throw new System.ArgumentException("b");
                }
                return a;
            }

            [Verified]
            public static int Loose(int a, int b)
            {
                Spec.Requires(b > 0);
                Spec.Ensures<int>(r => r == a);
                if (b <= 0)
                {
                    throw new System.ArgumentException("b");
                }
                return a;
            }

            [Verified]
            public static int Positive(int x)
            {
                Spec.Requires(x > 0);
                return x;
            }

            [Verified]
            public static int Plain(int a)
            {
                Spec.Ensures<int>(r => r == a);
                return Checked(a, 2);
            }

            [Verified]
            public static int Strict(int a)
            {
                Spec.NoThrow();
                Spec.Ensures<int>(r => r == a);
                return Checked(a, 2);
            }

            [Verified]
            public static int StrictOfPure(int a)
            {
                Spec.NoThrow();
                return Positive(2);
            }

            [Verified]
            public static int PlainOfLoose(int a)
            {
                Spec.Ensures<int>(r => r == a);
                return Loose(a, 2);
            }

            [Verified]
            public static int StrictOfLoose(int a)
            {
                Spec.NoThrow();
                return Loose(a, 2);
            }
            """);
        var result = Run(source);
        Proved(result.Find("M:S.Checked(System.Int32,System.Int32)"));
        Proved(result.Find("M:S.Loose(System.Int32,System.Int32)"));
        Proved(result.Find("M:S.PlainOfLoose(System.Int32)"));
        // A caller without NoThrow: the callee's exceptions are fewer than its own contract allows.
        var plain = result.Find("M:S.Plain(System.Int32)");
        Proved(plain);
        Assert.Empty(MayThrow(plain));
        // A caller with NoThrow: the callee allows what it allows.
        var strict = result.Find("M:S.Strict(System.Int32)");
        Proved(strict);
        Assert.Empty(MayThrow(strict));
        Proved(result.Find("M:S.StrictOfPure(System.Int32)"));
        // A callee without NoThrow may throw explicitly, which a NoThrow caller does not allow: a failure at the call.
        const string loose = "M:S.StrictOfLoose(System.Int32)";
        var (kind, text, message) = Failure(source, loose, result.Find(loose));
        Assert.Equal(VcKind.CalleeMayThrow, kind);
        Assert.Equal("Loose(a, 2)", text);
        // #238: the caller sees only the callee's contract, so the message names the callee and the workaround.
        Assert.Equal(
            "a callee without Spec.NoThrow may throw explicitly at this call (Spec.NoThrow): the contract of Loose allows an "
            + "explicit throw whatever the arguments, since a caller sees only the callee's contract, not its body; add "
            + "Spec.NoThrow to Loose, with a Spec.Requires that rules its throws out and that this call meets",
            message.Split('\n')[0]);
    }

    [Fact]
    public void ADependencysExceptionIsStillAllowedAndListed()
    {
        var source = """
            public interface ICounter { int Count(int id); }

            [ContractFor(typeof(ICounter))]
            internal abstract class CounterContract : ICounter
            {
                public int Count(int id) { Spec.Requires(id > 0); Spec.Ensures<int>(r => r >= 0); return default!; }
            }

            public sealed class Tally(ICounter counter)
            {
                [Verified]
                public int Size(int id)
                {
                    Spec.Requires(id > 0);
                    Spec.NoThrow();
                    Spec.Ensures<int>(r => r >= 0);
                    if (id <= 0)
                    {
                        throw new System.ArgumentException("id");
                    }
                    return counter.Count(id);
                }
            }
            """;
        const string key = "M:Tally.Size(System.Int32)";
        var size = Run(source).Find(key);
        Proved(size);
        var mayThrow = Assert.Single(MayThrow(size));
        var subject = MayThrowSubject.Parse(mayThrow.Assumption.Subject);
        Assert.Equal("M:ICounter.Count(System.Int32)", subject.Thrown);
        Assert.Equal("counter.Count(id)", Text(source, key, subject.Node));
    }

    [Fact]
    public void AScriptProofListsNoMayThrowForTheMethodsOwnThrows()
    {
        // #229: a script's proof lists what its walks relied on; under NoThrow the walk shows the method's own throws
        // unreachable, so none is listed.
        var source = Wrap("""
            [Verified]
            public static int Guard(int b)
            {
                Spec.Requires(b != 0);
                Spec.NoThrow();
                if (b == 0)
                {
                    throw new System.ArgumentException("b");
                }
                return b;
            }

            [ProofFor(nameof(Guard))]
            static Proof GuardProof() => Prove.Contract().By(Tactic.VcGen(), Tactic.AllGoals(Tactic.Omega()));
            """);
        var guard = Run(source).Find("M:S.Guard(System.Int32)");
        Proved(guard);
        Assert.Empty(MayThrow(guard));
    }
}
