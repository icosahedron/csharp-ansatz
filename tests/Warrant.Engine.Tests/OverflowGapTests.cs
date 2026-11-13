using Warrant.Engine.Contracts;

namespace Warrant.Engine.Tests;

/// <summary>
/// Bounds that hold but that #244's obligations over a pure body could not see (#255, #256, #258): a join point's
/// parameters, a closed-enum switch arm, and a recursive method's <c>Spec.Requires</c>. Each test pairs the bound that
/// now proves with a twin where the same fact would be wrong, which must still fail.
/// </summary>
public sealed class OverflowGapTests(EngineFixture engine) : IClassFixture<EngineFixture>
{
    private EngineResult Run(string source) =>
        Pipeline.Run(EngineCorpus.Inputs(EngineCorpus.Inline(source)), engine.Bundle, engine.Options);

    private static string Wrap(string members) => $"public static class S\n{{\n{members}\n}}\n";

    private static string Text(string source, string key, int? node)
    {
        var span = Reports.OutcomeText.SpanOf(EngineCorpus.Inline(source).Units.Single(u => u.Key == key).Spans, node);
        Assert.NotNull(span);
        var lines = ("using Warrant;\n" + source).Split('\n');
        Assert.Equal(span.StartLine, span.EndLine);
        return lines[span.StartLine - 1][(span.StartColumn - 1)..(span.EndColumn - 1)].Trim();
    }

    private static void Proved(UnitOutcome? outcome) =>
        Assert.True(outcome is TranslatedOutcome t && t.Declarations.Any(d => d is Kernel.TheoremDecl), Describe(outcome));

    private static string Describe(UnitOutcome? outcome) =>
        outcome is NotProvedOutcome n ? string.Join("\n----\n", n.Vcs.Select(v => $"{v.Kind}: {v.Message}\n{v.Goals}").Prepend(n.Message + "\n" + n.Goals)) : $"{outcome}";

    private static (VcKind Kind, string Text) Failure(string source, string key, UnitOutcome? outcome)
    {
        var notProved = Assert.IsType<NotProvedOutcome>(outcome);
        var vc = Assert.Single(notProved.Vcs);
        return (vc.Kind, Text(source, key, vc.Node));
    }

    [Fact]
    public void AJoinPointsParametersCarryTheirValueOnEachIncomingPathIntoLaterObligations()
    {
        // #255: a local merged after branches is known by its value on each path that reaches the join point, with what
        // that path knew, so the arithmetic after it is bounded. A path whose value would overflow still fails.
        var source = Wrap("""
            [Verified]
            public static int Shipping(int weight, bool express, bool member)
            {
                Spec.Requires(weight >= 0 && weight <= 1000000);
                var cost = weight * 2;
                var bonus = 0;
                if (express)
                {
                    cost = cost + 15;
                    bonus = 1;
                }
                if (member) return cost - 5;
                return cost + bonus;
            }

            [Verified]
            public static int Bucket(int code)
            {
                var result = 0;
                switch (code)
                {
                    case 1:
                        result = 10;
                        break;
                    case >= 5 and < 9:
                        return 20;
                }
                return result + 1;
            }

            [Verified]
            public static int Nested(bool p, bool q, int x)
            {
                Spec.Requires(x >= 0 && x <= 100);
                var a = x;
                var b = 0;
                if (p)
                {
                    if (q)
                    {
                        a = a + 1;
                        b = 1;
                    }
                    a = a + b;
                    if (a > 1000) return 0;
                }
                return a * 2;
            }

            [Verified]
            public static int Edge(bool big)
            {
                var a = 0;
                var b = 0;
                if (big)
                {
                    a = int.MaxValue;
                    b = 1;
                }
                if (b > 5) return 0;
                return a + 1;
            }
            """);
        var result = Run(source);
        Proved(result.Find("M:S.Shipping(System.Int32,System.Boolean,System.Boolean)"));
        Proved(result.Find("M:S.Bucket(System.Int32)"));
        Proved(result.Find("M:S.Nested(System.Boolean,System.Boolean,System.Int32)"));
        const string edge = "M:S.Edge(System.Boolean)";
        Assert.Equal((VcKind.ArithmeticOverflow, "a + 1"), Failure(source, edge, result.Find(edge)));
    }

    [Fact]
    public void AClosedEnumSwitchArmKnowsItsCase()
    {
        // #258: inside the arm or section a closed-enum switch takes, the scrutinee is one of the members it covers.
        // The arm that covers the other member does not know the bound, and fails.
        var source = """
            [Closed]
            public enum Size { Small, Medium, Big }

            public static class S
            {
                [Verified]
                public static int Section(Size s, int x)
                {
                    Spec.Requires(s != Size.Small || (x >= 0 && x <= 1000));
                    switch (s)
                    {
                        case Size.Small:
                            return x * 2;
                        default:
                            return 0;
                    }
                }

                [Verified]
                public static int Arm(Size s, int x)
                {
                    Spec.Requires(s == Size.Big || (x >= 0 && x <= 1000));
                    return s switch { Size.Big => 0, _ => x + 1 };
                }

                [Verified]
                public static int Shared(Size s, int x)
                {
                    Spec.Requires(s == Size.Big || (x >= 0 && x <= 1000));
                    var y = 0;
                    switch (s)
                    {
                        case Size.Small:
                        case Size.Medium:
                            y = x * 3;
                            break;
                    }
                    return y;
                }

                [Verified]
                public static int WrongArm(Size s, int x)
                {
                    Spec.Requires(s != Size.Small || (x >= 0 && x <= 1000));
                    return s switch { Size.Small => 0, _ => x + 1 };
                }

                [Verified]
                public static int Wrong(Size s, int x)
                {
                    Spec.Requires(s != Size.Small || (x >= 0 && x <= 1000));
                    switch (s)
                    {
                        case Size.Big:
                            return x * 2;
                        default:
                            return 0;
                    }
                }
            }
            """;
        var result = Run(source);
        Proved(result.Find("M:S.Section(Size,System.Int32)"));
        Proved(result.Find("M:S.Arm(Size,System.Int32)"));
        Proved(result.Find("M:S.Shared(Size,System.Int32)"));
        const string wrongArm = "M:S.WrongArm(Size,System.Int32)";
        Assert.Equal((VcKind.ArithmeticOverflow, "x + 1"), Failure(source, wrongArm, result.Find(wrongArm)));
        const string wrong = "M:S.Wrong(Size,System.Int32)";
        Assert.Equal((VcKind.ArithmeticOverflow, "x * 2"), Failure(source, wrong, result.Find(wrong)));
    }

    [Fact]
    public void ARecursiveMethodsRequiresIsAssumedByItsBodyAndCheckedAtEachRecursiveCall()
    {
        // #256: a recursive method may state Spec.Requires. Its body's obligations assume it, and each recursive call must
        // satisfy it, as every outside caller must; a recursive call that does not fails at the call.
        var source = Wrap("""
            [Verified]
            public static int Add(int a, int b)
            {
                Spec.Decreases(b);
                Spec.Requires(b >= 0 && a >= 0 && a <= int.MaxValue - b);
                if (b <= 0) return a;
                return Add(a + 1, b - 1);
            }

            [Verified]
            public static int Sum(int n)
            {
                Spec.Decreases(n);
                Spec.Requires(n >= 0 && n <= 1000);
                if (n <= 0) return 0;
                return n + Sum(n - 1);
            }

            [Verified]
            public static int Grow(int a, int b)
            {
                Spec.Decreases(b);
                Spec.Requires(a >= 0 && a <= 1000);
                if (b <= 0) return a;
                return Grow(a + 1, b - 1);
            }

            [Verified]
            public static int CallsAdd() => Add(1, 2);

            [Verified]
            public static int CallsAddBadly(int a) => Add(a, 2);
            """);
        var result = Run(source);
        Proved(result.Find("M:S.Add(System.Int32,System.Int32)"));
        Proved(result.Find("M:S.CallsAdd"));
        // The sum of n results is not bounded without Spec.Ensures (#256's follow-up), so its + still fails.
        const string sum = "M:S.Sum(System.Int32)";
        Assert.Equal((VcKind.ArithmeticOverflow, "n + Sum(n - 1)"), Failure(source, sum, result.Find(sum)));
        // a + 1 is in range, but the recursive call's a may pass 1000.
        const string grow = "M:S.Grow(System.Int32,System.Int32)";
        Assert.Equal("Grow(a + 1, b - 1)", Text(source, grow, Assert.IsType<NotProvedOutcome>(result.Find(grow)).TacticNode));
        Assert.IsNotType<TranslatedOutcome>(result.Find("M:S.CallsAddBadly(System.Int32)"));
    }
}
