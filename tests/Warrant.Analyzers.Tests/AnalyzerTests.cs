using Microsoft.CodeAnalysis.CSharp;

namespace Warrant.Analyzers.Tests;

/// <summary>
/// The analyzer (M5b U15, R18): it loads and reports under this project's Roslyn, gives the same diagnostics on every
/// concurrent run, never throws, and stays silent where Warrant is not used. This file runs under Roslyn 5.9 and, linked
/// into Warrant.Analyzers.Tests.Roslyn48, under Roslyn 4.8.
/// </summary>
public sealed class AnalyzerTests
{
    /// <summary>Two files, C# 12, with one of each diagnostic the analyzer reports.</summary>
    private static readonly (string Path, string Text)[] Sample =
    [
        ("Rules.cs", """
            using Warrant;

            namespace Sample;

            [Closed] public enum Light { Red, Amber, Green }

            public static class Rules
            {
                [Verified] public static int Half(int x) => x << 1;
                [Verified] public static int Fine(int x) => x + 1;
                [Verified] public static int UsesHalf(int x) => Half(x) + 1;
                [Verified] public static int Absolute(int x) => System.Math.Sign(x);
                [Verified] public static bool Implies(int x) => Spec.Implies(x > 0, x > 1);
                [Theorem] static Proof FineOfOne() => Prove.That(Fine(1) == 2);
                [Verified] public static int CallsTheorem() { FineOfOne(); return 0; }
                public static Light FromInt(int i) => (Light)i;
            }
            """),
        ("Outcomes.cs", """
            using Warrant;

            namespace Sample;

            [Closed]
            public sealed class Outcome
            {
                public static Outcome Matched { get; } = new Outcome();
                public Outcome() { }
            }

            public static class Loops
            {
                [Verified]
                public static int Count(int n)
                {
                    int s = 0;
                    for (int i = 0; i < n; i++) s += i;
                    return s;
                }
            }
            """),
    ];

    [Fact]
    public async Task TheAnalyzerLoadsUnderThisRoslynAndReportsEachKindOfDiagnosticAtItsConstruct()
    {
        Assert.Equal(AnalyzerHarness.RoslynMajor, typeof(CSharpCompilation).Assembly.GetName().Version!.Major);
        var compilation = AnalyzerHarness.Compile(Sample);
        Assert.Empty(compilation.GetDiagnostics().Where(d => d.Severity == Microsoft.CodeAnalysis.DiagnosticSeverity.Error));

        var (lines, exceptions) = await AnalyzerHarness.Run(compilation);

        Assert.Empty(exceptions);
        Assert.Collection(
            lines,
            l => Assert.StartsWith("Outcomes.cs(6,21,6,28): error WRT0009: ", l, StringComparison.Ordinal),
            l => Assert.Equal("Outcomes.cs(18,9,18,44): error WRT0002: M4 does not support loop.", l),
            l => Assert.Equal("Rules.cs(9,49,9,55): error WRT0002: M4 does not support shift.", l),
            l => Assert.Matches(@"^Rules\.cs\(11,\d+,11,\d+\): error WRT0002: .*depends on .*Half", l),
            l => Assert.Matches(@"^Rules\.cs\(12,\d+,12,\d+\): error WRT0005: ", l),
            l => Assert.Matches(@"^Rules\.cs\(13,\d+,13,\d+\): error WRT0004: ", l),
            l => Assert.Matches(@"^Rules\.cs\(15,\d+,15,\d+\): error WRT0003: ", l),
            l => Assert.Matches(@"^Rules\.cs\(16,43,16,51\): warning WRT0008: .*integer cast to a closed enum", l));
    }

    [Fact]
    public async Task TwentyConcurrentRunsGiveByteIdenticalDiagnosticsAndTheAnalyzerNeverThrows()
    {
        var compilation = AnalyzerHarness.Compile(Sample);

        var runs = await Task.WhenAll(Enumerable.Range(0, 20).Select(_ => Task.Run(() => AnalyzerHarness.Run(compilation))));

        Assert.All(runs, r => Assert.Empty(r.Exceptions));
        var first = string.Join("\n", runs[0].Lines);
        Assert.NotEmpty(runs[0].Lines);
        Assert.All(runs, r => Assert.Equal(first, string.Join("\n", r.Lines)));
    }

    [Fact]
    public async Task ACompilationWithoutWarrantGetsNothing()
    {
        var compilation = CSharpCompilation.Create(
            "Plain",
            [CSharpSyntaxTree.ParseText("public static class S { public static int Half(int x) => x / 2; }")],
            AnalyzerHarness.Compile().References);

        var (lines, exceptions) = await AnalyzerHarness.Run(compilation);

        Assert.Empty(exceptions);
        Assert.Empty(lines);
    }

    [Fact]
    public async Task AMemberThatDoesNotCompileIsLeftToTheCompilerAndItsNeighboursAreStillChecked()
    {
        var compilation = AnalyzerHarness.Compile(("S.cs", """
            using Warrant;
            public static class S
            {
                [Verified] public static int Broken(int x) => x / undefinedName;
                [Verified] public static int Rem(int x) => x & 3;
            }
            """));

        var (lines, exceptions) = await AnalyzerHarness.Run(compilation);

        Assert.Empty(exceptions);
        Assert.Matches(@"^S\.cs\(5,\d+,5,\d+\): error WRT0002: .*integer bitwise operator", Assert.Single(lines));
    }
}
