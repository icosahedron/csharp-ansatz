using Microsoft.CodeAnalysis.CSharp;
using Warrant.Extraction;
using Warrant.Frontend;
using Warrant.TestSupport;

namespace Warrant.Extraction.Tests;

/// <summary>
/// Diagnostics-only extraction (M5b U14, KTD22): <see cref="Diagnoser"/> reports for each member what a full extraction
/// reports, so the analyzer and the build agree. The reference is an extraction with the build's defines, which is what
/// the analyzer sees: the active configuration, without the <c>#if</c> combination check.
/// </summary>
public sealed class DiagnoseTests
{
    private static readonly ExtractionOptions ActiveConfiguration = new() { BuildDefines = true };

    public static TheoryData<string, string> Compilations()
    {
        var data = new TheoryData<string, string>();
        foreach (var set in new[] { CorpusSet.M4, CorpusSet.M5a, CorpusSet.M6 })
        {
            foreach (var name in set.Names)
            {
                data.Add(set.Name, name);
            }
        }
        return data;
    }

    private static CorpusSet Set(string set) => set switch { "m4" => CorpusSet.M4, "m5a" => CorpusSet.M5a, _ => CorpusSet.M6 };

    [Theory]
    [MemberData(nameof(Compilations))]
    public void EveryMembersDiagnosticsEqualTheFullExtractionsForThatMember(string set, string name)
    {
        var compilation = Set(set).Compile(name);
        var full = Extractor.Extract(compilation, ActiveConfiguration);
        Assert.False(full.HasCompileErrors);
        var diagnoser = new Diagnoser(compilation);
        Assert.NotEmpty(diagnoser.Members());

        foreach (var member in diagnoser.Members())
        {
            var key = Diagnoser.Key(member);
            var expected = full.Diagnostics.Where(d => d.MemberKey == key && d.Id != DiagnosticIds.UnnamedClosedValue).ToList();
            var actual = diagnoser.Member(member).Where(d => d.MemberKey == key).ToList();
            Assert.True(expected.SequenceEqual(actual), $"{key}: expected [{string.Join("; ", expected)}], got [{string.Join("; ", actual)}]");
        }
    }

    [Theory]
    [MemberData(nameof(Compilations))]
    public void TogetherTheMembersClosedTypesAndUnnamedValuesReportExactlyWhatTheFullExtractionReports(string set, string name)
    {
        var compilation = Set(set).Compile(name);
        var full = Extractor.Extract(compilation, ActiveConfiguration);
        var diagnoser = new Diagnoser(compilation);

        var reported = diagnoser.Members().SelectMany(m => diagnoser.Member(m))
            .Concat(diagnoser.ClosedTypes().SelectMany(t => diagnoser.ClosedType(t)))
            .Concat(diagnoser.UnnamedClosedValues())
            .ToHashSet();

        Assert.Equal(full.Diagnostics.ToHashSet(), reported);
        Assert.Equal(full.Diagnostics.Where(d => d.Id == DiagnosticIds.UnnamedClosedValue), diagnoser.UnnamedClosedValues());
    }

    [Fact]
    public void AnUnsupportedConstructIsReportedWhileAnotherMemberDoesNotCompile()
    {
        var compilation = Compile("""
            using Warrant;
            public static class S
            {
                [Verified] public static int Half(int x) => x << 1;
                [Verified] public static int Fine(int x) => x + 1;
                public static int Broken() => undefinedName;
            }
            """);
        var diagnoser = new Diagnoser(compilation);

        // A full extraction reports only the compiler's error; the diagnoser checks members without asking for it.
        Assert.True(Extractor.Extract(compilation, ActiveConfiguration).HasCompileErrors);
        var half = diagnoser.Members().Single(m => m.Name == "Half");
        var diagnostic = Assert.Single(diagnoser.Member(half));
        Assert.Equal(DiagnosticIds.Unsupported, diagnostic.Id);
        Assert.Equal("shift", diagnostic.Construct);
        Assert.Empty(diagnoser.Member(diagnoser.Members().Single(m => m.Name == "Fine")));
    }

    [Fact]
    public void AMemberWithItsOwnCompileErrorGetsNoDiagnosticsAndADependentIsStillChecked()
    {
        var compilation = Compile("""
            using Warrant;
            public static class S
            {
                [Verified] public static int Bad(int x) => x / undefinedName;
                [Verified] public static int Caller(int x) => x & 3;
            }
            """);
        var diagnoser = new Diagnoser(compilation);

        Assert.Empty(diagnoser.Member(diagnoser.Members().Single(m => m.Name == "Bad")));
        Assert.Equal("integer bitwise operator", Assert.Single(diagnoser.Member(diagnoser.Members().Single(m => m.Name == "Caller"))).Construct);
    }

    [Fact]
    public void MutualRecursionAndRejectedDependenciesAreFoundThroughTheClosure()
    {
        var compilation = Compile("""
            using Warrant;
            public static class S
            {
                [Verified] public static int Even(int n) { Spec.Decreases(n); return n <= 0 ? 1 : Odd(n - 1); }
                [Verified] public static int Odd(int n) { Spec.Decreases(n); return n <= 0 ? 0 : Even(n - 1); }
                [Verified] public static int UsesHalf(int x) => Half(x) + 1;
                [Verified] public static int Half(int x) => x << 1;
            }
            """);
        var diagnoser = new Diagnoser(compilation);
        var full = Extractor.Extract(compilation, ActiveConfiguration);

        foreach (var member in diagnoser.Members())
        {
            var key = Diagnoser.Key(member);
            Assert.Equal(full.Diagnostics.Where(d => d.MemberKey == key), diagnoser.Member(member).Where(d => d.MemberKey == key));
        }
        Assert.Equal("mutual recursion", Assert.Single(diagnoser.Member(diagnoser.Members().Single(m => m.Name == "Even"))).Construct);
        Assert.Equal("depends on a rejected unit", Assert.Single(diagnoser.Member(diagnoser.Members().Single(m => m.Name == "UsesHalf"))).Construct);
    }

    [Fact]
    public void ConcurrentQueriesOnOneDiagnoserGiveTheSequentialAnswers()
    {
        var compilation = CorpusSet.M4.Compile(CorpusSet.M4.Names.First(n => n.Contains("rejected", StringComparison.Ordinal)));
        var sequential = new Diagnoser(compilation);
        var expected = sequential.Members().Select(m => string.Join("\n", sequential.Member(m))).ToList();

        for (int round = 0; round < 5; round++)
        {
            var shared = new Diagnoser(compilation);
            var members = shared.Members().ToList();
            var actual = new string[members.Count];
            Parallel.For(0, members.Count * 4, new ParallelOptions { MaxDegreeOfParallelism = 8 }, i =>
            {
                var text = string.Join("\n", shared.Member(members[i % members.Count]));
                if (i < members.Count)
                {
                    actual[i] = text;
                }
                else
                {
                    Assert.Equal(expected[i % members.Count], text);
                }
            });
            Assert.Equal(expected, actual);
        }
    }

    private static CSharpCompilation Compile(string source)
    {
        var root = Path.Combine(Path.GetTempPath(), "warrant-diagnose-" + Guid.NewGuid().ToString("N")[..12]);
        Directory.CreateDirectory(root);
        try
        {
            File.WriteAllText(Path.Combine(root, "S.cs"), source);
            return CompilationFactory.FromFiles(root, ["S.cs"], checkOverflow: false);
        }
        finally
        {
            Directory.Delete(root, recursive: true);
        }
    }
}
