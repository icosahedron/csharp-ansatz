extern alias analyzers;

using System.Reflection.Metadata;
using System.Reflection.PortableExecutable;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using ExtractionOptions = analyzers::Warrant.Extraction.ExtractionOptions;
using ExtractionSeverity = analyzers::Warrant.Extraction.ExtractionSeverity;
using Extractor = analyzers::Warrant.Extraction.Extractor;

namespace Warrant.Analyzers.Tests;

/// <summary>
/// The M6 contract surface (plan U5, KTD8, KTD16) compiles against the netstandard2.0 package under this project's Roslyn,
/// leaves no call in the IL unless <c>WARRANT_CONTRACTS</c> is defined, and is read by the analyzer as extraction reads it
/// (U8), with every contract diagnostic the build reports. This file runs under Roslyn 5.9 and, linked into
/// Warrant.Analyzers.Tests.Roslyn48, under 4.8.
/// </summary>
public sealed class ContractSurfaceTests
{
    private const string Source = """
        using System.Threading.Tasks;
        using Warrant;

        namespace Sample;

        public interface IStore
        {
            int Get(int id);
            void Save(int value);
            Task<int> Load(int id);
        }

        [ContractFor(typeof(IStore))]
        internal abstract class StoreContract : IStore
        {
            public int Get(int id) { Spec.Requires(id > 0); Spec.Ensures<int>(r => r >= 0); return default!; }
            public void Save(int value) { Spec.Requires(value > 0); Spec.Ensures(() => true); }
            public Task<int> Load(int id) => default!;
        }

        public static class Rules
        {
            [Verified]
            public static int Clamp(int x)
            {
                Spec.Requires(x >= 0);
                Spec.Ensures<int>(r => r <= x);
                Spec.Assert(x >= 0, Tactic.VcGen());
                return x;
            }

            [ProofFor(nameof(Clamp))]
            static Proof ClampProof() => Prove.Contract().By(Tactic.Omega());

            public static async Task<int> Twice(IStore store)
            {
                Spec.Ensures<int>(r => r >= 0);
                return await store.Load(1);
            }
        }
        """;

    /// <summary>The members whose calls the compiler removes without <c>WARRANT_CONTRACTS</c>.</summary>
    private static readonly string[] Conditional = ["Requires", "Ensures", "Assert"];

    [Fact]
    public void WithoutWarrantContractsNoSpecCallIsInTheIl()
    {
        var names = MemberReferences(Emit(defineContracts: false));

        Assert.DoesNotContain(names, n => n.Type == "Spec" && Conditional.Contains(n.Member));
        // The arguments go with the call: Spec.Assert's script is not built either.
        Assert.DoesNotContain(("Tactic", "VcGen"), names);
        // The proof method is ordinary code the compiler keeps; Warrant never runs it.
        Assert.Contains(("Prove", "Contract"), names);
        Assert.Contains(("Tactic", "Omega"), names);
    }

    [Fact]
    public void WithWarrantContractsTheCallsAreKept()
    {
        var names = MemberReferences(Emit(defineContracts: true));

        Assert.All(Conditional, m => Assert.Contains(("Spec", m), names));
        Assert.Contains(("Tactic", "VcGen"), names);
    }

    [Fact]
    public async Task AContractAndItsProofForMethodInVerifiedCodeAreAccepted()
    {
        var compilation = AnalyzerHarness.Compile(("Rules.cs", Source));
        Assert.Empty(compilation.GetDiagnostics().Where(d => d.Severity == DiagnosticSeverity.Error));

        var (lines, exceptions) = await AnalyzerHarness.Run(compilation);

        Assert.Empty(exceptions);
        // The contract class is not read until M6 U18, and the async method is not verified.
        Assert.Empty(lines);
    }

    /// <summary>One member per contract diagnostic of U8 (KTD8, KTD11, KTD16), in C# 12 so Roslyn 4.8 reads it.</summary>
    private const string Rejected = """
        using System;
        using Warrant;

        namespace Sample;

        public static class Rejected
        {
            [Verified]
            public static int EnsuresLate(int x)
            {
                var y = x;
                Spec.Ensures<int>(r => r == x);
                return y;
            }

            [Verified]
            public static int RequiresAfterEnsures(int x)
            {
                Spec.Ensures<int>(r => r == x);
                Spec.Requires(x > 0);
                return x;
            }

            [Verified]
            public static int Countdown(int n)
            {
                Spec.Decreases(n);
                Spec.Requires(n >= 0);
                return n <= 0 ? 0 : Countdown(n - 1);
            }

            [Verified]
            public static int Descend(int n)
            {
                Spec.Decreases(n);
                if (n < 0) throw new ArgumentException("negative");
                return n == 0 ? 0 : Descend(n - 1);
            }

            [Verified]
            public static int Widened(int x)
            {
                Spec.Ensures<long>(r => r >= 0);
                return x;
            }

            [Verified]
            public static int NoResult(int x)
            {
                Spec.Ensures(() => x >= 0);
                return x;
            }

            [Verified] public static int Scale(int x, int d) => x / d;

            [Verified]
            public static int Scaled(int x, int d)
            {
                Spec.Ensures<int>(r => r == Scale(x, d));
                return x / d;
            }

            [Theorem] static Proof ScaleIsSmall(int x) => Prove.That(Scale(x, 2) <= x);
            [Theorem] static Proof RatioAtMost(int x, int y) => Prove.That(x / y <= x);

            [ProofFor("Missing")]
            static Proof MissingProof() => Prove.Contract().By(Tactic.Omega());

            [Verified] public static int Kept(int x) { Spec.Ensures<int>(r => r == x); return x; }

            [ProofFor(nameof(Kept))]
            static Proof KeptProof() => Prove.Contract().By(Tactic.Omega());

            [ProofFor(nameof(Kept))]
            static Proof KeptAgain() => Prove.Contract();

            [Verified] public static int Twin(int x) => x;
            [Verified] public static long Twin(long x) => x;

            [ProofFor(nameof(Twin))]
            static Proof TwinProof() => Prove.Contract().By(Tactic.Omega());
        }
        """;

    [Fact]
    public async Task TheAnalyzerReportsEachContractDiagnosticAsTheBuildDoes()
    {
        var compilation = AnalyzerHarness.Compile(("Rejected.cs", Rejected));
        Assert.Empty(compilation.GetDiagnostics().Where(d => d.Severity == DiagnosticSeverity.Error));
        var extraction = Extractor.Extract(compilation, new ExtractionOptions { BuildDefines = true });
        var expected = extraction.Diagnostics
            .Select(d => AnalyzerHarness.Line(
                d.Location!.Path, d.Location.StartLine, d.Location.StartColumn, d.Location.EndLine, d.Location.EndColumn,
                d.Severity == ExtractionSeverity.Warning ? "warning" : "error", d.Id, d.Message))
            .Order(StringComparer.Ordinal)
            .ToList();

        var (lines, exceptions) = await AnalyzerHarness.Run(compilation);

        Assert.Empty(exceptions);
        Assert.Equal(expected, lines.Order(StringComparer.Ordinal).ToList());
        Assert.Equal(
            [
                "WRT0002 | Spec.Ensures not leading the body",
                "WRT0002 | Spec.Requires after Spec.Ensures",
                "WRT0002 | contract on a recursive method",
                "WRT0002 | recursion with effects",
                "WRT0002 | Spec.Ensures type argument that is not the return type",
                "WRT0002 | Spec.Ensures without the result",
                "WRT0002 | Spec expression calling a raising method",
                "WRT0002 | theorem calling a raising method",
                "WRT0002 | division",
                "WRT0002 | [ProofFor] naming no method",
                "WRT0002 | second [ProofFor] for a method",
                "WRT0002 | [ProofFor] of an overloaded method",
            ],
            extraction.Diagnostics.Select(d => d.Id + " | " + d.Construct));
    }

    private static byte[] Emit(bool defineContracts)
    {
        var compilation = AnalyzerHarness.Compile(("Rules.cs", Source));
        var parse = new CSharpParseOptions(LanguageVersion.CSharp12, preprocessorSymbols: defineContracts ? ["WARRANT_CONTRACTS"] : []);
        compilation = compilation.ReplaceSyntaxTree(compilation.SyntaxTrees.Single(), CSharpSyntaxTree.ParseText(Source, parse, "Rules.cs"));
        using var stream = new MemoryStream();
        var result = compilation.Emit(stream);
        Assert.True(result.Success, string.Join("\n", result.Diagnostics));
        return stream.ToArray();
    }

    /// <summary>The (type, member) names of every member reference in an assembly, which is how its IL names a call into Warrant.</summary>
    private static List<(string Type, string Member)> MemberReferences(byte[] image)
    {
        using var pe = new PEReader(new MemoryStream(image));
        var reader = pe.GetMetadataReader();
        var result = new List<(string, string)>();
        foreach (var handle in reader.MemberReferences)
        {
            var reference = reader.GetMemberReference(handle);
            var parent = reference.Parent;
            if (parent.Kind == HandleKind.TypeReference)
            {
                var type = reader.GetTypeReference((TypeReferenceHandle)parent);
                result.Add((reader.GetString(type.Name), reader.GetString(reference.Name)));
            }
        }
        return result;
    }
}
