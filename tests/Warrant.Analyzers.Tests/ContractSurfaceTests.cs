using System.Reflection.Metadata;
using System.Reflection.PortableExecutable;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;

namespace Warrant.Analyzers.Tests;

/// <summary>
/// The M6 contract surface (plan U5, KTD8, KTD16) compiles against the netstandard2.0 package under this project's Roslyn,
/// leaves no call in the IL unless <c>WARRANT_CONTRACTS</c> is defined, and is still rejected in verified code until
/// extraction reads it (U8). This file runs under Roslyn 5.9 and, linked into Warrant.Analyzers.Tests.Roslyn48, under 4.8.
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
    public async Task AContractInVerifiedCodeIsRejectedAsAnUnverifiedCallUntilExtractionReadsIt()
    {
        var compilation = AnalyzerHarness.Compile(("Rules.cs", Source));
        Assert.Empty(compilation.GetDiagnostics().Where(d => d.Severity == DiagnosticSeverity.Error));

        var (lines, exceptions) = await AnalyzerHarness.Run(compilation);

        Assert.Empty(exceptions);
        // Only the [Verified] method is reported, at its first Spec call; the contract class and the proof method are not read yet.
        Assert.Matches(@"^Rules\.cs\(26,9,26,30\): error WRT0005: Verified code may call only verified or modelled members, not .*Spec\.Requires", Assert.Single(lines));
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
