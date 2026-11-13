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
                Spec.NoThrow();
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
    private static readonly string[] Conditional = ["Requires", "NoThrow", "Ensures", "Assert"];

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
        // The contract class has the contract shape (M6 U18), and the async method is not verified.
        Assert.Empty(lines);
    }

    /// <summary>
    /// One member or class per diagnostic of U18 (KTD9, KTD10, KTD22), and the payment example of design §5.2, which the
    /// analyzer accepts as the build does. C# 12, so Roslyn 4.8 reads it.
    /// </summary>
    private const string Dependencies = """
        #nullable enable
        using System.Threading.Tasks;
        using Warrant;

        namespace Sample;

        public enum Result { Success, InvalidId, NotFound }

        public sealed record Payment(int Id, decimal Amount);

        public interface IPaymentStore
        {
            Task<Payment?> GetPayment(int id);
            Task SavePayment(Payment p);
            int Size { get; }
        }

        public interface IClock { int Now(); }
        public interface IBox<T> { int Get(); }
        public interface IShaky { int Get(); }

        [ContractFor(typeof(IPaymentStore))]
        file abstract class PaymentStoreContract : IPaymentStore
        {
            public Task<Payment?> GetPayment(int id)
            {
                Spec.Ensures<Payment?>(r => r is null || r.Id == id);
                return default!;
            }

            public Task SavePayment(Payment p) => default!;

            public abstract int Size { get; }
        }

        [ContractFor(typeof(IPaymentStore))]
        internal abstract class Twin : IPaymentStore
        {
            public abstract Task<Payment?> GetPayment(int id);
            public abstract Task SavePayment(Payment p);
            public abstract int Size { get; }
        }

        [ContractFor(typeof(IShaky))]
        internal class ShakyContract : IShaky { public int Get() => default!; }

        public abstract class Base { protected readonly IPaymentStore inherited = null!; }

        public sealed class PaymentService(IPaymentStore store, IClock clock, IBox<int> box, IShaky shaky) : Base
        {
            private IPaymentStore mutable = store;
            private readonly int limit = 3;

            [Verified]
            public async Task<Result> ProcessPayment(int paymentId)
            {
                Spec.Ensures<Result>(r => r != Result.Success || paymentId > 0);
                if (paymentId <= 0) return Result.InvalidId;
                var payment = await store.GetPayment(paymentId);
                if (payment is null) return Result.NotFound;
                await store.SavePayment(payment with { Amount = 0m });
                return Result.Success;
            }

            [Verified] public int Mutable() => mutable.Size;
            [Verified] public int Inherited(int id) => inherited.GetPayment(id) == null ? 0 : 1;
            [Verified] public int Clock() => clock.Now();
            [Verified] public int Box() => box.Get();
            [Verified] public int Shaky() => shaky.Get();
            [Verified] public int Limit(int x) => x + limit;
            [Verified] public int Tested(int x) => store == null ? 0 : x;
            [Verified] public int Sized() => store.Size;
            [Verified] public async Task Discarded(Payment p) { _ = store.SavePayment(p); await store.SavePayment(p); }
            [Verified] public async Task<int> Configured(int id) => await store.GetPayment(id).ConfigureAwait(false) is null ? 0 : 1;
            [Verified] public async Task<int> Delayed(int id) { await Task.Delay(1); return id; }
            [Verified] public async void Fire(Payment p) => await store.SavePayment(p);
            [Verified] public async Task Early(Payment p, System.Threading.CancellationToken ct) { var t = ct; await store.SavePayment(p); }

            [Verified]
            public int InClaim(int x)
            {
                Spec.Ensures<int>(r => store.GetPayment(x) != null);
                return x;
            }
        }

        public sealed class Reassigned(IPaymentStore store)
        {
            public void Reset() => store = null!;

            [Verified] public async Task<int> Find(int id) => await store.GetPayment(id) is null ? 0 : 1;
        }
        """;

    [Fact]
    public async Task TheAnalyzerReportsEachDependencyAndContractClassDiagnosticAsTheBuildDoes()
    {
        var compilation = AnalyzerHarness.Compile(("Dependencies.cs", Dependencies));
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
        Assert.NotNull(extraction.Find("M:Sample.PaymentService.ProcessPayment(System.Int32)"));
        Assert.Equal(
            [
                "WRT0002 | second contract class for an interface",
                "WRT0002 | contract class that is not abstract",
                "WRT0002 | mutable dependency field",
                "WRT0002 | inherited dependency",
                "WRT0002 | dependency without a contract class",
                "WRT0002 | generic interface dependency",
                "WRT0002 | dependency whose contract class is rejected",
                "WRT0002 | member access on this",
                "WRT0002 | dependency used other than to call a member",
                "WRT0002 | property of a dependency",
                "WRT0002 | Task-returning call that is not awaited",
                "WRT0002 | ConfigureAwait",
                "WRT0002 | Task combinator",
                "WRT0002 | async void method",
                "WRT0002 | cancellation token other than a parameter",
                "WRT0002 | dependency call in a Spec expression",
                "WRT0002 | assigned primary-constructor parameter",
            ],
            extraction.Diagnostics.Select(d => d.Id + " | " + d.Construct));
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

            [Verified]
            public static int Idle(int x)
            {
                Spec.NoThrow();
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
                "WRT0013 | Spec.NoThrow on a method that cannot raise",
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
