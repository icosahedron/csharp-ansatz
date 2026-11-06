using Warrant.Cic;
using Warrant.Engine.Service;
using Warrant.Kernel;
using Warrant.Lean4Export;

namespace Warrant.Engine.Tests;

/// <summary>
/// Per-unit certificates and the toolchain identity (plan M5b U4, KTD9, KTD14): each outcome's admitted declarations,
/// written on their own as lean4export NDJSON and read back against the bundle and the unit's callees.
/// </summary>
public sealed class CertificateTests(EngineFixture engine) : IClassFixture<EngineFixture>
{
    private const string Corpus = "m5a/accepted";
    private const string ValidImpliesPositive = "M:Claims.Payments.ValidImpliesPositive(Claims.Payment)";
    private const string RankIsSmall = "M:Corpus.Quantifiers.RankIsSmall(Corpus.Light)";

    [Fact]
    public void EveryAcceptedUnitAdmitsItsOwnDeclarations()
    {
        var result = engine.Run(Corpus);
        Assert.All(result.Units, u => Assert.True(u is TranslatedOutcome or ProvedOutcome, $"{u.Key}: {u}"));
        Assert.All(result.Units, u => Assert.NotEmpty(u.Declarations));

        // A theorem's certificate is its theorem; a record's holds its inductive, casesOn, ctorIdx and equality; a recursive method's
        // its decrease theorem, the definition and the equation lemma.
        var proved = Assert.IsType<ProvedOutcome>(result.Find(ValidImpliesPositive));
        Assert.Same(proved.Certificate, Assert.Single(proved.Declarations));
        Assert.Equal(
            ["Cs.Claims.Payment", "Cs.Claims.Payment.casesOn", "Cs.Claims.Payment.ctorIdx", "Cs.Claims.Payment.$eq"],
            result.Find("T:Claims.Payment")!.Declarations.Select(FirstName));
        Assert.Equal(
            ["Cs.Corpus.Recursion.«Sum(System.Int32)».$dec_1", "Cs.Corpus.Recursion.«Sum(System.Int32)»", "Cs.Corpus.Recursion.«Sum(System.Int32)».$eq_def"],
            result.Find("M:Corpus.Recursion.Sum(System.Int32)")!.Declarations.Select(FirstName));
    }

    [Fact]
    public void AProvedTheoremsCertificateChecksInAForkOfTheBundleWithItsCalleesCertificates()
    {
        var result = engine.Run(Corpus);
        var callees = Closure(ValidImpliesPositive);
        Assert.Contains("M:Claims.Payments.Validate(Claims.Payment)", callees);
        Assert.Contains("T:Claims.Payment", callees);

        var checker = new ExportChecker(engine.Bundle.Env.Fork(), KernelLimits.Corpus);
        CheckCallees(checker, result, callees);
        var checks = checker.CheckAll(Certificates.Read(new MemoryStream(Certificate(result, ValidImpliesPositive))));

        var check = Assert.Single(checks);
        Assert.True(check.Accepted, check.Error);
        Assert.Equal("Cs.Claims.Payments.«ValidImpliesPositive(Claims.Payment)»", check.Name.ToString());
    }

    [Fact]
    public void ACertificateNamesItsCalleesWithoutIncludingThem()
    {
        var result = engine.Run(Corpus);
        var declarations = Certificates.Read(new MemoryStream(Certificate(result, ValidImpliesPositive)));
        Assert.Equal(["Cs.Claims.Payments.«ValidImpliesPositive(Claims.Payment)»"], declarations.Select(d => d.Constants[0].Name.ToString()));

        // Without its callees in the environment, the kernel cannot check it.
        var check = Assert.Single(new ExportChecker(engine.Bundle.Env.Fork(), KernelLimits.Corpus).CheckAll(declarations));
        Assert.False(check.Accepted);
    }

    [Fact]
    public void TheBundleAndEveryUnitCertificateAreWhatVerifyOutWrites()
    {
        var result = engine.Run(Corpus);
        using var whole = new MemoryStream();
        result.WriteNdjson(whole);
        whole.Position = 0;
        var expected = ReadAll(whole);

        using var bundle = new MemoryStream();
        using (var writer = new Lean4ExportWriter(bundle, result.Bundle.Metadata, leaveOpen: true))
        {
            writer.WriteAll(result.Bundle.Declarations);
        }
        bundle.Position = 0;
        var actual = ReadAll(bundle);
        foreach (var unit in result.Units)
        {
            actual.AddRange(Certificates.Read(new MemoryStream(Certificate(result, unit.Key))));
        }

        Assert.Equal(expected.Count, actual.Count);
        Assert.True(expected.ToHashSet().SetEquals(actual), "the bundle and the unit certificates differ from verify --out");
    }

    [Fact]
    public void ACertificateWithAnotherTheoremsProofIsRejected()
    {
        var result = engine.Run(Corpus);
        var callees = Closure(ValidImpliesPositive).Union(Closure(RankIsSmall)).ToHashSet(StringComparer.Ordinal);
        var other = Assert.IsType<ProvedOutcome>(result.Find(RankIsSmall)).Certificate.Value;

        var genuine = Certificates.Read(new MemoryStream(Certificate(result, ValidImpliesPositive)));
        var theorem = (TheoremInfo)Assert.Single(genuine).Constants[0];
        Assert.NotEqual(theorem.Proof, other.Proof);
        using var stream = new MemoryStream();
        using (var writer = new Lean4ExportWriter(stream, result.Bundle.Metadata, leaveOpen: true))
        {
            writer.Write(new ConstantDeclaration(theorem with { Proof = other.Proof }));
        }
        stream.Position = 0;

        var checker = new ExportChecker(engine.Bundle.Env.Fork(), KernelLimits.Corpus);
        CheckCallees(checker, result, callees);
        var checks = checker.CheckAll(Certificates.Read(stream));

        var check = Assert.Single(checks);
        Assert.False(check.Accepted);
        Assert.False(check.ResourceLimit, check.Error);
        Assert.Null(checker.Env.Find(theorem.Name));
    }

    [Fact]
    public void TheToolchainIdentityHashesTheKtd9Assemblies()
    {
        Assert.Equal(
            ["Warrant.Cic", "Warrant.Kernel", "Warrant.Semantics", "Warrant.Meta", "Warrant.Engine", "Warrant.Vir", "Warrant.Lean4Export"],
            Toolchain.Assemblies.Select(a => a.GetName().Name));
        Assert.Matches("^[0-9a-f]{64}$", Toolchain.Identity);
        Assert.Equal(Toolchain.Identity, Toolchain.Identity);
        Assert.Equal(Toolchain.Identity, Toolchain.IdentityOf(Toolchain.Assemblies));
    }

    [Fact]
    public void ADifferentAssemblyListHasADifferentIdentity()
    {
        var withTests = Toolchain.Assemblies.Append(typeof(CertificateTests).Assembly).ToList();
        var withoutEngine = Toolchain.Assemblies.Where(a => a != typeof(Pipeline).Assembly).ToList();

        Assert.NotEqual(Toolchain.Identity, Toolchain.IdentityOf(withTests));
        Assert.NotEqual(Toolchain.Identity, Toolchain.IdentityOf(withoutEngine));
        Assert.NotEqual(Toolchain.IdentityOf(withTests), Toolchain.IdentityOf(withoutEngine));
    }

    private static string FirstName(KernelDeclaration declaration) => declaration switch
    {
        InductiveDecl i => i.Types[0].Name.ToString(),
        DefinitionDecl d => d.Value.Name.ToString(),
        TheoremDecl t => t.Value.Name.ToString(),
        _ => throw new InvalidOperationException(declaration.GetType().Name),
    };

    private static List<Declaration> ReadAll(Stream stream)
    {
        using var reader = new Lean4ExportReader(stream, leaveOpen: true);
        return [.. reader.ReadDeclarations()];
    }

    /// <summary>The unit's certificate, written as the cache will store it.</summary>
    private static byte[] Certificate(EngineResult result, string key)
    {
        using var stream = new MemoryStream();
        Certificates.Write(stream, result.Environment, result.Find(key)!.Declarations, result.Bundle.Metadata);
        return stream.ToArray();
    }

    /// <summary>The keys of the units a unit depends on, transitively, without the unit itself.</summary>
    private HashSet<string> Closure(string key)
    {
        var byKey = engine.Inputs(Corpus).ToDictionary(u => u.Unit.Key, u => u.Unit, StringComparer.Ordinal);
        var seen = new HashSet<string>(StringComparer.Ordinal);
        var work = new Stack<string>(byKey[key].Deps);
        while (work.TryPop(out var next))
        {
            if (seen.Add(next))
            {
                foreach (var dep in byKey[next].Deps)
                {
                    work.Push(dep);
                }
            }
        }
        return seen;
    }

    /// <summary>
    /// Checks the callees' certificates, each of which the kernel must accept, in the order the run admitted their first
    /// declaration, which is a dependency order.
    /// </summary>
    private static void CheckCallees(ExportChecker checker, EngineResult result, IEnumerable<string> callees)
    {
        foreach (var callee in callees.OrderBy(k => result.Admitted.IndexOf(result.Find(k)!.Declarations[0])))
        {
            var checks = checker.CheckAll(Certificates.Read(new MemoryStream(Certificate(result, callee))));
            Assert.All(checks, c => Assert.True(c.Accepted, $"{c.Name}: {c.Error}"));
        }
    }
}
