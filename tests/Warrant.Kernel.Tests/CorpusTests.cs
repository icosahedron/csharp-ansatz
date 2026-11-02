using Warrant.Cic;

namespace Warrant.Kernel.Tests;

/// <summary>The kernel's verdicts on the export corpus must match Lean's.</summary>
public class CorpusTests(InitMediumFixture initMedium) : IClassFixture<InitMediumFixture>
{
    [Fact]
    public void AcceptsAllOfInitMedium()
    {
        var rejected = initMedium.Results.Where(r => !r.Accepted).Select(r => $"{r.Name}: {r.Error}").ToList();
        Assert.Empty(rejected);
        Assert.Equal(4631, initMedium.Results.Count);
        Assert.Equal(5118, initMedium.Env.Count);
        Assert.True(initMedium.Env.IsQuotInitialized);
    }

    /// <summary>
    /// The full Init library (≈58k declarations, a 348 MB export, too large to commit). Produce it
    /// with <c>scripts/export-lean-library.sh</c> and point <c>WARRANT_INIT_EXPORT</c> at it.
    /// </summary>
    [FactRequiringEnv("WARRANT_INIT_EXPORT")]
    public void AcceptsFullInit()
    {
        var path = Environment.GetEnvironmentVariable("WARRANT_INIT_EXPORT")!;
        var (env, results) = Corpus.CheckAll(Lean4Export.Lean4Export.ReadFile(path).Declarations);
        var rejected = results.Where(r => !r.Accepted).Take(20).Select(r => $"{r.Name}: {r.Error}").ToList();
        Assert.Empty(rejected);
        Assert.True(env.Count > 50_000, $"only {env.Count} constants");
    }

    [Fact]
    public void AcceptsNatAddSucc()
    {
        var (env, results) = Corpus.CheckAll(Corpus.Read("Nat.add_succ.ndjson"));
        Assert.All(results, r => Assert.True(r.Accepted, $"{r.Name}: {r.Error}"));
        Assert.Equal(32, env.Count);
    }

    /// <summary>
    /// lean-kernel-arena cases, with the declarations Lean's kernel rejects. For the two
    /// <c>*-of-subst-prop</c> exploits (Lean issues #14807/#14847), any declaration inside the
    /// exploit may be the first rejected; nothing in the Init closure may be.
    /// </summary>
    [Theory]
    [InlineData("arena/001_basicDef.ndjson", "")]
    [InlineData("arena/sparse-name-index.ndjson", "")]
    [InlineData("arena/002_badDef.ndjson", "badDef")]
    [InlineData("arena/141_falseFromUnsafe.ndjson", "falseFromUnsafe")]
    [InlineData("arena/proj-of-subst-prop.ndjson", "PR14806Subst.observe")]
    [InlineData("arena/rec-of-subst-prop.ndjson", "Issue.forallFalse")]
    public void ArenaVerdicts(string file, string expectedRejected)
    {
        var (_, results) = Corpus.CheckAll(Corpus.Read(file));
        var rejected = results.Where(r => !r.Accepted).Select(r => r.Name.ToString()).ToList();
        if (expectedRejected.Length == 0)
        {
            Assert.Empty(rejected);
        }
        else
        {
            Assert.Equal(expectedRejected, rejected.FirstOrDefault());
            Assert.All(results.Where(r => !r.Accepted), r => Assert.False(r.ResourceLimit));
        }
    }

    [Fact]
    public void UnsafeDefinitionIsAcceptedButSafeUseIsNot()
    {
        // Lean admits `unsafeLoop` (unsafe recursion is allowed) and rejects the safe theorem using it.
        var (env, results) = Corpus.CheckAll(Corpus.Read("arena/141_falseFromUnsafe.ndjson"));
        Assert.True(results.Single(r => r.Name == Name.Parse("unsafeLoop")).Accepted);
        Assert.Contains("unsafe declaration 'unsafeLoop'", results.Single(r => r.Name == Name.Parse("falseFromUnsafe")).Error, StringComparison.Ordinal);
        Assert.Null(env.Find(Name.Parse("falseFromUnsafe")));
    }

    [Fact]
    public void FuelExhaustionIsAResourceLimitNotARejection()
    {
        var decls = initMedium.Declarations.Take(200).ToList();
        var (_, results) = Corpus.CheckAll(decls, new KernelLimits(Fuel: 50, MaxNatBytes: 1 << 20));
        Assert.Contains(results, r => !r.Accepted);
        Assert.All(results.Where(r => !r.Accepted && r.Error!.Contains("fuel", StringComparison.Ordinal)), r => Assert.True(r.ResourceLimit));
        Assert.Contains(results, r => r.ResourceLimit);
    }

    [Fact]
    public void CheckingIsDeterministic()
    {
        var decls = Corpus.Read("Nat.add_succ.ndjson");
        var a = Corpus.CheckAll(decls).Results.Select(r => (r.Name, r.Accepted)).ToList();
        var b = Corpus.CheckAll(decls).Results.Select(r => (r.Name, r.Accepted)).ToList();
        Assert.Equal(a, b);
    }
}
