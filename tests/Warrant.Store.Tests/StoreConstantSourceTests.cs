using Warrant.Cic;
using Warrant.Kernel;

namespace Warrant.Store.Tests;

/// <summary>
/// A store as the kernel's lazy base (M5b U12, KTD18): the <c>Warrant</c> library's declarations check against a trusted
/// store of their Init closure, which decodes only the records they use, from many threads at once.
/// </summary>
public sealed class StoreConstantSourceTests : IDisposable
{
    private readonly TempDirectory _temp = new();

    public void Dispose() => _temp.Dispose();

    private (StoreReader Reader, StoreConstantSource Source) OpenClosure()
    {
        var store = _temp.Sub("closure");
        if (!Directory.Exists(store))
        {
            Stores.Write(store, Stores.Bundle.Where(d => !Stores.IsWarrants(d)));
        }
        var reader = StoreReader.Open(store);
        return (reader, new StoreConstantSource(reader));
    }

    [Fact]
    public void TheWarrantLibraryChecksAgainstALazyStoreOfItsClosureWhichDecodesOnlyWhatItUses()
    {
        var (reader, source) = OpenClosure();
        using (reader)
        {
            var env = new KernelEnvironment(source);
            var own = Stores.Bundle.Where(Stores.IsWarrants).ToList();
            Assert.NotEmpty(own);
            Assert.True(env.IsQuotInitialized);

            var results = new ExportChecker(env).CheckAll(own);

            Assert.All(results, r => Assert.True(r.Accepted, $"{r.Name}: {r.Error}"));
            Assert.Equal(source.Count + own.Sum(d => d.Constants.Count), env.Count);
            int closure = reader.Manifest.Declarations;
            Assert.InRange(source.MaterializedRecords, 1, closure - 1);
        }
    }

    [Fact]
    public void ADeclarationWhoseDependencyIsNotInTheStoreIsRejectedAsUnknown()
    {
        var (reader, source) = OpenClosure();
        using (reader)
        {
            var env = new KernelEnvironment(source);
            var axiom = new ConstantDeclaration(new AxiomInfo(Name.From("Test", "a"), EquatableArray<Name>.Empty,
                Expr.Const(Name.From("Warrant", "Int32")), false));

            var result = Assert.Single(new ExportChecker(env).CheckAll([axiom]));

            Assert.False(result.Accepted);
            Assert.Contains("unknown constant 'Warrant.Int32'", result.Error, StringComparison.Ordinal);
        }
    }

    [Fact]
    public void EightThreadsCheckingAgainstOneFrozenStoreGiveTheSequentialVerdicts()
    {
        // Theorems of the closure, re-declared under new names: each true one with its own proof, each false one with the
        // next theorem's proof.
        var theorems = Stores.Bundle.Where(d => !Stores.IsWarrants(d)).Select(d => d.Constants[0]).OfType<TheoremInfo>().Take(64).ToList();
        var checks = theorems.SelectMany((t, i) => new[]
        {
            new TheoremInfo(Name.From("Check", "good").Append((ulong)i), t.LevelParams, t.Type, t.Proof, EquatableArray<Name>.Empty),
            new TheoremInfo(Name.From("Check", "bad").Append((ulong)i), t.LevelParams, t.Type, theorems[(i + 1) % theorems.Count].Proof, EquatableArray<Name>.Empty),
        }).ToList();

        List<bool> Verdicts(int threads)
        {
            var (reader, source) = OpenClosure();
            using (reader)
            {
                var env = new KernelEnvironment(source);
                env.Freeze();
                var verdicts = new bool[checks.Count];
                var work = Enumerable.Range(0, threads).Select(t => Task.Run(() => KernelThread.Run(() =>
                {
                    for (int i = t; i < checks.Count; i += threads)
                    {
                        try
                        {
                            Warrant.Kernel.Kernel.Add(env.Fork(), new TheoremDecl(checks[i]));
                            verdicts[i] = true;
                        }
                        catch (KernelException)
                        {
                            verdicts[i] = false;
                        }
                    }
                }))).ToArray();
                Task.WaitAll(work);
                return [.. verdicts];
            }
        }

        var sequential = Verdicts(1);
        var parallel = Verdicts(8);

        Assert.Equal(sequential, parallel);
        Assert.All(Enumerable.Range(0, theorems.Count), i => Assert.True(sequential[2 * i], $"{theorems[i].Name} was rejected"));
        // A swapped proof can prove the same statement only by accident; nearly every one is rejected.
        Assert.True(sequential.Where((_, i) => i % 2 == 1).Count(v => !v) > theorems.Count / 2);
    }
}
