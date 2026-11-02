using Warrant.Cic;
using Warrant.Lean4Export;

namespace Warrant.Kernel.Tests;

/// <summary>
/// The Warrant side of the cross-kernel harness (<c>scripts/cross-check.sh</c>): declarations built
/// in C# must be admitted, and can be written out for Lean's kernel to re-check.
/// </summary>
public class CrossCheckTests(InitMediumFixture initMedium) : IClassFixture<InitMediumFixture>
{
    private static Name N(string s) => Name.Parse(s);

    private KernelEnvironment AdmitFixtures()
    {
        var env = Copy(initMedium.Env);
        KernelThread.Run(() =>
        {
            foreach (var d in CrossCheckFixtures.Build())
            {
                Kernel.Add(env, d);
            }
        });
        return env;
    }

    private static KernelEnvironment Copy(KernelEnvironment source)
    {
        var env = new KernelEnvironment();
        foreach (var c in source.Constants)
        {
            env.AddCore(c);
        }
        if (source.IsQuotInitialized)
        {
            env.MarkQuotInitialized();
        }
        return env;
    }

    [Fact]
    public void FixturesAreAdmittedWithTheExpectedRecursors()
    {
        var env = AdmitFixtures();

        var treeRec = (RecursorInfo)env.Get(N("test.Tree.rec"));
        Assert.Equal([N("u")], treeRec.LevelParams);
        Assert.Equal((1, 2, 2), (treeRec.NumMotives, treeRec.NumMinors, treeRec.Rules.Count));

        var evenRec = (RecursorInfo)env.Get(N("test.Even.rec"));
        Assert.Equal((2, 3), (evenRec.NumMotives, evenRec.NumMinors));
        Assert.Empty(evenRec.LevelParams); // mutual predicates eliminate only into Prop
        Assert.NotNull(env.Find(N("test.Odd.rec")));

        // Nested through List: an auxiliary recursor for the List Rose occurrence.
        var roseRec = (RecursorInfo)env.Get(N("test.Rose.rec"));
        Assert.Equal(2, roseRec.NumMotives);
        Assert.IsType<RecursorInfo>(env.Get(N("test.Rose.rec_1")));
        Assert.Equal(1, ((InductiveInfo)env.Get(N("test.Rose"))).NumNested);

        var boxRec = (RecursorInfo)env.Get(N("test.Box.rec"));
        Assert.Equal([N("u_1"), N("u")], boxRec.LevelParams); // `u` is taken, so the motive universe is u_1

        Assert.True(((RecursorInfo)env.Get(N("test.IsZero.rec"))).K);
        Assert.False(treeRec.K);
    }

    /// <summary>
    /// Writes init-medium followed by the fixtures (as Warrant's kernel generated them) for
    /// <c>lean-replay</c>. Run by <c>scripts/cross-check.sh</c>.
    /// </summary>
    [FactRequiringEnv("WARRANT_CROSSCHECK_OUT")]
    public void WritesFixturesForLean()
    {
        var path = Environment.GetEnvironmentVariable("WARRANT_CROSSCHECK_OUT")!;
        var env = AdmitFixtures();
        var source = Lean4Export.Lean4Export.ReadFile(Corpus.Path("init-medium.ndjson.gz"));
        using var writer = new Lean4ExportWriter(File.Create(path), source.Metadata);
        writer.WriteAll(source.Declarations);
        foreach (var d in CrossCheckFixtures.Build())
        {
            writer.Write(CrossCheckFixtures.AdmittedForm(env, d));
        }
    }
}
