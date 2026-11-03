using Warrant.Cic;

namespace Warrant.Kernel.Tests;

/// <summary>Frozen environments and their overlay forks.</summary>
public class KernelEnvironmentTests(InitMediumFixture initMedium) : IClassFixture<InitMediumFixture>
{
    private static Name N(string s) => Name.Parse(s);

    /// <summary>An axiom <c>name : Prop</c>, admissible into any environment.</summary>
    private static AxiomDecl Axiom(string name) => new(new AxiomInfo(N(name), [], Expr.Prop, false));

    private static void Add(KernelEnvironment env, KernelDeclaration d) => KernelThread.Run(() => Kernel.Add(env, d));

    private static KernelEnvironment FrozenBase()
    {
        var env = new KernelEnvironment();
        Add(env, Axiom("test.base"));
        env.Freeze();
        return env;
    }

    [Fact]
    public void ADeclarationAddedToAForkIsAbsentFromTheBase()
    {
        var baseEnv = FrozenBase();
        var fork = baseEnv.Fork();
        Add(fork, Axiom("test.inFork"));

        Assert.NotNull(fork.Find(N("test.base")));
        Assert.NotNull(fork.Find(N("test.inFork")));
        Assert.Equal(2, fork.Count);
        Assert.Null(baseEnv.Find(N("test.inFork")));
        Assert.Equal(1, baseEnv.Count);
    }

    [Fact]
    public void AddingToAFrozenBaseFails()
    {
        var baseEnv = FrozenBase();
        Assert.True(baseEnv.IsFrozen);
        Assert.Throws<InvalidOperationException>(() => Add(baseEnv, Axiom("test.late")));
        Assert.Null(baseEnv.Find(N("test.late")));
        Assert.Equal(1, baseEnv.Count);
    }

    [Fact]
    public void OnlyAFrozenEnvironmentCanBeForked()
    {
        var env = new KernelEnvironment();
        Assert.False(env.IsFrozen);
        Assert.Throws<InvalidOperationException>(env.Fork);
    }

    [Fact]
    public void TwoForksOfOneBaseDoNotSeeEachOther()
    {
        var baseEnv = FrozenBase();
        var a = baseEnv.Fork();
        var b = baseEnv.Fork();
        Add(a, Axiom("test.a"));
        Add(b, Axiom("test.b"));

        Assert.NotNull(a.Find(N("test.a")));
        Assert.Null(a.Find(N("test.b")));
        Assert.NotNull(b.Find(N("test.b")));
        Assert.Null(b.Find(N("test.a")));

        Add(a, Axiom("test.shared"));
        Add(b, Axiom("test.shared"));
        Assert.Equal(3, a.Count);
        Assert.Equal(3, b.Count);
    }

    [Fact]
    public void AForkOfInitMediumAdmitsTheFixturesAsACopyDoes()
    {
        Assert.True(initMedium.Env.IsFrozen);
        var fork = initMedium.Env.Fork();
        var copy = Copy(initMedium.Env);
        var fixtures = CrossCheckFixtures.Build();
        foreach (var d in fixtures)
        {
            Add(fork, d);
            Add(copy, d);
        }

        Assert.Equal(copy.Count, fork.Count);
        Assert.Equal(5118, initMedium.Env.Count);
        foreach (var d in fixtures)
        {
            var admitted = AdmittedDeclarations.Of(fork, d);
            Assert.Equal(AdmittedDeclarations.Of(copy, d), admitted);
            if (d is InductiveDecl ind)
            {
                var typeNames = ind.Types.Select(t => t.Name).ToEquatableArray();
                var scanned = copy.Constants.OfType<RecursorInfo>().Where(r => r.All.Equals(typeNames)).OrderBy(r => r.Name);
                Assert.Equal(scanned, ((InductiveDeclaration)admitted).Recursors.OrderBy(r => r.Name));
            }
        }
        Assert.All(fixtures, d => Assert.Null(initMedium.Env.Find(AdmittedDeclarations.Of(fork, d).Constants[0].Name)));
    }

    /// <summary>An unforked environment holding the same constants as <paramref name="source"/>.</summary>
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
}
