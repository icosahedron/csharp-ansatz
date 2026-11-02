using Warrant.Cic;

namespace Warrant.Lean4Export.Tests;

/// <summary>
/// Reads the real export corpus and checks it against counts computed independently
/// (by a separate Python script over the raw JSON, recorded in tests/data/README.md).
/// </summary>
public class ReaderCorpusTests
{
    public record Expected(int Names, int Levels, int Exprs, int DeclarationLines, int Axioms, int Defs, int Thms, int Opaques, int Quots, int Inducts, int Ctors, int Recs);

    public static TheoryData<string, Expected> Corpus => new()
    {
        { TestData.NatAddSucc, new(103, 15, 434, 19, 0, 12, 1, 0, 0, 6, 7, 6) },
        { TestData.InitMedium, new(31267, 122, 343950, 4631, 4, 1791, 2615, 11, 4, 206, 279, 208) },
        { "arena/001_basicDef.ndjson", new(1, 1, 2, 1, 0, 1, 0, 0, 0, 0, 0, 0) },
        { "arena/002_badDef.ndjson", new(1, 1, 2, 1, 0, 1, 0, 0, 0, 0, 0, 0) },
        { "arena/141_falseFromUnsafe.ndjson", new(7, 1, 10, 3, 0, 1, 1, 0, 0, 1, 0, 1) },
        { "arena/proj-of-subst-prop.ndjson", new(708, 18, 4030, 110, 0, 63, 26, 2, 0, 19, 23, 19) },
        { "arena/rec-of-subst-prop.ndjson", new(776, 18, 4203, 127, 1, 76, 25, 3, 0, 22, 25, 22) },
        { "arena/sparse-name-index.ndjson", new(1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0) },
    };

    [Theory]
    [MemberData(nameof(Corpus))]
    public void ReadsCorpusWithExpectedCounts(string file, Expected expected)
    {
        var export = Lean4Export.ReadFile(TestData.Path(file));
        Assert.Equal(new ExportStatistics(expected.Names, expected.Levels, expected.Exprs, expected.DeclarationLines), export.Statistics);

        var byKind = export.Declarations.SelectMany(d => d.Constants).CountBy(c => c.Kind).ToDictionary();
        int Count(ConstantKind k) => byKind.GetValueOrDefault(k);
        Assert.Equal(expected.Axioms, Count(ConstantKind.Axiom));
        Assert.Equal(expected.Defs, Count(ConstantKind.Definition));
        Assert.Equal(expected.Thms, Count(ConstantKind.Theorem));
        Assert.Equal(expected.Opaques, Count(ConstantKind.Opaque));
        Assert.Equal(expected.Quots, Count(ConstantKind.Quot));
        Assert.Equal(expected.Inducts, Count(ConstantKind.Inductive));
        Assert.Equal(expected.Ctors, Count(ConstantKind.Constructor));
        Assert.Equal(expected.Recs, Count(ConstantKind.Recursor));

        // Every file is a valid environment: no constant is declared twice.
        var env = new Env();
        foreach (var d in export.Declarations)
        {
            env.Add(d);
        }
    }

    [Fact]
    public void ReadsFormat300NatAddSucc()
    {
        var export = Lean4Export.ReadFile(TestData.Path(TestData.NatAddSucc));
        Assert.Equal("3.0.0", export.Metadata.FormatVersion);
        Assert.Equal("4.27.0-rc1", export.Metadata.LeanVersion);

        var env = new Env();
        foreach (var d in export.Declarations)
        {
            env.Add(d);
        }

        var nat = Assert.IsType<InductiveInfo>(env.Find(Name.Parse("Nat")));
        Assert.Equal(Expr.Type, nat.Type);
        Assert.Equal([Name.Parse("Nat.zero"), Name.Parse("Nat.succ")], nat.Constructors);
        Assert.True(nat.IsRec);

        var succ = Assert.IsType<ConstructorInfo>(env.Find(Name.Parse("Nat.succ")));
        Assert.Equal(1, succ.Index);
        Assert.Equal(1, succ.NumFields);
        var natConst = Expr.Const(Name.Parse("Nat"));
        Assert.Equal(Expr.Forall(Name.Parse("n"), natConst, natConst), succ.Type);

        var rec = Assert.IsType<RecursorInfo>(env.Find(Name.Parse("Nat.rec")));
        Assert.Equal([Name.Parse("u")], rec.LevelParams);
        Assert.Equal(2, rec.NumMinors);
        Assert.Equal(2, rec.Rules.Count);

        var thm = Assert.IsType<TheoremInfo>(env.Find(Name.Parse("Nat.add_succ")));
        Assert.Equal([Name.Parse("Nat.add_succ")], thm.All);
    }

    [Fact]
    public void ReadsFormat310InitMedium()
    {
        var env = Lean4Export.LoadEnv(TestData.Path(TestData.InitMedium));
        Assert.Equal(5118, env.ConstantCount);

        var quots = env.Constants.OfType<QuotInfo>().ToDictionary(q => q.Name.ToString(), q => q.QuotKind);
        Assert.Equal(
            new Dictionary<string, QuotKind> { ["Quot"] = QuotKind.Type, ["Quot.mk"] = QuotKind.Ctor, ["Quot.lift"] = QuotKind.Lift, ["Quot.ind"] = QuotKind.Ind },
            quots);
        Assert.Equal(
            ["Classical.choice", "Quot.sound", "lcProof", "propext"],
            env.Constants.OfType<AxiomInfo>().Select(a => a.Name.ToString()).Order(StringComparer.Ordinal));

        var eq = Assert.IsType<InductiveInfo>(env.Find(Name.Parse("Eq")));
        Assert.Equal((2, 1), (eq.NumParams, eq.NumIndices));
        var eqRec = Assert.IsType<RecursorInfo>(env.Find(Name.Parse("Eq.rec")));
        Assert.True(eqRec.K);
        Assert.False(Assert.IsType<RecursorInfo>(env.Find(Name.Parse("Nat.rec"))).K);

        var add = Assert.IsType<DefinitionInfo>(env.Find(Name.Parse("Nat.add")));
        Assert.Equal(ReducibilityHints.Regular(1), add.Hints);
        Assert.Equal(DefinitionSafety.Safe, add.Safety);

        Assert.IsType<TheoremInfo>(env.Find(Name.Parse("Nat.add_comm")));
        Assert.All(env.Constants, c => Assert.False(c.Type.HasLooseBVars, $"{c.Name} has a loose bound variable in its type"));
        Assert.All(env.Constants, c => Assert.False(c.Type.HasFVar));
    }

    [Fact]
    public void AcceptsSparseIndices()
    {
        var env = Lean4Export.LoadEnv(TestData.Path("arena/sparse-name-index.ndjson"));
        var foo = Assert.IsType<AxiomInfo>(env.Find(Name.Parse("foo")));
        Assert.Equal(Expr.Prop, foo.Type);
    }
}
