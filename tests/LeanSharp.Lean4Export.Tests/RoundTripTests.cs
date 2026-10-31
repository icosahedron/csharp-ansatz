using LeanSharp.Cic;

namespace LeanSharp.Lean4Export.Tests;

public class RoundTripTests
{
    private static (byte[] Bytes, ExportStatistics Stats) Export(ExportFile file)
    {
        using var ms = new MemoryStream();
        using (var writer = new Lean4ExportWriter(ms, file.Metadata, leaveOpen: true))
        {
            writer.WriteAll(file.Declarations);
        }
        return (ms.ToArray(), Read(ms.ToArray()).Statistics);
    }

    private static ExportFile Read(byte[] bytes)
    {
        using var reader = new Lean4ExportReader(new MemoryStream(bytes));
        var decls = reader.ReadDeclarations().ToList();
        return new ExportFile(reader.Metadata, decls, reader.Statistics);
    }

    [Theory]
    [MemberData(nameof(TestData.AllFiles), MemberType = typeof(TestData))]
    public void ImportExportImportPreservesEveryDeclaration(string file)
    {
        var original = Lean4Export.ReadFile(TestData.Path(file));
        var (bytes, _) = Export(original);
        var reread = Read(bytes);

        Assert.Equal(Lean4ExportWriter.FormatVersion, reread.Metadata.FormatVersion);
        Assert.Equal("LeanSharp", reread.Metadata.ExporterName);
        Assert.Equal(original.Metadata.LeanVersion, reread.Metadata.LeanVersion);
        Assert.Equal(original.Metadata.LeanGithash, reread.Metadata.LeanGithash);

        // 3.0.0 mutual arrays become one line per constant, so compare constant by constant.
        var before = original.Declarations.SelectMany(d => d.Constants).ToList();
        var after = reread.Declarations.SelectMany(d => d.Constants).ToList();
        Assert.Equal(before.Count, after.Count);
        for (int i = 0; i < before.Count; i++)
        {
            Assert.True(before[i].Equals(after[i]), $"constant #{i} '{before[i].Name}' differs after round trip");
        }
        Assert.Equal(
            original.Declarations.OfType<InductiveDeclaration>().Count(),
            reread.Declarations.OfType<InductiveDeclaration>().Count());
    }

    [Theory]
    [MemberData(nameof(TestData.AllFiles), MemberType = typeof(TestData))]
    public void WriterIsIdempotent(string file)
    {
        var (first, firstStats) = Export(Lean4Export.ReadFile(TestData.Path(file)));
        var (second, secondStats) = Export(Read(first));
        Assert.Equal(firstStats, secondStats);
        Assert.True(first.AsSpan().SequenceEqual(second), "export → import → export changed the bytes");
    }

    [Fact]
    public void WriterDoesNotDuplicateTableEntries()
    {
        // lean4export already deduplicates, so re-exporting a 3.1.0 file must not grow any table.
        var original = Lean4Export.ReadFile(TestData.Path(TestData.InitMedium));
        var (_, stats) = Export(original);
        Assert.True(stats.Names <= original.Statistics.Names, $"names {stats.Names} > {original.Statistics.Names}");
        Assert.True(stats.Levels <= original.Statistics.Levels, $"levels {stats.Levels} > {original.Statistics.Levels}");
        Assert.True(stats.Exprs <= original.Statistics.Exprs, $"exprs {stats.Exprs} > {original.Statistics.Exprs}");
    }

    [Fact]
    public void ExportingAFreeVariableFails()
    {
        var bad = new ConstantDeclaration(new AxiomInfo(Name.Parse("bad"), EquatableArray<Name>.Empty, Expr.FVar(new FVarId(Name.Parse("x"))), false));
        using var writer = new Lean4ExportWriter(new MemoryStream());
        Assert.Throws<ArgumentException>(() => writer.Write(bad));
    }

    [Fact]
    public void RoundTripsMetadataAndUnusualValues()
    {
        var u = Name.Parse("u");
        var weird = Name.Parse("«a.b»").Append(7).Append("ünïcode \"quoted\"\n");
        var body = Expr.MData(
            new KVMap(EquatableArray.Create(new KVMapEntry("b", "true"), new KVMapEntry("a", "`x"))),
            Expr.Let(Name.Parse("y"), Expr.Sort(Level.IMax(Level.Param(u), Level.Succ(Level.Zero))),
                Expr.NatLit(System.Numerics.BigInteger.Pow(10, 40)),
                Expr.Proj(Name.Parse("Prod"), 1, Expr.App(Expr.StrLit("é\u0000\t"), Expr.BVar(0))),
                nonDependent: true));
        var decl = new ConstantDeclaration(new DefinitionInfo(
            weird, EquatableArray.Create(u), Expr.Sort(Level.Max(Level.Param(u), Level.One)), body,
            ReducibilityHints.Abbrev, DefinitionSafety.Partial, EquatableArray.Create(weird)));

        using var ms = new MemoryStream();
        using (var writer = new Lean4ExportWriter(ms, leaveOpen: true))
        {
            writer.Write(decl);
        }
        var reread = Read(ms.ToArray());
        Assert.Equal(decl, Assert.Single(reread.Declarations));
    }
}
