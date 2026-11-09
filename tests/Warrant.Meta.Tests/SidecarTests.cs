using System.Text;
using Warrant.Cic;
using static Warrant.Meta.Tests.MetaTestSupport;

namespace Warrant.Meta.Tests;

/// <summary>
/// The attribute sidecar loader (plan U7, KTD5, KTD9; docs/m5a/05, "The sidecar"), against the
/// committed <c>warrant-attributes.ndjson.gz</c> and the semantics bundle it was exported for.
/// </summary>
public sealed class SidecarTests(AttributeSidecarFixture fixture) : IClassFixture<AttributeSidecarFixture>
{
    private const string Header = """{"kind":"header","format":2,"lean":"abc","bundleSha256":"00ff"}""";

    private Sidecar Sidecar => fixture.Sidecar;

    [Fact]
    public void TheHeaderNamesTheBundleAndLean()
    {
        Assert.Equal(2, Sidecar.Header!.Format);
        Assert.Equal(AttributeSidecarFixture.BundleSha256, Sidecar.Header.BundleSha256);
        Assert.Equal("eb6cafb7290e8bd5f2937522d8d804f58f02bafc", Sidecar.Header.LeanGithash);
    }

    [Fact]
    public void EveryKindHasTheExportedCount()
    {
        // tests/data/README.md; the simp count includes Lean's own duplicate entry for Nat.not_lt_zero.
        Assert.Equal(393, Sidecar.SimpEntries.Count);
        Assert.Equal(2, Sidecar.SimpEntries.Count(e => e.Name == N("Nat.not_lt_zero")));
        Assert.Equal(3, Sidecar.CongrEntries.Count);
        Assert.Equal(174, Sidecar.Instances.Count());
        Assert.Equal(652, Sidecar.ReducibilityStatuses.Count());
        Assert.Equal(66, Sidecar.DefEqNames.Count());
        Assert.Equal(337, Sidecar.Matchers.Count());
        Assert.Equal(75, Sidecar.Classes.Count());
        Assert.Equal(13, Sidecar.SpecEntries.Count);
    }

    [Fact]
    public void TheSpecEntriesAreStdDosTriplesForTheEffectMonadAndNameBundleConstants()
    {
        // M6 KTD15: the structural rules and the operations of StateT and ExceptT, all triples, from Std.Do.
        Assert.Equal(
            [
                "Std.Do.Spec.pure", "Std.Do.Spec.bind", "Std.Do.Spec.map", "Std.Do.Spec.seq", "Std.Do.Spec.monadLift_ExceptT",
                "Std.Do.Spec.get_StateT", "Std.Do.Spec.set_StateT", "Std.Do.Spec.modifyGet_StateT", "Std.Do.Spec.run_ExceptT",
                "Std.Do.Spec.throw_ExceptT", "Std.Do.Spec.tryCatch_ExceptT", "Std.Do.Spec.throw_MonadExcept", "Std.Do.Spec.tryCatch_MonadExcept",
            ],
            Sidecar.SpecEntries.Select(e => e.Name.ToString()));
        Assert.All(Sidecar.SpecEntries, e =>
        {
            Assert.Equal(SpecForm.Triple, e.Form);
            Assert.Equal(1000, e.Priority);
            Assert.Equal(N("Std.Do.Triple.SpecLemmas"), e.Module);
            Assert.True(fixture.Env.Find(e.Name) is TheoremInfo, $"{e.Name} is not a theorem of the bundle");
        });
    }

    [Fact]
    public void TheWPMonadInstancesOfTheEffectMonadsTransformersAreInstances()
    {
        var wpMonad = Sidecar.GetInstances(N("Std.Do.WPMonad")).Select(i => i.Name.ToString()).ToHashSet();
        Assert.Superset(
            new HashSet<string> { "Std.Do.Id.instWPMonad", "Std.Do.StateT.instWPMonad", "Std.Do.State.instWPMonad", "Std.Do.ExceptT.instWPMonad" },
            wpMonad);
        Assert.Contains(Sidecar.GetInstances(N("MonadExceptOf")), i => i.Name == N("instMonadExceptOfExceptTOfMonad"));
    }

    [Fact]
    public void AFormatOneSidecarIsRejectedNamingTheVersion()
    {
        var ex = Assert.Throws<SidecarFormatException>(() => Read("""{"kind":"header","format":1,"lean":"abc","bundleSha256":"00ff"}"""));

        Assert.Equal(1, ex.LineNumber);
        Assert.Contains("unsupported sidecar format 1; this loader reads format 2", ex.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ReducibilityStatusesAreLeans()
    {
        var m = fixture.NewMeta();
        Assert.Equal(ReducibilityStatus.ImplicitReducible, m.GetReducibilityStatus(N("Int.bmod")));
        Assert.Equal(ReducibilityStatus.Reducible, m.GetReducibilityStatus(N("GT.gt")));
        Assert.True(m.IsReducible(N("GT.gt")));
        // Init/Data/SInt/Basic.lean: `instance : DecidableEq Int32 := Int32.decEq`.
        Assert.Equal(ReducibilityStatus.InstanceReducible, m.GetReducibilityStatus(N("instDecidableEqInt32")));
        // Int32.add is implicitReducible; Int32.decEq, the body of instDecidableEqInt32, has no entry.
        Assert.Equal(ReducibilityStatus.ImplicitReducible, m.GetReducibilityStatus(N("Int32.add")));
        Assert.NotNull(m.Env.Find(N("Int32.decEq")));
        Assert.Equal(ReducibilityStatus.Semireducible, m.GetReducibilityStatus(N("Int32.decEq")));
        Assert.False(m.IsReducible(N("Int32.decEq")));
        Assert.False(m.IsIrreducible(N("Int32.decEq")));
        Assert.Equal(
            new Dictionary<ReducibilityStatus, int>
            {
                [ReducibilityStatus.Reducible] = 277,
                [ReducibilityStatus.InstanceReducible] = 251,
                [ReducibilityStatus.ImplicitReducible] = 119,
                [ReducibilityStatus.Irreducible] = 5,
            },
            Sidecar.ReducibilityStatuses.GroupBy(kv => kv.Value).ToDictionary(g => g.Key, g => g.Count()));
    }

    [Fact]
    public void InstancesComeInLeansOrder()
    {
        var decEq = Sidecar.GetInstances(N("DecidableEq"));
        var int32 = Assert.Single(decEq, i => i.Name == N("instDecidableEqInt32"));
        Assert.Equal(N("DecidableEq"), int32.Class);
        Assert.Equal(1000, int32.Priority);
        Assert.True(Sidecar.IsInstance(N("instDecidableEqInt32")));

        // Highest priority first, the most recently declared first among equals.
        Assert.Equal(N("instDecidableEqInt64"), decEq[0].Name);
        Assert.Equal(N("instDecidableEqInt32"), decEq[1].Name);
        foreach (var cls in Sidecar.Instances.Select(i => i.Class).Distinct())
        {
            var list = Sidecar.GetInstances(cls);
            Assert.All(list.Zip(list.Skip(1)), p =>
                Assert.True(p.First.Priority > p.Second.Priority || (p.First.Priority == p.Second.Priority && p.First.Order > p.Second.Order), $"{p.First.Name} before {p.Second.Name}"));
        }
        Assert.Empty(Sidecar.GetInstances(N("Nat")));
    }

    [Fact]
    public void SimpEntriesKeepPriorityAndDirection()
    {
        var falseEq = Assert.Single(Sidecar.SimpEntries, e => e.Name == N("Bool.false_eq"));
        Assert.Equal(100, falseEq.Priority);
        Assert.True(falseEq.Post);
        Assert.False(falseEq.Inverse);
        Assert.Equal(N("Init.Data.Bool"), falseEq.Module);
        Assert.Equal(new[] { "Eq", "Bool", "Bool.false", "*" }, falseEq.LeanKeys);
        Assert.Equal(10000, Assert.Single(Sidecar.SimpEntries, e => e.Name == N("imp_self")).Priority);
    }

    [Fact]
    public void CongrMatcherClassAndDefEqEntriesLoad()
    {
        var ite = Assert.Single(Sidecar.CongrEntries, c => c.Name == N("ite_congr"));
        Assert.Equal(N("ite"), ite.Function);
        Assert.Equal(1000, ite.Priority);
        Assert.Equal(new[] { 9, 10, 11 }, ite.Hypotheses);

        var and = Sidecar.GetMatcherInfo(N("Bool.Internal.and.match_1"));
        Assert.NotNull(and);
        Assert.Equal((0, 1, 2, 0), (and.NumParams, and.NumDiscrs, and.NumAlts, and.UElimPos));
        Assert.All(and.Alts, a => Assert.Equal(new MatcherAltInfo(0, 0, true), a));
        Assert.Equal(4, and.Arity);
        Assert.Equal((0, 1, 2), (and.MotivePos, and.FirstDiscrPos, and.FirstAltPos));
        Assert.Equal(new[] { 1, 1 }, and.AltNumParams);
        Assert.Null(Sidecar.GetMatcherInfo(N("Int32.add")));
        var decEq = Sidecar.GetMatcherInfo(N("BitVec.decEq.match_1"))!;
        Assert.Null(decEq.UElimPos);
        Assert.Equal(new Name?[] { null }, decEq.DiscrNames);

        Assert.True(Sidecar.IsClass(N("HAdd")));
        Assert.Equal(new[] { 2 }, Sidecar.GetOutParams(N("HAdd"))!.Value);
        Assert.Equal(new[] { 2, 3 }, Sidecar.GetOutParams(N("GetElem"))!.Value);
        Assert.Empty(Sidecar.GetOutParams(N("Add"))!.Value);
        Assert.Null(Sidecar.GetOutParams(N("Nat")));

        Assert.True(Sidecar.HasDefEqAttribute(N("BitVec.getLsbD.eq_1")));
        Assert.False(Sidecar.HasDefEqAttribute(N("Int32.add")));
    }

    [Fact]
    public void EveryNameInTheSidecarIsInTheBundle()
    {
        var names = Sidecar.SimpEntries.Select(e => e.Name)
            .Concat(Sidecar.CongrEntries.SelectMany(c => new[] { c.Name, c.Function }))
            .Concat(Sidecar.Instances.SelectMany(i => new[] { i.Name, i.Class }))
            .Concat(Sidecar.ReducibilityStatuses.Select(kv => kv.Key))
            .Concat(Sidecar.DefEqNames)
            .Concat(Sidecar.Matchers.Select(m => m.Name))
            .Concat(Sidecar.Classes.Select(kv => kv.Key))
            .Distinct()
            .ToList();
        Assert.NotEmpty(names);
        Assert.All(names, n => Assert.True(fixture.Env.Find(n) is not null, $"{n} is not in the bundle"));
    }

    [Fact]
    public void AMismatchedBundleHashFailsNamingBothHashes()
    {
        var wrong = new string('0', 64);
        var ex = Assert.Throws<SidecarFormatException>(() => Sidecar.Load(TestData.Path(AttributeSidecarFixture.FileName), wrong));
        Assert.Contains(wrong, ex.Message, StringComparison.Ordinal);
        Assert.Contains(AttributeSidecarFixture.BundleSha256, ex.Message, StringComparison.Ordinal);
        Assert.Equal(1, ex.LineNumber);
    }

    [Theory]
    [InlineData("""{"kind":"lemma","name":"Nat.add_zero"}""", "unknown kind 'lemma'")]
    [InlineData("""{"kind":"defeq","name":"Nat.add_zero","extra":1}""", "unknown field 'extra'")]
    [InlineData("""{"kind":"reducibility","name":"Nat.add"}""", "missing field 'status'")]
    [InlineData("""{"kind":"reducibility","name":"Nat.add","status":"opaque"}""", "unknown reducibility status 'opaque'")]
    [InlineData("""{"kind":"instance","name":"i","class":"C","prio":"high","order":0}""", "'prio' must be")]
    [InlineData(Header, "a second header")]
    [InlineData("""{"kind":"spec","name":"Std.Do.Spec.pure","prio":1000,"form":"lemma","module":"M"}""", "unknown spec form 'lemma'")]
    [InlineData("""{"kind":"spec","name":"Std.Do.Spec.pure","prio":1000,"form":"triple"}""", "missing field 'module'")]
    public void MalformedLinesFailNamingTheLine(string line, string message)
    {
        var ex = Assert.Throws<SidecarFormatException>(() => Read(Header, line));
        Assert.Equal(2, ex.LineNumber);
        Assert.Contains("line 2", ex.Message, StringComparison.Ordinal);
        Assert.Contains(message, ex.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void TheFirstLineMustBeAHeader()
    {
        var ex = Assert.Throws<SidecarFormatException>(() => Read("""{"kind":"defeq","name":"x"}"""));
        Assert.Equal(1, ex.LineNumber);
        Assert.Contains("header", ex.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void AForkAddsEntriesWithoutChangingTheBase()
    {
        var baseSidecar = Sidecar;
        var fork = baseSidecar.Fork();
        var payment = N("PaymentResult");
        var sum = N("Sum");
        var inst = N("instDecidableEqPaymentResult");

        fork.SetReducibilityStatus(payment, ReducibilityStatus.Reducible);
        fork.SetReducibilityStatus(sum, ReducibilityStatus.Irreducible);
        fork.SetReducibilityStatus(N("GT.gt"), ReducibilityStatus.Semireducible);
        fork.AddInstance(inst, N("DecidableEq"));

        Assert.Equal(ReducibilityStatus.Reducible, fork.GetReducibilityStatus(payment));
        Assert.Equal(ReducibilityStatus.Irreducible, fork.GetReducibilityStatus(sum));
        Assert.Equal(ReducibilityStatus.Semireducible, fork.GetReducibilityStatus(N("GT.gt")));
        Assert.Equal(ReducibilityStatus.ImplicitReducible, fork.GetReducibilityStatus(N("Int.bmod")));
        var added = fork.GetInstances(N("DecidableEq"))[0];
        Assert.Equal((inst, 1000), (added.Name, added.Priority));
        Assert.True(fork.IsInstance(inst));
        Assert.Equal(baseSidecar.GetInstances(N("DecidableEq")).Count + 1, fork.GetInstances(N("DecidableEq")).Count);
        Assert.Equal(653, fork.ReducibilityStatuses.Count(kv => kv.Value != ReducibilityStatus.Semireducible));
        Assert.Same(baseSidecar.Header, fork.Header);
        Assert.Equal(baseSidecar.SimpEntries, fork.SimpEntries);

        Assert.Equal(ReducibilityStatus.Semireducible, baseSidecar.GetReducibilityStatus(payment));
        Assert.Equal(ReducibilityStatus.Reducible, baseSidecar.GetReducibilityStatus(N("GT.gt")));
        Assert.False(baseSidecar.IsInstance(inst));
        Assert.DoesNotContain(baseSidecar.GetInstances(N("DecidableEq")), i => i.Name == inst);
        Assert.Throws<InvalidOperationException>(() => baseSidecar.SetReducibilityStatus(payment, ReducibilityStatus.Reducible));
        Assert.Equal(ReducibilityStatus.Semireducible, fixture.NewMeta().GetReducibilityStatus(payment));
    }

    private static Sidecar Read(params string[] lines) =>
        Sidecar.Read(new MemoryStream(Encoding.UTF8.GetBytes(string.Join('\n', lines))), "00ff", "test");
}
