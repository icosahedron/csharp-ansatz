using Warrant.Cic;
using Xunit.Abstractions;
using static Warrant.Meta.Tests.InitTerms;
using static Warrant.Meta.Tests.MetaTestSupport;

namespace Warrant.Meta.Tests;

/// <summary>
/// Discrimination trees (plan U16, KTD9; docs/m5a/05 "Discrimination trees"): keys recomputed from
/// the bundle's kernel-checked types agree with the keys Lean exported in the sidecar.
/// </summary>
public sealed class DiscrTreeTests(AttributeSidecarFixture fixture, ITestOutputHelper output) : IClassFixture<AttributeSidecarFixture>
{
    private static string Format(IEnumerable<DiscrTreeKey> keys) => string.Join(", ", keys.Select(k => k.Format()));

    // Lemmas whose left side Lean marks `no_index`: lean4export drops metadata unless run with
    // --export-mdata, which scripts/export-semantics.sh does not pass, so the bundle's types lack the
    // annotation and the recomputed keys index the term Lean does not. Each must still differ from
    // Lean's keys only by that: its type in the bundle carries no metadata at all.
    private static readonly HashSet<Name> NoIndexLostInExport = [N("Int32.toBitVec_ofNat"), N("Int64.toBitVec_ofNat")];

    [Fact]
    public void EverySimpEntrysKeysAreLeans()
    {
        var m = fixture.NewMeta();
        var entries = fixture.Sidecar.SimpEntries;
        var computed = new Dictionary<(Name, bool), IReadOnlyList<string>>();
        var seen = new Dictionary<(Name, bool), int>();
        var mismatches = new List<string>();
        int residue = 0;
        foreach (var e in entries)
        {
            var key = (e.Name, e.Inverse);
            if (!computed.TryGetValue(key, out var paths))
            {
                try
                {
                    paths = [.. m.MkSimpTheoremKeys(e.Name, e.Inverse).Select(p => Format(p))];
                }
                catch (MetaException ex)
                {
                    paths = [$"error: {ex.Message}"];
                }
                computed[key] = paths;
            }
            // A conjunction makes one entry per conjunct, in order; a lemma registered twice repeats them.
            int i = seen.GetValueOrDefault(key);
            seen[key] = i + 1;
            var mine = paths[i % paths.Count];
            var lean = string.Join(", ", e.LeanKeys);
            if (mine != lean && NoIndexLostInExport.Contains(e.Name) && !HasMData(m.GetConstInfo(e.Name).Type))
            {
                output.WriteLine($"{e.Name}: no_index lost in export; Lean [{lean}], Warrant [{mine}]");
                residue++;
            }
            else if (mine != lean)
            {
                mismatches.Add($"{e.Name}{(e.Inverse ? " (←)" : "")}: Lean [{lean}], Warrant [{mine}]");
            }
        }
        output.WriteLine($"{entries.Count - mismatches.Count - residue} of {entries.Count} simp entries agree with Lean's keys; {residue} differ only by a no_index the bundle lost");
        foreach (var mm in mismatches)
        {
            output.WriteLine(mm);
        }
        Assert.True(mismatches.Count == 0, string.Join('\n', mismatches));
    }

    private static bool HasMData(Expr e) => Kernel.ExprOps.Find(e, (x, _) => x is MDataExpr) is not null;

    [Fact]
    public void InstanceArgumentsAreIgnoredAndNumeralsAreLiterals()
    {
        var m = fixture.NewMeta();
        m.WithLocalDeclD(N("a"), Int32T, a =>
        {
            // @HAdd.hAdd Int32 Int32 Int32 inst a 5: the instance is a wildcard, the numeral the literal 5.
            var path = DiscrTree.MkPath(m, Int32Add(a, Int32Lit(5)));
            DiscrTreeKey[] expected =
            [
                DiscrTreeKey.Const(N("HAdd.hAdd"), 6), DiscrTreeKey.Const(N("Int32"), 0), DiscrTreeKey.Const(N("Int32"), 0),
                DiscrTreeKey.Const(N("Int32"), 0), DiscrTreeKey.Star, DiscrTreeKey.FVar(a.Id, 0), DiscrTreeKey.NatLit(5),
            ];
            Assert.Equal(expected, path);
            return 0;
        });
    }

    [Fact]
    public void NoIndexKeysAsAWildcard()
    {
        var m = fixture.NewMeta();
        var lit = DiscrTree.MkNoIndexAnnotation(Int32Lit(5));
        var toInt = Expr.App(C("Int32.toInt"), lit);
        Assert.Equal("Int32.toInt, *", Format(DiscrTree.MkPath(m, toInt)));
        Assert.Equal("Int32.toInt, 5", Format(DiscrTree.MkPath(m, Expr.App(C("Int32.toInt"), Int32Lit(5)))));
    }

    [Fact]
    public void ReducibleDefinitionsAreUnfolded()
    {
        var m = fixture.NewMeta();
        // GT.gt is reducible: a > b keys as b < a.
        var gt = Expr.App(C("GT.gt", Level.Zero), Nat, C("instLTNat"), NatLit(1), NatLit(2));
        Assert.Equal("LT.lt, Nat, *, 2, 1", Format(DiscrTree.MkPath(m, gt)));
    }

    [Fact]
    public void GetMatchFindsLemmasByShapeAndGetUnifyAlsoThroughMetavariables()
    {
        var m = fixture.NewMeta();
        var tree = new DiscrTree<string>();
        // Patterns, as simp lemmas' left sides: ?x + 0 and 0 + ?x at Nat, and a + b for any a b.
        var x = m.MkFreshExprMVar(Nat);
        tree.Insert(m, NatAdd(x, NatLit(0)), "add_zero");
        tree.Insert(m, NatAdd(NatLit(0), x), "zero_add");
        tree.Insert(m, NatAdd(m.MkFreshExprMVar(Nat), m.MkFreshExprMVar(Nat)), "add");
        Assert.Equal(3, tree.Count);

        m.WithLocalDeclD(N("n"), Nat, n =>
        {
            Assert.Equal(["add", "add_zero"], tree.GetMatch(m, NatAdd(n, NatLit(0))).Order());
            Assert.Equal(["add", "zero_add"], tree.GetMatch(m, NatAdd(NatLit(0), n)).Order());
            Assert.Equal(["add"], tree.GetMatch(m, NatAdd(n, n)));
            // A metavariable in the query matches nothing specific, but may unify with everything.
            var y = m.MkFreshExprMVar(Nat);
            Assert.Equal(["add"], tree.GetMatch(m, NatAdd(y, y)));
            Assert.Equal(["add", "add_zero", "zero_add"], tree.GetUnify(m, NatAdd(y, y)).Order());
            // n + 0 applied to nothing more: no extra arguments.
            Assert.Equal([("add", 0), ("add_zero", 0)], tree.GetMatchWithExtra(m, NatAdd(n, NatLit(0))).Order());
            return 0;
        });
    }
}
