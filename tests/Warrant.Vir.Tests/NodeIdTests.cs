namespace Warrant.Vir.Tests;

public class NodeIdTests
{
    [Fact]
    public void NodeIdsArePreOrder()
    {
        var kinds = VirTree.PreOrder(Samples.Payout()).Select(n => n.GetType().Name).ToArray();

        Assert.Equal(
            new[]
            {
                "BlockStmt",
                "IfStmt", "CompareExpr", "ParamExpr", "ParamExpr", "BlockStmt", "ReturnStmt", "LitExpr",
                "DeclStmt", "BinaryExpr", "ParamExpr", "ParamExpr",
                "ReturnStmt", "CondExpr", "CompareExpr", "LocalExpr", "ParamExpr", "ParamExpr", "LocalExpr",
            },
            kinds);
    }

    [Fact]
    public void TheSpanTableIsKeyedByNodeId()
    {
        var unit = Samples.Payout();
        var lit = VirTree.PreOrder(unit).OfType<LitExpr>().Single();
        var span = new VirSpan("PayoutRules.cs", 12, 20, 12, 21);

        var table = SpanTable.Build(unit, n => ReferenceEquals(n, lit) ? span : null);

        Assert.Equal(1, table.Count);
        Assert.True(table.TryGetSpan(7, out var found));
        Assert.Equal(span, found);
    }

    [Fact]
    public void TheSpanTableEnumeratesItsSpansInNodeIdOrder()
    {
        var a = new VirSpan("A.cs", 3, 1, 3, 2);
        var b = new VirSpan("A.cs", 1, 1, 1, 2);
        var c = new VirSpan("A.cs", 2, 1, 2, 2);

        var table = new SpanTable([new(9, a), new(2, b), new(5, c)]);

        Assert.Equal([new(2, b), new(5, c), new(9, a)], table.Entries);
        var copy = new SpanTable(table.Entries);
        Assert.True(copy.TryGetSpan(5, out var found));
        Assert.Equal(c, found);
    }
}
