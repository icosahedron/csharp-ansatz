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
}
