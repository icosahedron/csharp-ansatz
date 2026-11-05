using Warrant.Vir;

namespace Warrant.Engine.Tests;

/// <summary><see cref="VirTree.IdOf"/>, the one lookup of a node's pre-order ID (plan M5a U1, ticket 1e637f0).</summary>
public sealed class NodeIdTests
{
    [Fact]
    public void IdOfAgreesWithAScanOfThePreOrderForEveryNodeOfEveryCorpusUnit()
    {
        int checkedNodes = 0;
        foreach (var compilation in EngineCorpus.Compilations)
        {
            foreach (var unit in EngineCorpus.Extract(compilation).Units.Select(u => u.Unit))
            {
                var nodes = VirTree.PreOrder(unit);
                foreach (var node in nodes)
                {
                    int expected = -1;
                    for (int i = 0; i < nodes.Count; i++)
                    {
                        if (ReferenceEquals(nodes[i], node))
                        {
                            expected = i;
                            break;
                        }
                    }
                    Assert.Equal(expected, VirTree.IdOf(unit, node));
                    checkedNodes++;
                }
            }
        }
        Assert.True(checkedNodes > 0);
    }
}
