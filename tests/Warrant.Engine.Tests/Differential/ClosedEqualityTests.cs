using System.Reflection;
using Warrant.Vir;

namespace Warrant.Engine.Tests.Differential;

/// <summary>
/// A closed class is modelled by identity (KTD11, plan R8): on every pair of static instances, <c>==</c>,
/// <c>Equals(object)</c> and <c>EqualityComparer&lt;T&gt;.Default.Equals</c> are true exactly for identical instances, and
/// reading each instance property twice gives the same object (docs/m4/07, "Closed classes").
/// </summary>
[Collection(DifferentialGroup.Name)]
public sealed class ClosedEqualityTests(DifferentialFixture corpus)
{
    [Fact]
    public void EveryClosedClassComparesItsStaticInstancesByIdentity()
    {
        var classes = ClosedClasses().ToList();
        Assert.Equal(["T:Claims.Outcome"], classes.Select(c => c.Key));
        foreach (var (key, closed) in classes)
        {
            var type = corpus.Assembly.TypeOf(key);
            var instances = closed.Members.Select(m => (m.Name, Value: CorpusAssembly.ReadStatic(type, m.Name))).ToList();
            Assert.All(instances, i => Assert.NotNull(i.Value));

            foreach (var member in closed.Members)
            {
                Assert.Same(CorpusAssembly.ReadStatic(type, member.Name), CorpusAssembly.ReadStatic(type, member.Name));
            }

            var opEquality = type.GetMethod("op_Equality", BindingFlags.Public | BindingFlags.Static, [type, type]);
            var comparer = typeof(EqualityComparer<>).MakeGenericType(type).GetProperty("Default")!.GetValue(null)!;
            var comparerEquals = comparer.GetType().GetMethod("Equals", [type, type])!;
            foreach (var (aName, a) in instances)
            {
                foreach (var (bName, b) in instances)
                {
                    var identical = ReferenceEquals(a, b);
                    // Without a user-defined operator, == on a class is reference equality.
                    var equalOperator = opEquality is null ? ReferenceEquals(a, b) : (bool)opEquality.Invoke(null, [a, b])!;
                    Assert.True(identical == equalOperator, $"{key}: {aName} == {bName} is {equalOperator}");
                    Assert.True(identical == a!.Equals(b), $"{key}: {aName}.Equals((object){bName}) is {!identical}");
                    Assert.True(identical == (bool)comparerEquals.Invoke(comparer, [a, b])!, $"{key}: EqualityComparer.Default.Equals({aName}, {bName}) is {!identical}");
                }
            }
        }
    }

    [Fact]
    public void TheModelOfSameAgreesOnEveryPairOfInstances()
    {
        var unit = corpus.Unit("M:Claims.Outcomes.Same(Claims.Outcome,Claims.Outcome)");
        var inputs = corpus.Inputs.BoundaryInputs(ModelCheck.ParameterTypes(unit.Unit));
        Assert.Equal(4, inputs.Count);
        var run = corpus.Check(unit, inputs);
        Assert.True(run.Disagreements.Count == 0, string.Join("\n", run.Disagreements));
    }

    private IEnumerable<(string Key, ClosedDefinition Closed)> ClosedClasses() =>
        corpus.Extraction.Units
            .Where(u => u.Unit.Definition is ClosedDefinition && !corpus.Assembly.TypeOf(u.Key).IsEnum)
            .Select(u => (u.Key, (ClosedDefinition)u.Unit.Definition!));
}
