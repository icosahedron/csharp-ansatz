using Warrant.Kernel;
using Warrant.Vir;

namespace Warrant.Engine.Tests.Differential;

/// <summary>
/// <c>null</c>, which the M4 model does not have, on the CLR side only (docs/m4/07, "Null"; plan R7): what the .NET method
/// does with it, and the non-null assumption that excludes it from what a proof covers.
/// </summary>
[Collection(DifferentialGroup.Name)]
public sealed class NullTests(DifferentialFixture corpus)
{
    [Theory]
    [InlineData("M:Claims.Payments.Validate(Claims.Payment)", "p")]
    [InlineData("M:Claims.Records.Move(Claims.Point,System.Int32)", "p")]
    [InlineData("M:Claims.Records.Distance(Claims.Point)", "p")]
    public void ANullRecordTheMethodReadsThrowsAndIsAssumedNonNull(string key, string parameter)
    {
        var unit = corpus.Unit(key);
        var args = ModelCheck.ParameterTypes(unit.Unit).Select(t => t is PrimitiveType ? corpus.Inputs.Boundaries(t)[0] : null).ToArray();
        Assert.Throws<NullReferenceException>(() => CorpusAssembly.Invoke(corpus.Assembly.MethodOf(unit.Unit), args));
        Assert.Contains(new VirAssumption(VirAssumptionKind.NonNull, parameter), unit.Unit.Assumptions);
        Assert.Contains(corpus.Run.Find(key)!.Assumptions, a => a.UnitKey == key && a.Assumption.Subject == parameter);
    }

    [Fact]
    public void NullForAClosedClassReturnsAValueTheModelCannotProduceAndIsAssumedNonNull()
    {
        var unit = corpus.Unit("M:Claims.Outcomes.Code(Claims.Outcome)");
        var method = corpus.Assembly.MethodOf(unit.Unit);
        Assert.Equal(3, CorpusAssembly.Invoke(method, [null]));

        // The model's Code is total over the closed type's members, and on each of them it is not 3: for every member o
        // the kernel rejects Code o = 3.
        var outcome = VirType.Ref("T:Claims.Outcome");
        var members = corpus.Inputs.Boundaries(outcome);
        Assert.Equal(2, members.Count);
        var messages = KernelThread.Run(() => members
            .Select(o => corpus.Model.Disagreement($"Code({corpus.Model.Values.Display(outcome, o)})", VirType.Int32, corpus.Model.Application(unit.Unit, [o]), 3))
            .ToList());
        Assert.All(messages, m => Assert.Contains("the CLR returned 3 but the model computes", m, StringComparison.Ordinal));

        Assert.Contains(new VirAssumption(VirAssumptionKind.NonNull, "o"), unit.Unit.Assumptions);
    }

    [Fact]
    public void ANullRecordFieldMisbehavesAndIsAssumedNonNull()
    {
        var unit = corpus.Unit("M:Claims.Records.Amount(Claims.Claim)");
        var method = corpus.Assembly.MethodOf(unit.Unit);
        var claim = corpus.Assembly.TypeOf("T:Claims.Claim");
        var matched = CorpusAssembly.ReadStatic(corpus.Assembly.TypeOf("T:Claims.Outcome"), "Matched");

        // A null Payment is read when the outcome is Matched.
        Assert.Throws<NullReferenceException>(() => CorpusAssembly.Invoke(method, [Activator.CreateInstance(claim, 1, null, matched)]));

        // A null Outcome does not throw: it compares unequal to Matched and the CLR returns 0, for an input the model has
        // no value for.
        var payment = Activator.CreateInstance(corpus.Assembly.TypeOf("T:Claims.Payment"), 1, 10, Enum.ToObject(corpus.Assembly.TypeOf("T:Claims.PaymentStatus"), 0));
        var nullOutcome = Activator.CreateInstance(claim, 1, payment, null);
        Assert.Equal(0, CorpusAssembly.Invoke(method, [nullOutcome]));
        Assert.Throws<ModelGapException>(() => corpus.Model.Values.Term(VirType.Ref("T:Claims.Claim"), nullOutcome));

        var subjects = unit.Unit.Assumptions.Where(a => a.Kind == VirAssumptionKind.NonNull).Select(a => a.Subject).ToList();
        Assert.Equal(["c", "c.Outcome", "c.Payment"], subjects.Order(StringComparer.Ordinal));
    }

    /// <summary>
    /// Every unit that receives a record, directly or as its receiver, assumes non-null every record- and closed-typed
    /// field reachable from it (plan R7): for <c>Amount</c>, <c>c.Payment</c> and <c>c.Outcome</c>.
    /// </summary>
    [Fact]
    public void EveryReachableReferenceFieldIsAssumedNonNullByEveryUnitThatReceivesIt()
    {
        int checkedSubjects = 0;
        foreach (var unit in corpus.Functions)
        {
            var parameters = (unit.Unit.Params ?? VirList<VirParam>.Empty).Select(p => (p.Name, p.Type)).ToList();
            if (unit.Unit.Self is { } self)
            {
                parameters.Insert(0, ("this", VirType.Ref(self)));
            }
            var subjects = unit.Unit.Assumptions.Where(a => a.Kind == VirAssumptionKind.NonNull).Select(a => a.Subject).ToHashSet();
            foreach (var (name, type) in parameters)
            {
                foreach (var subject in References(name, type, unit.Unit.Self is not null && name == "this"))
                {
                    Assert.True(subjects.Contains(subject), $"{unit.Key} does not assume {subject} is non-null; it assumes {string.Join(", ", subjects)}");
                    checkedSubjects++;
                }
            }
        }
        Assert.True(checkedSubjects >= 3);
        Assert.Contains("c.Payment", corpus.Unit("M:Claims.Records.Amount(Claims.Claim)").Unit.Assumptions.Select(a => a.Subject));
    }

    /// <summary>
    /// The reference-typed values reachable from a parameter: itself (unless it is the receiver) and its record and
    /// closed-class fields, transitively. Enums, closed ones included, are value types and cannot be null.
    /// </summary>
    private IEnumerable<string> References(string prefix, VirType type, bool receiver)
    {
        if (type is not RefType r || corpus.Assembly.TypeOf(r.Key).IsValueType)
        {
            yield break;
        }
        if (!receiver)
        {
            yield return prefix;
        }
        if (corpus.Model.Values.Definition(r.Key) is RecordDefinition record)
        {
            foreach (var field in record.Fields)
            {
                foreach (var subject in References($"{prefix}.{field.Name}", field.Type, receiver: false))
                {
                    yield return subject;
                }
            }
        }
    }
}
