namespace Warrant.Semantics.Tests;

/// <summary>
/// M6's exit criterion for the models (plan M6 Success Criteria, R5; plan U14): CLR-agreement tests pass for every new model
/// operation, with generators that include zero divisors, <c>MinValue / -1</c> and equal decimals with different scales.
/// The other criteria are <c>Warrant.Cli.Tests.M6ExitTests</c> and <c>Warrant.Engine.Tests.M6ExitTests</c>;
/// <c>dotnet test --filter M6Exit</c> runs all of them.
/// </summary>
public sealed class M6ExitTests(SemanticsBundleFixture bundle) : IClassFixture<SemanticsBundleFixture>
{
    [Fact]
    public void EveryNewModelOperationAgreesWithTheClrOnGeneratorsWithZeroDivisorsMinValueByMinusOneAndRescaledDecimals()
    {
        // The generators hold the inputs the criterion names.
        Assert.Contains(Generators.Int32BoundaryPairs(), p => p.Item2 == 0);
        Assert.Contains((int.MinValue, -1), Generators.Int32BoundaryPairs());
        Assert.Contains(Generators.Int64BoundaryPairs(), p => p.Item2 == 0);
        Assert.Contains((long.MinValue, -1L), Generators.Int64BoundaryPairs());
        Assert.Contains(Generators.DecimalBoundaryPairs(), p => p.Item1 == p.Item2 && Scale(p.Item1) != Scale(p.Item2));

        // Every agreement test of an M6 model operation (U3's raising operations, U16's nullable reads and Math, U4's
        // decimal): ClrM's checked arithmetic, division and remainder, narrowing, the nullable reads and unwrap, Math.Min,
        // Math.Max and Math.Abs on int, long and decimal, and decimal literals, +, -, unary -, comparisons and equality.
        var agreement = new ClrAgreementTests(bundle);
        foreach (var name in ClrAgreementTests.RaisingNames().Cast<object[]>().Select(row => (string)row[0]))
        {
            agreement.Int32RaisingOperationsAgree(name);
            agreement.Int64RaisingOperationsAgree(name);
        }
        agreement.CheckedNegationAgrees();
        agreement.CheckedNarrowingAgrees();
        agreement.NamedRaisingCasesAgree();
        agreement.NullableValueAgrees();
        agreement.NonNullUnwrapAgrees();
        agreement.CoalesceAndGetValueOrDefaultAgree();
        agreement.ANullValueRaisesInvalidOperationAndANullReceiverNullReference();
        agreement.MathMinAndMaxAgree();
        agreement.MathAbsAgrees();
        agreement.DecimalLiteralsRoundTripAtEveryScale();
        agreement.DecimalAdditionAndSubtractionAgree();
        agreement.NamedDecimalCasesAgree();
        agreement.DecimalNegationAgrees();
        agreement.DecimalComparisonsAgree();
        agreement.EqualValuesAtDifferentScalesAreEqual();
        agreement.MathOnDecimalAgrees();
    }

    private static int Scale(decimal value) => (decimal.GetBits(value)[3] >> 16) & 0xFF;
}
