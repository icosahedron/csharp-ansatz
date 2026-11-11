using Warrant.Engine.Tests.Differential;
using Xunit.Abstractions;

namespace Warrant.Engine.Tests;

/// <summary>
/// M6's exit criterion for the differential tests (plan M6 Success Criteria, KTD21; plan U14): with contract-satisfying
/// mocked externals, CLR runs and model evaluation agree on results and on exceptions, and every proved contract holds of
/// the CLR runs. The other criteria are <c>Warrant.Cli.Tests.M6ExitTests</c> and <c>Warrant.Semantics.Tests.M6ExitTests</c>;
/// <c>dotnet test --filter M6Exit</c> runs all of them.
/// </summary>
public sealed class M6ExitTests(M6DependencyFixture fixture, ITestOutputHelper output) : IClassFixture<M6DependencyFixture>
{
    [Fact]
    public void DifferentialTestsWithContractSatisfyingMockedExternalsPass()
    {
        // Every function in the corpus's dependency files, accepted and refuted, on every boundary input against random
        // contract-satisfying tapes and on random inputs and tapes: the model makes the CLR's calls and ends as it does.
        var differential = new DependencyDifferentialTests(fixture, output);
        differential.EveryM6FunctionInTheDependencyFilesIsCompared();
        var functions = DependencyDifferentialTests.Functions().Cast<object[]>().Select(row => ((string)row[0], (string)row[1])).ToList();
        Assert.Contains(("accepted", "M:Corpus.M6.Payments.PaymentService.ProcessPayment(System.Int32)"), functions);
        foreach (var (compilation, key) in functions)
        {
            differential.AgreesOnEveryBoundaryCombination(compilation, key);
            differential.AgreesOnRandomInputs(compilation, key);
        }

        // Every proved contract's Spec.Requires and Spec.Ensures, computed on the CLR, hold of its runs with the same mocks.
        var statements = new ContractStatementTests(fixture, output);
        statements.EveryProvedObligationIsChecked();
        foreach (var key in ContractStatementTests.Methods().Cast<object[]>().Select(row => (string)row[0]))
        {
            statements.EveryProvedContractHoldsOnItsClrRuns(key);
        }
    }
}
