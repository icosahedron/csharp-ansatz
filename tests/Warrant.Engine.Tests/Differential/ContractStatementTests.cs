using Warrant.Kernel;
using Warrant.Semantics;
using Warrant.Vir;
using Xunit.Abstractions;
using Xunit.Sdk;

namespace Warrant.Engine.Tests.Differential;

/// <summary>
/// What one contract-statement check of a method found (plan M6 U22 step 2): the inputs tried and those that satisfied its
/// <c>Spec.Requires</c>, how their runs ended, and every run that broke the contract.
/// </summary>
internal sealed class StatementCheck
{
    /// <summary>
    /// The fewest generated inputs that must satisfy a method's <c>Spec.Requires</c> (#185): a check that ran on fewer has
    /// shown too little, and fails.
    /// </summary>
    public const int MinimumSatisfyingInputs = 100;

    /// <summary>The satisfying inputs a check stops at.</summary>
    public const int SatisfyingInputs = 1_000;

    /// <summary>The most inputs a check generates, the boundary inputs included, looking for satisfying ones.</summary>
    public const int InputBudget = 20_000;

    /// <summary>The seed of the generated inputs; each run's tape has its own, from the input's index.</summary>
    public const int Seed = 20261111;

    private readonly List<string> _failures = [];

    public int Tried { get; private set; }

    public int Satisfying { get; private set; }

    public int Returned { get; private set; }

    public int ExplicitThrows { get; private set; }

    public int External { get; private set; }

    public int Calls { get; private set; }

    public IReadOnlyList<string> Failures => _failures;

    /// <summary>
    /// Runs a method on the CLR on its boundary inputs and then generated ones, keeping those that satisfy its
    /// <c>Spec.Requires</c> as the CLR computes it, against a contract-satisfying random tape, and checks that every
    /// normal return satisfies its <c>Spec.Ensures</c>, that every exception is the type of one of its explicit throws or a
    /// mock's sentinel, and that every external call satisfies the member's <c>Spec.Requires</c>. Uses no model.
    /// </summary>
    public static StatementCheck Run(DependencyRunner runner, string key)
    {
        var check = new StatementCheck();
        var unit = runner.Side.Unit(key).Unit;
        var types = ModelCheck.ParameterTypes(unit);
        var throws = runner.Contracts.ExplicitThrows[key];
        var rng = new Random(Seed);
        var boundaries = runner.Side.Inputs.BoundaryInputs(types);
        for (int i = 0; i < InputBudget && check.Satisfying < SatisfyingInputs; i++)
        {
            var args = i < boundaries.Count ? boundaries[i] : runner.Values.Input(types, rng);
            check.Tried++;
            // A Spec takes the method's declared parameters, not a receiver.
            var declared = unit.Self is null ? args : args[1..];
            if (runner.Specs.FailedRequires(key, declared) is not null)
            {
                continue;
            }
            check.Satisfying++;
            var description = runner.DisplayCall(key, args);
            var clr = runner.RunClr(unit, [args], new RandomReplies(runner, i), checkMemberRequires: true);
            check.Calls += clr.Tape.Calls.Count;
            foreach (var violation in clr.Tape.RequiresViolations)
            {
                check._failures.Add($"{description}: {violation}");
            }
            var (result, thrown) = clr.Outcomes[0];
            switch (thrown)
            {
                case null:
                    check.Returned++;
                    if (runner.Specs.FailedEnsures(key, declared, result) is { } ensures)
                    {
                        check._failures.Add($"{description} returned {runner.Side.Model.Values.Display(ModelCheck.Returned(unit), result)}, which falsifies {ensures}");
                    }
                    break;
                case MockException:
                    check.External++;
                    break;
                case var ex when throws.Contains(ClrExceptions.Key(ex.GetType())):
                    check.ExplicitThrows++;
                    break;
                default:
                    check._failures.Add($"{description} threw {thrown.GetType().Name}, which is neither one of its explicit throws [{string.Join(", ", throws.Order(StringComparer.Ordinal))}] nor a mock's");
                    break;
            }
        }
        return check;
    }

    /// <summary>Fails unless no run broke the contract and at least <see cref="MinimumSatisfyingInputs"/> inputs satisfied <c>Spec.Requires</c>.</summary>
    public void AssertHolds(string key)
    {
        if (_failures.Count > 0)
        {
            throw new XunitException($"{key}: {_failures.Count} of {Satisfying} runs break the contract:\n{string.Join("\n", _failures.Take(20))}");
        }
        if (Satisfying < MinimumSatisfyingInputs)
        {
            throw new XunitException(
                $"{key}: only {Satisfying} of the {Tried} inputs generated satisfy its Spec.Requires, and at least {MinimumSatisfyingInputs} must (#185).");
        }
    }

    public override string ToString() =>
        $"{Satisfying} of {Tried} inputs satisfy Spec.Requires: {Returned} returned, {ExplicitThrows} threw explicitly, {External} threw a mock's sentinel; {Calls} external calls";
}

/// <summary>
/// Contract statements against the CLR (plan M6 U22 step 2, R6, R8, R11), modelled on <see cref="TheoremStatementTests"/>:
/// for every accepted M6 method whose contract obligation is proved, its <c>Spec.Requires</c> and <c>Spec.Ensures</c>,
/// computed on the CLR from a rewritten copy of the compilation (<see cref="ContractCompilation"/>), must hold of its CLR
/// runs with contract-satisfying mocks. This checks the trusted statement: a proved triple that the CLR breaks is a
/// statement that says less than the C# contract.
/// </summary>
public sealed class ContractStatementTests(M6DependencyFixture fixture, ITestOutputHelper output) : IClassFixture<M6DependencyFixture>
{
    /// <summary>The accepted M6 methods with a proved contract obligation (<c>$contract</c> or <c>$contract_spec</c>).</summary>
    private static readonly string[] Proved =
    [
        "M:Corpus.M6.Contracts.AtMost(System.Int32,System.Int32)",
        "M:Corpus.M6.Contracts.Average(System.Int32,System.Int32)",
        "M:Corpus.M6.Contracts.Capped(System.Int32)",
        "M:Corpus.M6.Contracts.Half(System.Int32)",
        "M:Corpus.M6.Contracts.NonNegative(System.Int32)",
        "M:Corpus.M6.Contracts.Quotient(System.Int32,System.Int32)",
        "M:Corpus.M6.Contracts.Same(System.Int32)",
        "M:Corpus.M6.Dependencies.OrderService.Counted(System.Int32)",
        "M:Corpus.M6.Dependencies.OrderService.QuantityOf(System.Int32)",
        "M:Corpus.M6.Dependencies.OrderService.Reserved(System.Int32)",
        "M:Corpus.M6.Dependencies.Steps.Next(System.Int32)",
        "M:Corpus.M6.Dependencies.Steps.Run(System.Int32)",
        "M:Corpus.M6.Effects.Closed(System.Int32)",
        "M:Corpus.M6.Effects.Guard(System.Int32)",
        "M:Corpus.M6.Nullables.Guarded(Corpus.M6.Payment)",
        "M:Corpus.M6.Nullables.IdOrZero(Corpus.M6.Payment)",
        "M:Corpus.M6.Nullables.ValueWhenKnown(System.Nullable{System.Int32})",
        "M:Corpus.M6.Payments.PaymentLookup.Found(System.Int32)",
        "M:Corpus.M6.Payments.PaymentService.ProcessPayment(System.Int32)",
        "M:Corpus.Rejected.Statements.Throws(System.Int32)",
    ];

    private ContractCorpus Corpus => fixture.Corpus;

    public static TheoryData<string> Methods() => [.. Proved];

    /// <summary>
    /// The methods checked are exactly the accepted function units whose engine outcome admits a contract obligation
    /// (<c>$contract</c>, or <c>$contract_spec</c> for a pure one), so a method that gains one is checked.
    /// </summary>
    [Fact]
    public void EveryProvedObligationIsChecked()
    {
        var proved = Corpus.Side.Extraction.Units
            .Where(u => u.Unit.Kind == VirUnitKind.Function && HasProvedObligation(Corpus.Side.Run, u.Key))
            .Select(u => u.Key);
        Assert.Equal(Proved.Order(StringComparer.Ordinal), proved.Order(StringComparer.Ordinal));
    }

    private static bool HasProvedObligation(EngineResult run, string key) =>
        run.Find(key) is TranslatedOutcome translated
        && translated.Declarations.Any(d => d is TheoremDecl { Value.Name: var n } && (n == LeanNames.Contract(key) || n == LeanNames.ContractSpec(key)));

    [Theory]
    [MemberData(nameof(Methods))]
    public void EveryProvedContractHoldsOnItsClrRuns(string key)
    {
        Assert.True(HasProvedObligation(Corpus.Side.Run, key), $"{key}: its obligation is not proved: {Corpus.Side.Run.Find(key)}");
        var check = StatementCheck.Run(Corpus.Runner, key);
        output.WriteLine($"{key}: {check}");
        check.AssertHolds(key);
    }

    // ---- The check finds what it should ----

    private const string Broken = """
        public sealed class Refused : Exception
        {
            public Refused(string message) : base(message) { }
        }

        public interface ISource
        {
            int Get(int id);
        }

        [ContractFor(typeof(ISource))]
        internal abstract class SourceContract : ISource
        {
            public int Get(int id)
            {
                Spec.Requires(id > 0);
                Spec.Ensures<int>(r => r >= 0);
                return default!;
            }
        }

        public static class Broken
        {
            [Verified]
            public static int Off(int x)
            {
                Spec.Requires(x >= 0 && x < 100);
                Spec.Ensures<int>(r => r > x);
                return x;
            }

            [Verified]
            public static int Divide(int x)
            {
                Spec.Requires(x >= 0);
                return 100 / x;
            }

            [Verified]
            public static int Explicit(int x)
            {
                Spec.Requires(x < 0 || x >= 0);
                if (x < 0) throw new Refused("negative");
                return x;
            }

            [Verified]
            public static int Narrow(int x)
            {
                Spec.Requires(x == 123456789);
                return x;
            }
        }

        public sealed class Reader(ISource source)
        {
            [Verified]
            public int Before(int id)
            {
                Spec.Requires(id > 0);
                Spec.Ensures<int>(r => r >= 0);
                return source.Get(id - 1);
            }
        }
        """;

    /// <summary>
    /// The check reports a false <c>Spec.Ensures</c>, an implicit exception, and a call outside a member's
    /// <c>Spec.Requires</c>, and passes an explicit throw; whatever the engine's outcome for each, which it does not read.
    /// </summary>
    [Fact]
    public void TheCheckReportsEachWayAContractIsBroken()
    {
        using var corpus = ContractCorpus.Inline("Broken.cs", Broken);

        var off = StatementCheck.Run(corpus.Runner, "M:Broken.Off(System.Int32)");
        Assert.Equal(off.Satisfying, off.Failures.Count);
        Assert.Contains("Broken.Off(0) returned 0, which falsifies Spec.Ensures<int>(r => r > x);", off.Failures, StringComparer.Ordinal);

        var divide = StatementCheck.Run(corpus.Runner, "M:Broken.Divide(System.Int32)");
        Assert.NotEmpty(divide.Failures);
        Assert.All(divide.Failures, f => Assert.Equal("Broken.Divide(0) threw DivideByZeroException, which is neither one of its explicit throws [] nor a mock's", f));

        var explicitly = StatementCheck.Run(corpus.Runner, "M:Broken.Explicit(System.Int32)");
        Assert.Empty(explicitly.Failures);
        Assert.True(explicitly.ExplicitThrows > 0 && explicitly.Returned > 0, explicitly.ToString());
        explicitly.AssertHolds("Explicit");

        var before = StatementCheck.Run(corpus.Runner, "M:Reader.Before(System.Int32)");
        Assert.Contains("Reader.Before(1): call 0 to Get(0) falsifies Spec.Requires(id > 0);", before.Failures, StringComparer.Ordinal);
        Assert.True(before.External > 0, before.ToString());
        Assert.Throws<XunitException>(() => before.AssertHolds("Before"));
    }

    /// <summary>
    /// #185: a method whose <c>Spec.Requires</c> almost no generated input satisfies fails the check, rather than pass
    /// having run on (almost) nothing.
    /// </summary>
    [Fact]
    public void TooFewInputsSatisfyingRequiresFail()
    {
        using var corpus = ContractCorpus.Inline("Broken.cs", Broken);
        var narrow = StatementCheck.Run(corpus.Runner, "M:Broken.Narrow(System.Int32)");
        Assert.Empty(narrow.Failures);
        Assert.Equal(StatementCheck.InputBudget, narrow.Tried);
        var failure = Assert.Throws<XunitException>(() => narrow.AssertHolds("Narrow"));
        Assert.Contains($"only {narrow.Satisfying} of the {StatementCheck.InputBudget} inputs generated satisfy its Spec.Requires, and at least {StatementCheck.MinimumSatisfyingInputs} must (#185)", failure.Message, StringComparison.Ordinal);
    }
}
