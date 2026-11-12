using Warrant.Engine.Contracts;
using Warrant.Engine.Reports;
using Warrant.Vir;

namespace Warrant.Engine.Tests;

/// <summary>
/// External calls in the VC walker (plan M6 U20, KTD9, KTD13, design D9): at a call to a dependency member, the member's
/// contract hypothesis is instantiated at the call's arguments and the current world, its <c>Spec.Requires</c> is a VC at the
/// call, its <c>Spec.Ensures</c> a hypothesis of the rest, and an exception from it is allowed and reported as
/// <c>MayThrow</c>. Two calls are unrelated unless the contract relates them (KTD4).
/// </summary>
public sealed class ExternalCallTests(EngineFixture engine) : IClassFixture<EngineFixture>
{
    private EngineResult Run(string source) =>
        Pipeline.Run(EngineCorpus.Inputs(EngineCorpus.Inline(source)), engine.Bundle, engine.Options);

    /// <summary>The source text of a node of an inline source's unit.</summary>
    private static string Text(string source, string key, int? node)
    {
        var span = OutcomeText.SpanOf(EngineCorpus.Inline(source).Units.Single(u => u.Key == key).Spans, node);
        Assert.NotNull(span);
        var lines = ("using Warrant;\n" + source).Split('\n');
        Assert.Equal(span.StartLine, span.EndLine);
        return lines[span.StartLine - 1][(span.StartColumn - 1)..(span.EndColumn - 1)].Trim();
    }

    private static void Proved(UnitOutcome? outcome) =>
        Assert.True(outcome is TranslatedOutcome t && t.Declarations.Any(d => d is Kernel.TheoremDecl), Describe(outcome));

    private static string Describe(UnitOutcome? outcome) =>
        outcome is NotProvedOutcome n ? string.Join("\n----\n", n.Vcs.Select(v => $"{v.Kind}: {v.Message}\n{v.Goals}").Prepend(n.Message + "\n" + n.Goals)) : $"{outcome}";

    /// <summary>The one failing VC of a method: its kind and the source text at its node.</summary>
    private static (VcKind Kind, string Text) Failure(string source, string key, UnitOutcome? outcome)
    {
        var notProved = Assert.IsType<NotProvedOutcome>(outcome);
        Assert.True(notProved.Vcs.Length == 1, Describe(outcome));
        var vc = notProved.Vcs[0];
        Assert.StartsWith(VcKinds.Text(vc.Kind), notProved.Message, StringComparison.Ordinal);
        return (vc.Kind, Text(source, key, vc.Node));
    }

    /// <summary>Design §5.2's store, with an <c>int</c> amount: <c>GetPayment</c> promises the id, <c>SavePayment</c> nothing.</summary>
    private const string Store = """
        using System.Threading.Tasks;

        public sealed record Payment(int Id, int Amount);

        public interface IStore
        {
            Task<Payment?> GetPayment(int id);
            Task SavePayment(Payment p);
        }

        [ContractFor(typeof(IStore))]
        internal abstract class StoreContract : IStore
        {
            public Task<Payment?> GetPayment(int id)
            {
                Spec.Ensures<Payment?>(r => r is null || r.Id == id);
                return default!;
            }

            public Task SavePayment(Payment p) => default!;
        }

        """;

    private static string WithStore(string members) => Store + "public sealed class S(IStore store)\n{\n" + members + "\n}\n";

    /// <summary>
    /// The milestone's headline (design §5.2, plan M6 Success Criteria): ProcessPayment's obligation, which binds the store's
    /// two operations and their contracts as hypotheses, is proved by the default procedure with no script, and the kernel
    /// admits it as <c>$contract</c>.
    /// </summary>
    [Fact]
    public void ProcessPaymentsObligationProvesUnderTheDefaultProcedure()
    {
        const string Key = "M:Corpus.M6.Payments.PaymentService.ProcessPayment(System.Int32)";
        var outcome = engine.Run("m6/accepted").Find(Key);
        Proved(outcome);
        var theorem = Assert.Single(((TranslatedOutcome)outcome!).Declarations.OfType<Kernel.TheoremDecl>());
        Assert.EndsWith("$contract", theorem.Value.Name.ToString(), StringComparison.Ordinal);
        var unit = engine.Inputs("m6/accepted").Single(u => u.Unit.Key == Key).Unit;
        Assert.Null(unit.Script);
        // Two operations, GetPayment's and SavePayment's, so two contract hypotheses, each used at its call.
        var contract = Semantics.Translator.Translate(engine.Inputs("m6/accepted").Select(u => u.Unit), engine.Bundle.Env).Find(Key)!.Contract!;
        Assert.Equal(2, contract.Operations);
        Assert.Equal(
            ["M:Corpus.M6.Payments.IPaymentStore.GetPayment(System.Int32)", "M:Corpus.M6.Payments.IPaymentStore.SavePayment(Corpus.M6.Payments.Payment)"],
            outcome!.Assumptions.Where(a => a.Assumption.Kind == VirAssumptionKind.MayThrow).Select(a => MayThrowSubject.Parse(a.Assumption.Subject).Thrown));
    }

    [Fact]
    public void AnEnsuresThatHoldsOnlyThroughTheMembersContractProves()
    {
        var source = WithStore("""
            [Verified]
            public async Task<bool> Found(int id)
            {
                Spec.Ensures<bool>(r => r);
                var p = await store.GetPayment(id);
                return p is null || p.Id == id;
            }

            [Verified]
            public async Task<Payment?> Get(int id)
            {
                Spec.Ensures<Payment?>(r => r is null || r.Id == id);
                return await store.GetPayment(id);
            }
            """);
        var result = Run(source);
        Proved(result.Find("M:S.Found(System.Int32)"));
        Proved(result.Find("M:S.Get(System.Int32)"));
    }

    /// <summary>
    /// #226: each read of a field of the awaited result cases on it anew, so the walk names its value twice; the two names
    /// are of one value (<c>some v₁ = some v₂</c>), and a fact about the first, from a null test or the contract, is a fact
    /// about the second.
    /// </summary>
    [Fact]
    public void AFieldOfANullableResultReadAfterANullTestIsRelatedToWhatTheWalkLearned()
    {
        var source = WithStore("""
            [Verified]
            public async Task<int> AmountOrZero(int id)
            {
                Spec.Ensures<int>(r => r >= 0);
                var p = await store.GetPayment(id);
                if (p is null || p.Amount < 0) return 0;
                return p.Amount;
            }

            [Verified]
            public async Task<int> IdAfterAmount(int id)
            {
                Spec.Ensures<int>(r => r == 0 || r == id);
                var p = await store.GetPayment(id);
                if (p is null || p.Amount < 0) return 0;
                return p.Id;
            }
            """);
        var result = Run(source);
        Proved(result.Find("M:S.AmountOrZero(System.Int32)"));
        Proved(result.Find("M:S.IdAfterAmount(System.Int32)"));
    }

    [Fact]
    public void AFieldOfANullableResultThatNothingBoundsStillFails()
    {
        var source = WithStore("""
            [Verified]
            public async Task<int> AmountOrZero(int id)
            {
                Spec.Ensures<int>(r => r >= 0);
                var p = await store.GetPayment(id);
                if (p is null || p.Id < 0) return 0;
                return p.Amount;
            }
            """);
        const string Key = "M:S.AmountOrZero(System.Int32)";
        Assert.Equal((VcKind.Postcondition, "Spec.Ensures<int>(r => r >= 0);"), Failure(source, Key, Run(source).Find(Key)));
    }

    [Fact]
    public void TheSameEnsuresFailsAtItsLineWhenTheCallAsksForAnotherId()
    {
        var source = WithStore("""
            [Verified]
            public async Task<bool> Neighbour(int id)
            {
                Spec.Requires(id < int.MaxValue);
                Spec.Ensures<bool>(r => r);
                var p = await store.GetPayment(id + 1);
                return p is null || p.Id == id;
            }
            """);
        const string Key = "M:S.Neighbour(System.Int32)";
        Assert.Equal((VcKind.Postcondition, "Spec.Ensures<bool>(r => r);"), Failure(source, Key, Run(source).Find(Key)));
    }

    [Fact]
    public void AnEnsuresThatReliesOnAPropertySavePaymentsContractDoesNotGiveFails()
    {
        // SavePayment's `=> default!` contract promises nothing: not that GetPayment then finds the payment.
        var source = WithStore("""
            [Verified]
            public async Task<bool> Saved(Payment p)
            {
                Spec.Ensures<bool>(r => r);
                await store.SavePayment(p);
                var q = await store.GetPayment(p.Id);
                return q is not null;
            }
            """);
        const string Key = "M:S.Saved(Payment)";
        Assert.Equal((VcKind.Postcondition, "Spec.Ensures<bool>(r => r);"), Failure(source, Key, Run(source).Find(Key)));
    }

    [Fact]
    public void TwoCallsWithTheSameArgumentAreUnrelatedSoAProofThatTheyAgreeFails()
    {
        // KTD4, #96: the world threads through the calls, so the two results are two values the contract says little about.
        var source = WithStore("""
            [Verified]
            public async Task<bool> Twice(int id)
            {
                Spec.Ensures<bool>(r => r);
                var a = await store.GetPayment(id);
                var b = await store.GetPayment(id);
                return (a is null) == (b is null);
            }
            """);
        const string Key = "M:S.Twice(System.Int32)";
        Assert.Equal((VcKind.Postcondition, "Spec.Ensures<bool>(r => r);"), Failure(source, Key, Run(source).Find(Key)));
    }

    private const string Orders = """
        public interface IOrders { int Count(int id); }

        [ContractFor(typeof(IOrders))]
        internal abstract class OrdersContract : IOrders
        {
            public int Count(int id)
            {
                Spec.Requires(id > 0);
                Spec.Ensures<int>(r => r >= 0);
                return default!;
            }
        }

        public sealed class S(IOrders orders)
        {
            [Verified]
            public int Checked(int id)
            {
                Spec.Requires(id > 0);
                Spec.Ensures<int>(r => r >= 0);
                return orders.Count(id);
            }

            [Verified]
            public int Unchecked(int id)
            {
                return orders.Count(id);
            }
        }
        """;

    [Fact]
    public void AMembersRequiresIsAVcAtTheCall()
    {
        var result = Run(Orders);
        Proved(result.Find("M:S.Checked(System.Int32)"));
        const string Key = "M:S.Unchecked(System.Int32)";
        Assert.Equal((VcKind.DependencyPrecondition, "orders.Count(id)"), Failure(Orders, Key, result.Find(Key)));
        Assert.StartsWith("precondition of a dependency member at this call", VcKinds.Text(VcKind.DependencyPrecondition), StringComparison.Ordinal);
    }

    [Fact]
    public void AnExceptionFromTheMemberIsAMayThrowAtTheCall()
    {
        var source = WithStore("""
            [Verified]
            public async Task<Payment?> Get(int id)
            {
                Spec.Ensures<Payment?>(r => r is null || r.Id == id);
                return await store.GetPayment(id);
            }
            """);
        const string Key = "M:S.Get(System.Int32)";
        var outcome = Run(source).Find(Key);
        Proved(outcome);
        var mayThrow = Assert.Single(outcome!.Assumptions, a => a.Assumption.Kind == VirAssumptionKind.MayThrow);
        var subject = MayThrowSubject.Parse(mayThrow.Assumption.Subject);
        Assert.Equal("M:IStore.GetPayment(System.Int32)", subject.Thrown);
        Assert.Equal("store.GetPayment(id)", Text(source, Key, subject.Node));
        // The member's contract and the dependency's non-null assumptions come from extraction (KTD9, #71, #223).
        Assert.Contains(outcome.Assumptions, a => a.Assumption == new VirAssumption(VirAssumptionKind.ExternalContract, "M:IStore.GetPayment(System.Int32)"));
        Assert.Contains(outcome.Assumptions, a => a.Assumption == new VirAssumption(VirAssumptionKind.NonNull, "store"));
    }

    [Fact]
    public void AnObligationClosedStraightFromTheMembersContractStillListsIt()
    {
        // #223: `Size() => counter.Count()` is the member's own contract; the report still lists it.
        const string Source = """
            public interface ICounter { int Count(); }

            [ContractFor(typeof(ICounter))]
            internal abstract class CounterContract : ICounter
            {
                public int Count() { Spec.Ensures<int>(r => r >= 0); return default!; }
            }

            public sealed class S(ICounter counter)
            {
                [Verified]
                public int Size()
                {
                    Spec.Ensures<int>(r => r >= 0);
                    return counter.Count();
                }
            }
            """;
        var inputs = EngineCorpus.Inputs(EngineCorpus.Inline(Source));
        var result = Pipeline.Run(inputs, engine.Bundle, engine.Options);
        Proved(result.Find("M:S.Size"));
        var report = AssumptionReports.Build(result, inputs, new ReportSettings(CheckOverflow: false, Bundle: "b"), SourceText(Source));
        Assert.Contains(
            report.Find("M:S.Size")!.Assumptions,
            a => a.Kind == VirAssumptionKind.ExternalContract && a.Text == "Every implementation of ICounter.Count() keeps its contract: Spec.Ensures<int>(r => r >= 0)");
    }

    [Fact]
    public void AnUnsupportedShapeAfterACallIsReportedAtAnode()
    {
        // #223: a leftover the walker has no rule for carries the node where the walk stopped, so it has a line.
        var source = """
            [Closed] public enum Light { Red, Green }

            public static class S
            {
                [Verified]
                public static Light Flip(Light l) => l == Light.Red ? Light.Green : Light.Red;

                [Verified]
                public static int Rank(Light l, int a, int b)
                {
                    var c = checked(a + 1);
                    return Flip(l) switch { Light.Red => b / c, _ => 0 };
                }
            }
            """;
        var outcome = Assert.IsType<NotProvedOutcome>(Run(source).Find("M:S.Rank(Light,System.Int32,System.Int32)"));
        var unsupported = Assert.Single(outcome.Vcs, v => v.Kind == VcKind.Unsupported);
        Assert.NotNull(unsupported.Node);
    }

    /// <summary>Reads a single-line span of an inline source.</summary>
    internal static Func<VirSpan, string?> SourceText(string source) => span =>
    {
        var lines = ("using Warrant;\n" + source).Split('\n');
        return span.StartLine == span.EndLine ? lines[span.StartLine - 1][(span.StartColumn - 1)..(span.EndColumn - 1)] : null;
    };
}
