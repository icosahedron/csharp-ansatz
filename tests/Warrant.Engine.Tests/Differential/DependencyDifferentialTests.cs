using System.Diagnostics;
using System.Globalization;
using System.Text;
using FsCheck;
using FsCheck.Fluent;
using Microsoft.CodeAnalysis.CSharp;
using Warrant.Kernel;
using Warrant.Vir;
using Xunit.Abstractions;
using Xunit.Sdk;

namespace Warrant.Engine.Tests.Differential;

/// <summary>
/// A compilation on both sides for plan M6 U22: extraction and the engine read it, and the CLR runs its
/// <see cref="ContractCompilation"/> copy, with the <c>Spec</c> methods and mocks.
/// </summary>
internal sealed class ContractCorpus : IDisposable
{
    public ContractCorpus(CSharpCompilation compilation)
    {
        Contracts = ContractCompilation.Of(compilation);
        Side = new EffectCorpus(compilation, Contracts.Compilation);
        Runner = new DependencyRunner(Side, Contracts);
    }

    public ContractCompilation Contracts { get; }

    public EffectCorpus Side { get; }

    public DependencyRunner Runner { get; }

    /// <summary>A compilation of inline sources, each with <c>using System; using System.Threading.Tasks; using Warrant;</c>.</summary>
    public static ContractCorpus Inline(string name, string source) =>
        new(Warrant.Frontend.CompilationFactory.Create(
            [new Warrant.Frontend.SourceFile(name, "using System;\nusing System.Threading.Tasks;\nusing Warrant;\n" + source)], checkOverflow: false));

    public void Dispose() => Side.Dispose();
}

/// <summary>
/// The M6 compilations with dependencies on both sides: the accepted one, and (plan M6 U14) the refuted one whose methods
/// call dependencies, built when a test first asks for it.
/// </summary>
public sealed class M6DependencyFixture : IDisposable
{
    /// <summary>The compilations with dependencies.</summary>
    public static readonly string[] Compilations = ["accepted", "refuted-dependencies"];

    private readonly Lazy<ContractCorpus> _refuted = new(() => new ContractCorpus(CorpusSet.M6.Compile("refuted-dependencies")));

    public M6DependencyFixture()
    {
        Corpus = new ContractCorpus(CorpusSet.M6.Compile("accepted"));
    }

    /// <summary>The accepted compilation.</summary>
    internal ContractCorpus Corpus { get; }

    /// <summary>A compilation of <see cref="Compilations"/>.</summary>
    internal ContractCorpus this[string compilation] => compilation == "accepted" ? Corpus : _refuted.Value;

    public void Dispose()
    {
        Corpus.Dispose();
        if (_refuted.IsValueCreated)
        {
            _refuted.Value.Dispose();
        }
    }
}

/// <summary>
/// The M6 corpus's functions with dependencies, and the async functions beside them, agree with the CLR under
/// contract-satisfying mocks (plan M6 U22, R6, R8, R11, KTD21): each run replays a reply tape on both sides
/// (<see cref="DependencyRunner"/>), the model in the world <c>Nat</c>, so the model must make the CLR's calls with the
/// CLR's arguments and end in the CLR's result or exception, the mocks' sentinel matching <c>external</c>.
/// </summary>
public sealed class DependencyDifferentialTests(M6DependencyFixture fixture, ITestOutputHelper output) : IClassFixture<M6DependencyFixture>
{
    /// <summary>The tapes each boundary input runs against, each from its own seed.</summary>
    internal const int TapesPerBoundaryInput = 16;

    private const string ProcessPayment = "M:Corpus.M6.Payments.PaymentService.ProcessPayment(System.Int32)";

    /// <summary>
    /// The functions compared, by compilation: those with dependencies, then the ones in their files without (plan U13 left
    /// them here). A refuted method is compared too, since agreement is about the model, not about whether its contract holds.
    /// </summary>
    private static readonly (string Compilation, string Key)[] Covered =
    [
        ("accepted", ProcessPayment),
        ("accepted", "M:Corpus.M6.Payments.PaymentLookup.Found(System.Int32)"),
        ("accepted", "M:Corpus.M6.Dependencies.OrderService.QuantityOf(System.Int32)"),
        ("accepted", "M:Corpus.M6.Dependencies.OrderService.Counted(System.Int32)"),
        ("accepted", "M:Corpus.M6.Dependencies.OrderService.Reserved(System.Int32)"),
        ("accepted", "M:Corpus.M6.Payments.PaymentService.Validate(Corpus.M6.Payments.Payment)"),
        ("accepted", "M:Corpus.M6.Dependencies.Steps.Next(System.Int32)"),
        ("accepted", "M:Corpus.M6.Dependencies.Steps.Run(System.Int32)"),
        ("refuted-dependencies", "M:Corpus.M6.Refuted.Dependencies.Lookups.Neighbour(System.Int32)"),
        ("refuted-dependencies", "M:Corpus.M6.Refuted.Dependencies.Lookups.Saved(Corpus.M6.Refuted.Dependencies.Payment)"),
        ("refuted-dependencies", "M:Corpus.M6.Refuted.Dependencies.Lookups.Twice(System.Int32)"),
        ("refuted-dependencies", "M:Corpus.M6.Refuted.Dependencies.Lookups.TwiceScripted(System.Int32)"),
        ("refuted-dependencies", "M:Corpus.M6.Refuted.Dependencies.Steps.Next(System.Int32)"),
        ("refuted-dependencies", "M:Corpus.M6.Refuted.Dependencies.Steps.Run(System.Int32)"),
    ];

    /// <summary>The functions with dependencies that are not compared, each with the reason.</summary>
    private static readonly Dictionary<string, string> Skipped = new(StringComparer.Ordinal)
    {
        ["M:Corpus.M6.Refuted.Dependencies.Tally.Size"] =
            "ICounter.Count's contract is unsatisfiable (KTD25), so the engine admits no definition of Size, which calls it",
    };

    private static readonly string[] Namespaces = ["M:Corpus.M6.Payments.", "M:Corpus.M6.Dependencies.", "M:Corpus.M6.Refuted.Dependencies."];

    private ContractCorpus Corpus => fixture.Corpus;

    public static TheoryData<string, string> Functions()
    {
        var data = new TheoryData<string, string>();
        foreach (var (compilation, key) in Covered)
        {
            data.Add(compilation, key);
        }
        return data;
    }

    /// <summary>
    /// The compared and skipped functions are exactly the function units of the M6 corpus's <c>Payments</c> and
    /// <c>Dependencies</c> namespaces (which plan U13's test leaves to this one), in every compilation; each compared one
    /// has an admitted definition, and each skipped one has none, for the reason given.
    /// </summary>
    [Fact]
    public void EveryM6FunctionInTheDependencyFilesIsCompared()
    {
        foreach (var compilation in M6DependencyFixture.Compilations)
        {
            var functions = fixture[compilation].Side.Extraction.Units
                .Where(u => u.Unit.Kind == VirUnitKind.Function && Namespaces.Any(ns => u.Key.StartsWith(ns, StringComparison.Ordinal)))
                .Select(u => u.Key);
            Assert.Equal(
                Covered.Where(c => c.Compilation == compilation).Select(c => c.Key)
                    .Concat(Skipped.Keys.Where(k => fixture[compilation].Side.Extraction.Find(k) is not null))
                    .Order(StringComparer.Ordinal),
                functions.Order(StringComparer.Ordinal));
        }
        foreach (var compilation in M6DifferentialFixture.Compilations.Where(c => c != "accepted"))
        {
            Assert.DoesNotContain(
                CorpusSet.M6.Expected.GetProperty("members").GetProperty(compilation).EnumerateObject(),
                m => Namespaces.Any(ns => m.Name.StartsWith(ns, StringComparison.Ordinal)));
        }
        foreach (var (compilation, key) in Covered)
        {
            var side = fixture[compilation].Side;
            side.AssertDefinitionAdmitted(key);
            output.WriteLine($"{key}: {side.Run.Find(key)!.GetType().Name}, {(side.Unit(key).Unit.Dependencies?.Count ?? 0)} dependencies");
        }
        foreach (var (key, reason) in Skipped)
        {
            Assert.False(fixture["refuted-dependencies"].Side.EngineAdmitted(key), $"{key} is admitted now ({reason}): compare it.");
        }
    }

    /// <summary>Every boundary input, against <see cref="TapesPerBoundaryInput"/> random tapes for a function with dependencies.</summary>
    [Theory]
    [MemberData(nameof(Functions))]
    public void AgreesOnEveryBoundaryCombination(string compilation, string key)
    {
        var corpus = fixture[compilation];
        var unit = corpus.Side.Unit(key).Unit;
        var types = ModelCheck.ParameterTypes(unit);
        var boundaries = corpus.Side.Inputs.BoundaryInputs(types);
        var run = new EffectRun();
        var stats = new TapeStats();
        var check = Checker(corpus, key, stats);
        var tapes = HasDependencies(unit) ? TapesPerBoundaryInput : 1;
        var watch = Stopwatch.StartNew();
        KernelThread.Run(() =>
        {
            for (int i = 0; i < boundaries.Count; i++)
            {
                for (int t = 0; t < tapes; t++)
                {
                    run.Record(check(boundaries[i], (i * tapes) + t));
                }
            }
        });
        output.WriteLine($"{key}: {run.Evaluated} of {run.Checked} runs evaluated ({run.Skipped} skipped), {boundaries.Count} boundary inputs × {tapes} tapes, {stats} in {watch.Elapsed.TotalSeconds:F2} s");
        Assert.True(run.Disagreements.Count == 0, run.Report());
        run.AssertEnoughEvaluated(key);
        stats.AssertTapesVaried(key, unit);
    }

    /// <summary>
    /// The property that the model agrees with the CLR on every input and tape: <see cref="EffectDifferentialTests.RandomInputsPerFunction"/>
    /// cases from the pinned seed, each an input and a tape seed.
    /// </summary>
    [Theory]
    [MemberData(nameof(Functions))]
    public void AgreesOnRandomInputs(string compilation, string key)
    {
        var corpus = fixture[compilation];
        var unit = corpus.Side.Unit(key).Unit;
        var types = ModelCheck.ParameterTypes(unit);
        var arbitrary = corpus.Side.Inputs.Arbitrary([.. types, VirType.Int32]);
        var config = Pbt.Config(EffectDifferentialTests.RandomInputsPerFunction);
        var run = new EffectRun();
        var stats = new TapeStats();
        var check = Checker(corpus, key, stats);
        var watch = Stopwatch.StartNew();
        KernelThread.Run(() => Pbt.Check(
            Prop.ForAll(arbitrary, input =>
            {
                if (run.Record(check(input[..^1], (int)input[^1]!)) is { } disagreement)
                {
                    throw new XunitException(disagreement);
                }
            }),
            config));
        output.WriteLine($"{key}: {run.Evaluated} of {run.Checked} random runs evaluated ({run.Skipped} skipped), {stats} in {watch.Elapsed.TotalSeconds:F2} s");
        Assert.Equal(config.MaxTest, run.Checked);
        run.AssertEnoughEvaluated(key);
        stats.AssertTapesVaried(key, unit);
    }

    private static bool HasDependencies(VirUnit unit) => unit.Dependencies is { Count: > 0 };

    /// <summary>One run's check: against a random tape with a function's dependencies, as plan U13 checks one without.</summary>
    private static Func<object?[], int, InputCheck> Checker(ContractCorpus corpus, string key, TapeStats stats)
    {
        var unit = corpus.Side.Unit(key);
        if (!HasDependencies(unit.Unit))
        {
            var check = corpus.Side.Checker(unit);
            return (args, _) => check(args);
        }
        corpus.Side.AssertDefinitionAdmitted(key);
        return (args, seed) =>
        {
            var clr = corpus.Runner.RunClr(unit.Unit, [args], new RandomReplies(corpus.Runner, seed));
            stats.Add(clr);
            return corpus.Runner.Check(unit.Unit, [args], clr);
        };
    }

    // ---- ProcessPayment's tapes (plan U22's scenarios) ----

    private object Payment(int id, decimal amount, string status) =>
        Activator.CreateInstance(
            Corpus.Side.Assembly.TypeOf("T:Corpus.M6.Payments.Payment"),
            id, amount, Enum.Parse(Corpus.Side.Assembly.TypeOf("T:Corpus.M6.Payments.PaymentStatus"), status))!;

    private const string GetPayment = "M:Corpus.M6.Payments.IPaymentStore.GetPayment(System.Int32)";

    /// <summary>
    /// <c>ProcessPayment</c> agrees with the CLR for tapes whose <c>GetPayment</c> returns null, a matching pending payment,
    /// one whose status is not pending, and one whose amount is not positive, and for a mock that throws from either
    /// member (the external path); each CLR outcome and call sequence is pinned so the agreement is about what was meant.
    /// </summary>
    [Fact]
    public void ProcessPaymentAgreesOnEachScriptedTape()
    {
        var unit = Corpus.Side.Unit(ProcessPayment).Unit;
        var scripts = new (string Name, int Id, Func<string, int, object?[], Reply> Reply, string Clr, int Calls)[]
        {
            ("a non-positive id", 0, (_, _, _) => throw new InvalidOperationException("no call expected"), "InvalidId", 0),
            ("null", 7, (m, _, _) => m == GetPayment ? Reply.Of(null) : Reply.Of(null), "NotFound", 1),
            ("a matching pending payment", 7, (m, _, a) => m == GetPayment ? Reply.Of(Payment((int)a[0]!, 12.50m, "Pending")) : Reply.Of(null), "Success", 2),
            ("a payment that is not pending", 7, (m, _, a) => m == GetPayment ? Reply.Of(Payment((int)a[0]!, 12.50m, "Processed")) : Reply.Of(null), "Success", 2),
            ("a payment of no amount", 7, (m, _, a) => m == GetPayment ? Reply.Of(Payment((int)a[0]!, 0.00m, "Pending")) : Reply.Of(null), "Invalid", 1),
            ("GetPayment throws", 7, (m, _, _) => m == GetPayment ? Reply.Throw : Reply.Of(null), "MockException", 1),
            ("SavePayment throws", 7, (m, _, a) => m == GetPayment ? Reply.Of(Payment((int)a[0]!, 1m, "Pending")) : Reply.Throw, "MockException", 2),
        };
        foreach (var (name, id, reply, expected, calls) in scripts)
        {
            var clr = Corpus.Runner.RunClr(unit, [[id]], new ScriptedReplies(reply));
            var (result, thrown) = clr.Outcomes[0];
            Assert.Equal(expected, thrown?.GetType().Name ?? result!.ToString());
            Assert.Equal(calls, clr.Tape.Calls.Count);
            var check = KernelThread.Run(() => Corpus.Runner.Check(unit, [[id]], clr));
            Assert.True(check == InputCheck.Agrees, $"{name}: {check.Disagreement}");
            output.WriteLine($"{name}: {expected} after [{string.Join("; ", clr.Tape.Calls.Select(Corpus.Runner.Display))}]");
        }
        // The saved payment is the fetched one, processed: the arguments the model passes are checked against these.
        var saved = Corpus.Runner.RunClr(unit, [[7]], new ScriptedReplies(scripts[2].Reply)).Tape.Calls[1];
        Assert.Equal("SavePayment(new Payment(7, 12.50m, PaymentStatus.Processed)) → ()", Corpus.Runner.Display(saved));
    }

    /// <summary>
    /// Two calls of <c>ProcessPayment</c> on one service see different payments: the second runs from the world the first
    /// left, so its <c>GetPayment</c> reads the tape's later entry, and both outcomes and the four calls agree.
    /// </summary>
    [Fact]
    public void ProcessPaymentAgreesOnSuccessiveCallsThatSeeDifferentPayments()
    {
        var unit = Corpus.Side.Unit(ProcessPayment).Unit;
        var source = new ScriptedReplies((m, i, a) => m != GetPayment
            ? Reply.Of(null)
            : Reply.Of(i == 0 ? Payment((int)a[0]!, 5m, "Pending") : Payment((int)a[0]!, -5m, "Pending")));
        object?[][] invocations = [[7], [7]];
        var clr = Corpus.Runner.RunClr(unit, invocations, source);
        Assert.Equal(["Success", "Invalid"], clr.Outcomes.Select(o => o.Result!.ToString()));
        Assert.Equal(3, clr.Tape.Calls.Count);
        var check = KernelThread.Run(() => Corpus.Runner.Check(unit, invocations, clr));
        Assert.True(check == InputCheck.Agrees, check.Disagreement);

        // Replayed from the start instead, the second call would read the first payment: the worlds matter.
        var fresh = KernelThread.Run(() => Corpus.Runner.Check(unit, [[7]], clr.Tape.Calls, [clr.Outcomes[1]]));
        Assert.NotNull(fresh.Disagreement);
    }

    /// <summary>
    /// The sentinel a mock throws matches <c>external</c> and nothing else, and <c>external</c> matches nothing else: a
    /// run whose <c>GetPayment</c> throws ends in <c>error external</c>, and the CLR exceptions an implicit or explicit
    /// error stands for do not match it.
    /// </summary>
    [Fact]
    public void AMockThatThrowsTakesTheExternalPath()
    {
        var unit = Corpus.Side.Unit(ProcessPayment).Unit;
        var clr = Corpus.Runner.RunClr(unit, [[3]], new ScriptedReplies((_, _, _) => Reply.Throw));
        Assert.IsType<MockException>(clr.Outcomes[0].Thrown);
        Assert.Equal([ClrExceptions.Constructor(ClrExceptions.External)], ClrExceptions.ModelErrors(new MockException()));
        KernelThread.Run(() =>
        {
            Assert.Same(InputCheck.Agrees, Corpus.Runner.Check(unit, [[3]], clr));
            foreach (var other in new Exception[] { new InvalidOperationException(), new DivideByZeroException(), new OverflowException() })
            {
                var check = Corpus.Runner.Check(unit, [[3]], clr.Tape.Calls, [(null, other)]);
                Assert.Contains($"the CLR threw {other.GetType().Name} but the model computes error external", check.Disagreement, StringComparison.Ordinal);
            }
        });
    }

    /// <summary>
    /// #188: the model is checked to make the CLR's calls with the CLR's arguments. A call recorded with another argument
    /// (as if the translation passed a wrong id, or saved the payment unprocessed), a call to another member, a missing call
    /// and an extra one are each a disagreement naming it, though <c>ProcessPayment</c>'s result does not depend on them.
    /// </summary>
    [Fact]
    public void ACallWithOtherArgumentsOrInAnotherOrderIsCaught()
    {
        var unit = Corpus.Side.Unit(ProcessPayment).Unit;
        var clr = Corpus.Runner.RunClr(unit, [[7]], new ScriptedReplies((m, _, a) => m == GetPayment ? Reply.Of(Payment((int)a[0]!, 1m, "Pending")) : Reply.Of(null)));
        var calls = clr.Tape.Calls;
        var get = calls[0];
        var save = calls[1];
        var cases = new (string Name, RecordedCall[] Calls, string Message)[]
        {
            ("another id", [get with { Args = [8] }, save], "call 0 to store.GetPayment has other arguments in the model than the CLR's (8)"),
            ("the payment saved unprocessed", [get, save with { Args = [Payment(7, 1m, "Pending")] }], "call 1 to store.SavePayment has other arguments in the model than the CLR's (new Payment(7, 1m, PaymentStatus.Pending))"),
            ("the payment saved at another scale", [get, save with { Args = [Payment(7, 1.0m, "Processed")] }], "call 1 to store.SavePayment has other arguments"),
            ("the calls swapped", [save with { Index = 0 }, get with { Index = 1 }], "call 0 is to store.GetPayment in the model but to SavePayment"),
            ("a call missing", [get], "store.SavePayment was called after the CLR's last call (it made 1)"),
            ("an extra call", [get, save, save with { Index = 2 }], "the CLR made 3 external calls"),
        };
        KernelThread.Run(() =>
        {
            Assert.Same(InputCheck.Agrees, Corpus.Runner.Check(unit, [[7]], clr));
            foreach (var (name, recorded, message) in cases)
            {
                var check = Corpus.Runner.Check(unit, [[7]], recorded, clr.Outcomes);
                Assert.True(check.Disagreement?.Contains(message, StringComparison.Ordinal) == true, $"{name}: {check.Disagreement ?? "agrees"}");
            }
        });
    }

    // ---- Replies that keep a contract ----

    private const string Codes = """
        public interface ICodes { int Code(int id); }

        [ContractFor(typeof(ICodes))]
        internal abstract class CodesContract : ICodes
        {
            public int Code(int id)
            {
                Spec.Ensures<int>(r => r == id + 12345);
                return default!;
            }
        }

        public sealed class Coder(ICodes codes)
        {
            [Verified]
            public int Get(int id) => codes.Code(id);
        }
        """;

    /// <summary>
    /// A member for which no generated reply satisfies its <c>Spec.Ensures</c> within <see cref="DependencyRunner.ReplyBudget"/>
    /// candidates fails the test, rather than run the method against a reply that breaks the contract; a reply that keeps
    /// it is used.
    /// </summary>
    [Fact]
    public void AMemberWithNoReplyThatKeepsItsContractFailsTheTest()
    {
        using var corpus = ContractCorpus.Inline("Codes.cs", Codes);
        var unit = corpus.Side.Unit("M:Coder.Get(System.Int32)").Unit;
        var failures = new List<string>();
        for (int seed = 0; seed < 8; seed++)
        {
            try
            {
                var clr = corpus.Runner.RunClr(unit, [[1]], new RandomReplies(corpus.Runner, seed));
                Assert.IsType<MockException>(clr.Outcomes[0].Thrown);
            }
            catch (XunitException ex)
            {
                failures.Add(ex.Message);
            }
        }
        Assert.NotEmpty(failures);
        Assert.All(failures, f => Assert.Contains(
            $"no reply to call 0, Code(1), satisfies its Spec.Ensures within {DependencyRunner.ReplyBudget} candidates", f, StringComparison.Ordinal));

        var kept = corpus.Runner.RunClr(unit, [[1]], new ScriptedReplies((_, _, a) => Reply.Of((int)a[0]! + 12345)));
        Assert.Equal(12346, kept.Outcomes[0].Result);
        Assert.Throws<XunitException>(() => corpus.Runner.RunClr(unit, [[1]], new ScriptedReplies((_, _, _) => Reply.Of(0))));
    }

    // ---- Cost ----

    /// <summary>
    /// The cost measurement for the functions with dependencies (README.md, "Measured cost"): fuel and wall clock per run,
    /// on their boundary inputs against <see cref="TapesPerBoundaryInput"/> tapes each. Opt-in, like the others.
    /// </summary>
    [FactRequiringEnv("WARRANT_DIFFERENTIAL_COST")]
    public void MeasureTheCostOfADependencyCheck()
    {
        var table = new StringBuilder("| Function | Runs | Calls per run (mean) | Fuel per run (mean / max) | ms per run (mean) |\n|---|---|---|---|---|\n");
        foreach (var key in Covered.Where(c => c.Compilation == "accepted").Select(c => c.Key).Where(k => !HasDependencies(Corpus.Side.Unit(k).Unit)))
        {
            // As plan U13 measures a function without dependencies: one run per boundary input.
            var unit = Corpus.Side.Unit(key);
            var inputs = Corpus.Side.Inputs.BoundaryInputs(ModelCheck.ParameterTypes(unit.Unit));
            var method = Corpus.Side.Assembly.MethodOf(unit.Unit);
            var check = Corpus.Side.Checker(unit);
            var measured = KernelThread.Run(() => inputs.Select(i => EffectDifferentialTests.Measure(Corpus.Side, unit.Unit, method, i)).ToList());
            var watch = Stopwatch.StartNew();
            KernelThread.Run(() =>
            {
                foreach (var input in inputs)
                {
                    Assert.Same(InputCheck.Agrees, check(input));
                }
            });
            table.Append(CultureInfo.InvariantCulture, $"| `{unit.DisplayName}` | {inputs.Count} | 0 | {measured.Average():F0} / {measured.Max()} | {watch.Elapsed.TotalMilliseconds / inputs.Count:F2} |\n");
        }
        foreach (var key in Covered.Where(c => c.Compilation == "accepted").Select(c => c.Key).Where(k => HasDependencies(Corpus.Side.Unit(k).Unit)))
        {
            var unit = Corpus.Side.Unit(key).Unit;
            var boundaries = Corpus.Side.Inputs.BoundaryInputs(ModelCheck.ParameterTypes(unit));
            var fuel = new List<long>();
            var calls = 0;
            var watch = new Stopwatch();
            KernelThread.Run(() =>
            {
                for (int i = 0; i < boundaries.Count; i++)
                {
                    for (int t = 0; t < TapesPerBoundaryInput; t++)
                    {
                        watch.Start();
                        var clr = Corpus.Runner.RunClr(unit, [boundaries[i]], new RandomReplies(Corpus.Runner, (i * TapesPerBoundaryInput) + t));
                        Assert.Same(InputCheck.Agrees, Corpus.Runner.Check(unit, [boundaries[i]], clr));
                        watch.Stop();
                        calls += clr.Tape.Calls.Count;
                        fuel.Add(Measure(unit, boundaries[i], clr));
                    }
                }
            });
            table.Append(CultureInfo.InvariantCulture, $"| `{Corpus.Side.Unit(key).DisplayName}` | {fuel.Count} | {(double)calls / fuel.Count:F2} | {fuel.Average():F0} / {fuel.Max()} | {watch.Elapsed.TotalMilliseconds / fuel.Count:F2} |\n");
        }
        output.WriteLine(table.ToString());
    }

    /// <summary>The fuel of a run's agreeing checks: its outcome, and its number of calls.</summary>
    private long Measure(VirUnit unit, object?[] input, DependencyRunner.ClrRun clr)
    {
        var model = Corpus.Side.Model;
        var r = Values.CicType(ModelCheck.Returned(unit));
        var pair = model.WorldRun(unit, Corpus.Runner.Operations(unit, clr.Tape.Calls), input, Cic.Expr.NatLit(0));
        var outcome = ModelCheck.OutcomeOfRun(r, pair);
        var (result, thrown) = clr.Outcomes[0];
        var expected = thrown is null
            ? ModelCheck.Ok(r, model.Values.Term(ModelCheck.Returned(unit), result))
            : ClrExceptions.ModelErrors(thrown).Select(e => ModelCheck.Error(r, e)).First(o => model.Equal(ModelCheck.Except(r), outcome, o));
        return model.Measure(ModelCheck.Theorem(ModelCheck.Except(r), outcome, expected)).Fuel
            + model.Measure(ModelCheck.Theorem(ModelCheck.Nat, ModelCheck.WorldAfter(r, pair), Cic.Expr.NatLit(clr.Tape.Calls.Count))).Fuel;
    }

    /// <summary>What the tapes of a test did: runs, calls per member, sentinel replies, and runs that ended in the sentinel.</summary>
    private sealed class TapeStats
    {
        private readonly Dictionary<string, int> _calls = new(StringComparer.Ordinal);

        public int Runs { get; private set; }

        public int Thrown { get; private set; }

        public int External { get; private set; }

        public int NullReplies { get; private set; }

        public void Add(DependencyRunner.ClrRun run)
        {
            Runs++;
            foreach (var call in run.Tape.Calls)
            {
                _calls[Tape.Short(call.Member)] = _calls.GetValueOrDefault(Tape.Short(call.Member)) + 1;
                Thrown += call.Reply.Throws ? 1 : 0;
                NullReplies += !call.Reply.Throws && call.Reply.Value is null ? 1 : 0;
            }
            External += run.Outcomes[0].Thrown is MockException ? 1 : 0;
        }

        /// <summary>A function with dependencies must have called each of its members, and ended in the sentinel at least once.</summary>
        public void AssertTapesVaried(string key, VirUnit unit)
        {
            if (unit.Dependencies is not { Count: > 0 } dependencies)
            {
                return;
            }
            foreach (var member in dependencies.SelectMany(d => d.Members))
            {
                Assert.True(_calls.GetValueOrDefault(Tape.Short(member)) > 0, $"{key}: no run called {member}: {this}");
            }
            Assert.True(External > 0, $"{key}: no run took the external path: {this}");
        }

        public override string ToString() => Runs == 0
            ? "no tapes"
            : $"{Runs} tapes, calls [{string.Join(", ", _calls.OrderBy(p => p.Key, StringComparer.Ordinal).Select(p => $"{p.Key} {p.Value}"))}], {Thrown} sentinel replies, {NullReplies} null or unit replies, {External} runs ended in the sentinel";
    }
}
