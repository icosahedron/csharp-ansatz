using System.Diagnostics;
using System.Globalization;
using System.Text;
using System.Text.Json;
using Warrant.Engine.Service;
using Warrant.Meta;
using Warrant.Vir;

namespace Warrant.Engine.Tests;

/// <summary>A verification service over the test process's bundle and sidecar, with four workers.</summary>
public sealed class ServiceFixture : IDisposable
{
    public VerificationService Service { get; } = new(EngineFixture.SharedBundle.Value, EngineFixture.SharedSidecar.Value, workers: 4);

    public void Dispose() => Service.Dispose();
}

/// <summary>
/// The verification service (M5b plan U5, KTD1, KTD6, KTD8, KTD10, KTD32, KTD33; R3, R5, R6, R7): one request's theorems run
/// level by level on a pool of workers, each in its own fork, and the outcomes are those of a sequential run, in the
/// request's order.
/// </summary>
public sealed class ServiceTests(EngineFixture engine, ServiceFixture fixture) : IClassFixture<EngineFixture>, IClassFixture<ServiceFixture>
{
    private const string Lemmas = """
        public static class S
        {
            [Verified] public static int Twice(int x) => x + x;

            [Theorem]
            static Proof Lemma() => Prove.That(Spec.ForAll<int>(x => Twice(x) == unchecked(x + x))).By(Tactic.Intro("x"), Tactic.Exact(Lean.Const("rfl")));

            [Theorem] static Proof User(int a) => Prove.That(Twice(a) == unchecked(a + a)).By(Tactic.Apply(nameof(Lemma)));
        }
        """;

    private VerificationService Service => fixture.Service;

    [Fact]
    public void TheM5aAndM4CorporaGetThePipelinesOutcomesThroughTheService()
    {
        var compilations = CorpusSet.M5a.Names.Select(n => $"m5a/{n}").Concat(CorpusSet.M4.Names).ToList();
        foreach (var compilation in compilations)
        {
            var inputs = engine.Inputs(compilation);
            var response = Service.Verify(Request(inputs, engine.Options));
            Assert.Equal(Texts(engine.Run(compilation).Units), Texts(response));
        }
        Assert.Contains("m5a/refuted", compilations);
    }

    [Fact]
    public void SixteenIndependentTheoremsComeBackInRequestOrderTheSameEveryTime()
    {
        var source = new StringBuilder("public static class S\n{\n    [Verified] public static int Inc(int x) => x + 1;\n");
        for (int i = 0; i < 16; i++)
        {
            // Even theorems are proved; odd ones are not, with the counterexample x = 2147483647.
            source.Append(i % 2 == 0
                ? string.Create(CultureInfo.InvariantCulture, $"    [Theorem] static Proof T{i:00}(int x) => Prove.That(unchecked(Inc(x) + {i} == x + 1 + {i})).By(Tactic.Unfold(nameof(Inc)), Tactic.Omega());\n")
                : string.Create(CultureInfo.InvariantCulture, $"    [Theorem] static Proof T{i:00}(int x) => Prove.That(Inc(x) > x).By(Tactic.Unfold(nameof(Inc)), Tactic.Omega());\n"));
        }
        source.Append('}');
        // Requested in reverse key order, so request order is not the order a sorted run would give.
        var inputs = EngineCorpus.Inputs(EngineCorpus.Inline(source.ToString())).Reverse().ToList();
        var request = Request(inputs, engine.Options);
        var sequential = Texts(Pipeline.Run(inputs, engine.Bundle, engine.Options).Units);

        Assert.Equal(4, Service.Workers);
        for (int run = 0; run < 10; run++)
        {
            var response = Service.Verify(request);
            Assert.Equal(inputs.Select(u => u.Unit.Key), response.Units.Select(u => u.Outcome.Key));
            Assert.Equal(sequential, Texts(response));
        }
        var outcomes = Service.Verify(request).Units.Select(u => u.Outcome).Where(o => o.UnitKind == VirUnitKind.Theorem).ToList();
        Assert.Equal(8, outcomes.Count(o => o.Kind == OutcomeKind.Proved));
        Assert.Equal(8, outcomes.Count(o => o.Kind == OutcomeKind.NotProved && o.Counterexample.Single().Value == "2147483647"));
    }

    [Fact]
    public void ATheoremThatTimesOutDoesNotDelayTheOthers()
    {
        var source = new StringBuilder(Chain(24));
        source.Append("    [Theorem(TimeoutSeconds = 2)] static Proof Slow() => Prove.That(A24(0) > 0);\n");
        for (int i = 0; i < 6; i++)
        {
            source.Append(CultureInfo.InvariantCulture, $"    [Theorem] static Proof Fast{i}() => Prove.That(A0({i}) == {i + 1});\n");
        }
        source.Append('}');
        var inputs = EngineCorpus.Inputs(EngineCorpus.Inline(source.ToString()));
        var options = engine.Options with { Kernel = engine.Options.Kernel with { Fuel = long.MaxValue } };

        var response = Service.Verify(Request(inputs, options));

        var slow = response.Units.Single(u => u.Outcome.Key == "M:S.Slow");
        Assert.Equal(OutcomeKind.Undecided, slow.Outcome.Kind);
        Assert.StartsWith("the time limit of 2 s was reached", slow.Outcome.Message, StringComparison.Ordinal);
        var fast = response.Units.Where(u => u.Outcome.Key.StartsWith("M:S.Fast", StringComparison.Ordinal)).ToList();
        Assert.Equal(6, fast.Count);
        Assert.All(fast, u => Assert.Equal(OutcomeKind.Proved, u.Outcome.Kind));
        Assert.All(fast, u => Assert.True(u.Elapsed < TimeSpan.FromSeconds(1), $"{u.Outcome.Key} took {u.Elapsed}"));
        Assert.True(response.Elapsed < TimeSpan.FromSeconds(5), $"the request took {response.Elapsed}");
    }

    [Fact]
    public void TheSimpSetsAreBuiltOnceOverTheBundleAndSharedByEveryFork()
    {
        // A sidecar of its own, so this service's sets are not ones another test built.
        var sidecar = Sidecar.Load(TestData.Path(AttributeSidecarFixture.FileName), AttributeSidecarFixture.BundleSha256);
        using var service = new VerificationService(engine.Bundle, sidecar, workers: 2);
        var simp = service.SimpSet;
        var omega = service.OmegaPrep;

        var inputs = EngineCorpus.Inputs(EngineCorpus.Inline(Lemmas));
        var response = service.Verify(Request(inputs, engine.Options));
        Assert.All(response.Units, u => Assert.Contains(u.Outcome.Kind, new[] { OutcomeKind.Translated, OutcomeKind.Proved }));

        // A theorem's MetaM runs over a fork of a level's fork and a fork of the run's sidecar fork: it gets the same sets.
        var theoremEnv = engine.Bundle.Env.Fork();
        theoremEnv.Freeze();
        var runSidecar = sidecar.Fork();
        runSidecar.Freeze();
        var meta = new MetaM(theoremEnv.Fork(), new MetaLimits(1000)) { Attributes = runSidecar.Fork() };
        Assert.Same(simp, DefaultSimpSet.Theorems(meta));
        Assert.Same(omega, OmegaPrepSet.Theorems(meta));
        Assert.Same(simp, service.SimpSet);

        // Built from the bundle alone: every constant they are made from is the bundle's, none a run's.
        Assert.All(DefaultSimpSet.LemmaNames(sidecar).Concat(OmegaPrepSet.Names), n => Assert.NotNull(engine.Bundle.Env.Find(n)));
        // And per base sidecar, not once per process.
        using var other = new VerificationService(
            engine.Bundle, Sidecar.Load(TestData.Path(AttributeSidecarFixture.FileName), AttributeSidecarFixture.BundleSha256), workers: 1);
        Assert.NotSame(simp, other.SimpSet);
    }

    [Fact]
    public void AUnitWhoseVirCannotBeReadIsAnInternalErrorForThatUnitOnly()
    {
        var inputs = EngineCorpus.Inputs(EngineCorpus.Inline("""
            public static class S
            {
                [Verified] public static int Inc(int x) => x + 1;
                [Theorem] static Proof One() => Prove.That(Inc(0) == 1);
                [Theorem] static Proof Two() => Prove.That(Inc(1) == 2);
            }
            """));
        var request = Request(inputs, engine.Options);
        var broken = request.Units.Single(u => u.Key == "M:S.One");
        request = request with { Units = request.Units.Replace(broken, broken with { Vir = Encoding.UTF8.GetBytes("{\"vir\": 2, \"key\": ") }) };

        var response = Service.Verify(request);

        Assert.Equal(new[] { "M:S.Inc(System.Int32)", "M:S.One", "M:S.Two" }, response.Units.Select(u => u.Outcome.Key));
        var one = response.Units[1].Outcome;
        Assert.Equal(OutcomeKind.Failed, one.Kind);
        Assert.Null(one.Code); // WRT0010
        Assert.Equal(VirUnitKind.Theorem, one.UnitKind);
        Assert.Equal("S.One()", one.DisplayName);
        Assert.StartsWith("the unit's VIR could not be read: Not a VIR unit: ", one.Message, StringComparison.Ordinal);
        Assert.Equal(OutcomeKind.Translated, response.Units[0].Outcome.Kind);
        Assert.Equal(OutcomeKind.Proved, response.Units[2].Outcome.Kind);
    }

    [Fact]
    public void ALemmaNamedWithNameofRunsFirstAndItsFailureSkipsItsUser()
    {
        var proved = Verify(Lemmas);
        Assert.Equal(OutcomeKind.Proved, proved["M:S.Lemma"].Kind);
        Assert.Equal(OutcomeKind.Proved, proved["M:S.User(System.Int32)"].Kind);

        var failed = Verify(Lemmas.Replace("Twice(x) == unchecked(x + x)", "Twice(x) == unchecked(x + x) + 1", StringComparison.Ordinal)
            .Replace("Tactic.Exact(Lean.Const(\"rfl\"))", "Tactic.Omega()", StringComparison.Ordinal));
        Assert.Equal(OutcomeKind.NotProved, failed["M:S.Lemma"].Kind);
        var user = failed["M:S.User(System.Int32)"];
        Assert.Equal(OutcomeKind.Skipped, user.Kind);
        Assert.Equal("M:S.Lemma", user.Dependency);
        Assert.Equal("it depends on S.Lemma(), which was not admitted.", user.Message);
    }

    [Fact]
    public void AChainOfThreeTheoremsRunsInThreeLevelsWithTheSequentialOutcomes()
    {
        const string source = """
            public static class S
            {
                [Verified] public static int Twice(int x) => x + x;

                [Theorem]
                static Proof First() => Prove.That(Spec.ForAll<int>(x => Twice(x) == unchecked(x + x))).By(Tactic.Intro("x"), Tactic.Exact(Lean.Const("rfl")));

                [Theorem] static Proof Second() => Prove.That(Spec.ForAll<int>(x => Twice(x) == unchecked(x + x))).By(Tactic.Exact(nameof(First)));

                [Theorem] static Proof Third() => Prove.That(Spec.ForAll<int>(x => Twice(x) == unchecked(x + x))).By(Tactic.Exact(nameof(Second)));
            }
            """;
        // Requested last first: each theorem still runs after the one it names.
        var inputs = EngineCorpus.Inputs(EngineCorpus.Inline(source)).Reverse().ToList();
        var run = Service.Run(Request(inputs, engine.Options));

        Assert.All(run.Response.Units, u => Assert.Contains(u.Outcome.Kind, new[] { OutcomeKind.Translated, OutcomeKind.Proved }));
        Assert.Equal(Texts(Pipeline.Run(inputs, engine.Bundle, engine.Options).Units), Texts(run.Response));
        // Each level's proof names the theorem of the level before, which only that level's fork held.
        var third = Assert.IsType<ProvedOutcome>(run.Result.Find("M:S.Third"));
        Assert.Contains("Cs.S.Second", third.Certificate.Value.Proof.ToString(), StringComparison.Ordinal);
        Assert.Equal(new[] { "Cs.S.«Twice(System.Int32)»", "Cs.S.First", "Cs.S.Second", "Cs.S.Third" }, run.Result.Admitted.OfType<Kernel.DefinitionDecl>()
            .Select(d => d.Value.Name.ToString())
            .Concat(run.Result.Admitted.OfType<Kernel.TheoremDecl>().Select(t => t.Value.Name.ToString())));
    }

    [Fact]
    public void AlwaysLargersCounterexampleIsTheSameOnEveryRunWithEveryWorkerBusy()
    {
        var source = new StringBuilder(Chain(24));
        for (int i = 0; i < 4; i++)
        {
            source.Append(CultureInfo.InvariantCulture, $"    [Theorem(TimeoutSeconds = 1)] static Proof Busy{i}() => Prove.That(A24({i}) > 0);\n");
        }
        source.Append("""
                [Verified] public static int Increment(int x) => x + 1;
                [Theorem] static Proof AlwaysLarger(int x) => Prove.That(Increment(x) > x).By(Tactic.Unfold(nameof(Increment)), Tactic.Omega());
            }
            """);
        var inputs = EngineCorpus.Inputs(EngineCorpus.Inline(source.ToString()));
        var request = Request(inputs, engine.Options with { Kernel = engine.Options.Kernel with { Fuel = long.MaxValue } });
        for (int run = 0; run < 10; run++)
        {
            var outcome = Service.Verify(request).Units.Single(u => u.Outcome.Key == "M:S.AlwaysLarger(System.Int32)").Outcome;
            Assert.Equal(OutcomeKind.NotProved, outcome.Kind);
            Assert.Equal("x = 2147483647", string.Join(", ", outcome.Counterexample.Select(v => $"{v.Parameter} = {v.Value}")));
        }
    }

    [Fact]
    public void ALeanConstNamingAnotherUnitsEquationLemmaWithoutNameofIsWrt0004()
    {
        var outcomes = Verify("""
            public static class S
            {
                [Verified]
                public static int Sum(int n)
                {
                    Spec.Decreases(n);
                    if (n <= 0) return 0;
                    return n + Sum(n - 1);
                }

                [Theorem] static Proof Outside(int a) => Prove.That(a == a).By(Tactic.Exact(Lean.Const("Cs.S.«Sum(System.Int32)».$eq_def")));

                [Theorem] static Proof Library(int a) => Prove.That(a == a).By(Tactic.Exact(Lean.Const("rfl")));

                [Theorem] static Proof Inside(int n) => Prove.That(Sum(n) == Sum(n)).By(Tactic.Simp(Lean.Const("Cs.S.«Sum(System.Int32)».$eq_def")));
            }
            """);
        var outside = outcomes["M:S.Outside(System.Int32)"];
        Assert.Equal(OutcomeKind.Failed, outside.Kind);
        Assert.Equal("WRT0004", outside.Code);
        Assert.Equal(
            "Malformed proof script: Lean.Const(\"Cs.S.«Sum(System.Int32)».$eq_def\") names a constant of 'Sum', which this theorem does not "
            + "depend on; name it with nameof(Sum) instead.",
            outside.Message);
        Assert.NotNull(outside.Node);
        // A Lean library constant is not another unit's, and a dependency's constant may be named.
        Assert.Equal(OutcomeKind.Proved, outcomes["M:S.Library(System.Int32)"].Kind);
        Assert.Null(outcomes["M:S.Inside(System.Int32)"].Code);
        Assert.NotEqual(OutcomeKind.Failed, outcomes["M:S.Inside(System.Int32)"].Kind);
    }

    [Fact]
    public void ALeanConstNamingAnotherTheoremIsWrt0004()
    {
        var outcomes = Verify("""
            public static class S
            {
                [Verified] public static int Twice(int x) => x + x;

                [Theorem]
                static Proof ViaConst() => Prove.That(Spec.ForAll<int>(x => Twice(x) == unchecked(x + x))).By(Tactic.Intro("x"), Tactic.Exact(Lean.Const("rfl")));

                [Theorem] static Proof User() => Prove.That(Spec.ForAll<int>(x => Twice(x) == unchecked(x + x))).By(Tactic.Exact(Lean.Const("Cs.S.ViaConst")));
            }
            """);
        Assert.Equal(OutcomeKind.Proved, outcomes["M:S.ViaConst"].Kind);
        // User names ViaConst only through Lean.Const, so it does not depend on it: WRT0004, whatever order they run in.
        Assert.Equal("WRT0004", outcomes["M:S.User"].Code);
    }

    [Fact]
    public void ALeanConstNamingATypeAdmittedBeforeItsUnitRanOutIsWrt0004()
    {
        // With 40 steps of kernel fuel Light's inductive type is admitted and its casesOn is not: the unit is undecided,
        // but Cs.Light is in the run's environment, and Light owns it.
        var inputs = EngineCorpus.Inputs(EngineCorpus.Inline("""
            [Closed]
            public enum Light { Red, Amber, Green }

            public static class S
            {
                [Verified] public static Light Next(Light l) => l switch { Light.Red => Light.Amber, Light.Amber => Light.Green, _ => Light.Red };

                [Theorem] static Proof Outside(int a) => Prove.That(a == a).By(Tactic.Exact(Lean.Const("Cs.Light")));
            }
            """));
        var run = Service.Run(Request(inputs, engine.Options with { Kernel = engine.Options.Kernel with { Fuel = 40 } }));

        Assert.IsType<UndecidedOutcome>(run.Result.Find("T:Light"));
        Assert.Contains(run.Result.Admitted, d => d is Kernel.InductiveDecl i && i.Types.Any(t => t.Name.ToString() == "Cs.Light"));
        var outside = run.Response.Units.Single(u => u.Outcome.Key == "M:S.Outside(System.Int32)").Outcome;
        Assert.Equal("WRT0004", outside.Code);
        Assert.Equal(
            "Malformed proof script: Lean.Const(\"Cs.Light\") names a constant of 'Light', which this theorem does not depend on; "
            + "name it with nameof(Light) instead.",
            outside.Message);
    }

    [Fact]
    public void AMalformedLeanConstNameIsAnInternalErrorForThatTheoremOnly()
    {
        var outcomes = Verify("""
            public static class S
            {
                [Verified] public static int Twice(int x) => x + x;

                [Theorem] static Proof Malformed(int a) => Prove.That(a == a).By(Tactic.Exact(Lean.Const("a..b")));

                [Theorem] static Proof Valid(int a) => Prove.That(a == a).By(Tactic.Exact(Lean.Const("rfl")));
            }
            """);
        // The run's KTD33 check skips a name that does not parse; the tactic that reads it fails this theorem alone.
        Assert.Equal(OutcomeKind.InternalError, outcomes["M:S.Malformed(System.Int32)"].Kind);
        Assert.StartsWith("Meta failed unexpectedly: FormatException: ", outcomes["M:S.Malformed(System.Int32)"].Message, StringComparison.Ordinal);
        Assert.Equal(OutcomeKind.Proved, outcomes["M:S.Valid(System.Int32)"].Kind);
        Assert.Equal(OutcomeKind.Translated, outcomes["M:S.Twice(System.Int32)"].Kind);
    }

    [Fact]
    public void CancellingDuringTheCounterexampleSearchStopsItWithinOneSecond()
    {
        // The script fails at once (no hypothesis h); then each of the 343 combinations runs A20 in the kernel until its
        // million steps run out, far longer than the two seconds before the cancel.
        var source = Chain(20) + """
                [Theorem] static Proof Search(int a, int b, int c) => Prove.That(unchecked(A20(a) + b + c) > a).By(Tactic.Exact("h"));
            }
            """;
        var inputs = EngineCorpus.Inputs(EngineCorpus.Inline(source));
        var request = Request(inputs, engine.Options with { Timeout = TimeSpan.FromHours(1) });

        using var cts = new CancellationTokenSource();
        var stopwatch = Stopwatch.StartNew();
        TimeSpan? cancelledAt = null;
        using var registration = cts.Token.Register(() => cancelledAt = stopwatch.Elapsed);
        cts.CancelAfter(TimeSpan.FromSeconds(2));
        var response = Service.Verify(request, cts.Token);
        var stoppedAt = stopwatch.Elapsed;

        Assert.NotNull(cancelledAt);
        Assert.True(stoppedAt - cancelledAt < TimeSpan.FromSeconds(1), $"the request stopped {stoppedAt - cancelledAt} after the cancel");
        Assert.Equal(OutcomeKind.Cancelled, response.Units.Single(u => u.Outcome.Key.StartsWith("M:S.Search", StringComparison.Ordinal)).Outcome.Kind);
        Assert.Equal(OutcomeKind.Translated, response.Units.Single(u => u.Outcome.Key == "M:S.A20(System.Int32)").Outcome.Kind);
    }

    [Fact]
    public void TheResponseRoundTripsThroughItsJsonContract()
    {
        var inputs = engine.Inputs("m5a/refuted");
        var request = Request(inputs, engine.Options);
        var response = Service.Verify(request);

        var requestJson = JsonSerializer.Serialize(request, ServiceJsonContext.Default.VerifyRequest);
        var readRequest = JsonSerializer.Deserialize(requestJson, ServiceJsonContext.Default.VerifyRequest)!;
        Assert.Equal(request.Units.Select(u => u.Vir.ToArray()), readRequest.Units.Select(u => u.Vir.ToArray()));
        Assert.Equal(requestJson, JsonSerializer.Serialize(readRequest, ServiceJsonContext.Default.VerifyRequest));

        var json = JsonSerializer.Serialize(response, ServiceJsonContext.Default.VerifyResponse);
        Assert.Contains("\"kind\":\"NotProved\"", json, StringComparison.Ordinal);
        var read = JsonSerializer.Deserialize(json, ServiceJsonContext.Default.VerifyResponse)!;
        Assert.Equal(json, JsonSerializer.Serialize(read, ServiceJsonContext.Default.VerifyResponse));
        Assert.Equal(Texts(response), Texts(read));
    }

    /// <summary><c>A0(x) = x + 1</c> and <c>A{k}(x) = A{k-1}(A{k-1}(x))</c>, which adds 2^k, in an open class <c>S</c>.</summary>
    private static string Chain(int depth)
    {
        var source = new StringBuilder("public static class S\n{\n    [Verified] public static int A0(int x) => x + 1;\n");
        for (int k = 1; k <= depth; k++)
        {
            source.Append(CultureInfo.InvariantCulture, $"    [Verified] public static int A{k}(int x) => A{k - 1}(A{k - 1}(x));\n");
        }
        return source.ToString();
    }

    private Dictionary<string, OutcomeDto> Verify(string source) =>
        Service.Verify(Request(EngineCorpus.Inputs(EngineCorpus.Inline(source)), engine.Options)).Units.ToDictionary(u => u.Outcome.Key, u => u.Outcome);

    internal static VerifyRequest Request(IEnumerable<EngineUnit> units, EngineOptions options) => new(
        VerificationService.ProtocolVersion,
        "test",
        "project",
        CacheDirectory: null,
        VerifyBudgets.From(options),
        Recheck: false,
        Priority: 0,
        [.. units.Select(u => new RequestUnit(u.Unit.Key, u.Unit.Kind, u.DisplayName, VirWriter.Write(u.Unit)))]);

    /// <summary>The outcomes as their wire form's JSON, which every field of an outcome but its declarations reaches.</summary>
    private static List<string> Texts(IEnumerable<UnitOutcome> outcomes) =>
        [.. outcomes.Select(o => JsonSerializer.Serialize(OutcomeDto.From(o), ServiceJsonContext.Default.OutcomeDto))];

    private static List<string> Texts(VerifyResponse response) =>
        [.. response.Units.Select(u => JsonSerializer.Serialize(u.Outcome, ServiceJsonContext.Default.OutcomeDto))];
}
