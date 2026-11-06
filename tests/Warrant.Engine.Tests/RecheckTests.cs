using System.Text.Json;
using System.Text.Json.Nodes;
using Warrant.Engine.Reports;
using Warrant.Engine.Service;
using Warrant.Engine.Service.Cache;
using Warrant.Kernel;
using Warrant.Vir;

namespace Warrant.Engine.Tests;

/// <summary>
/// Cache hits, closure admission and recheck (M5b plan U7, KTD15, KTD16; R8, R11): a hit runs nothing, a miss admits the
/// cached units it depends on with their cached proofs, each checked by the kernel, and recheck checks every cached proof
/// with the kernel against the theorem translated from the current code, running no tactic.
/// </summary>
public sealed class RecheckTests(EngineFixture engine) : IClassFixture<EngineFixture>, IDisposable
{
    private const string Source = """
        public static class S
        {
            [Verified] public static int Inc(int x) => x + 1;

            [Verified] public static int Twice(int x) => x + x;

            [Verified]
            public static int Sum(int n)
            {
                Spec.Decreases(n);
                if (n <= 0) return 0;
                return n + Sum(n - 1);
            }

            [Theorem] static Proof IncAddsOne(int x) => Prove.That(Inc(x) == x + 1).By(Tactic.Unfold(nameof(Inc)), Tactic.Omega());

            [Theorem] static Proof SumOfZero() => Prove.That(Sum(0) == 0).By(Tactic.Unfold(nameof(Sum)), Tactic.Simp());

            [Theorem]
            static Proof Lemma() => Prove.That(Spec.ForAll<int>(x => Twice(x) == x + x)).By(Tactic.Intro("x"), Tactic.Exact(Lean.Const("rfl")));

            [Theorem] static Proof User(int a) => Prove.That(Twice(a) == a + a).By(Tactic.Apply(nameof(Lemma)));

            [Theorem] static Proof Wrong() => Prove.That(Inc(1) == 3);
        }
        """;

    private const string IncAddsOne = "M:S.IncAddsOne(System.Int32)";
    private const string SumOfZero = "M:S.SumOfZero";
    private const string Lemma = "M:S.Lemma";
    private const string User = "M:S.User(System.Int32)";
    private const string Wrong = "M:S.Wrong";
    private const string Sum = "M:S.Sum(System.Int32)";

    private static readonly BundleHashes Hashes =
        new(AttributeSidecarFixture.BundleSha256, OutcomeText.FileSha256(TestData.Path(AttributeSidecarFixture.FileName)));

    private readonly string _root = Path.Combine(Path.GetTempPath(), "warrant-recheck-tests-" + Guid.NewGuid().ToString("N"));
    private readonly List<VerificationService> _services = [];

    private string Dir => Path.Combine(_root, "obj", "warrant", "cache");

    public void Dispose()
    {
        foreach (var service in _services)
        {
            service.Dispose();
        }
        if (Directory.Exists(_root))
        {
            Directory.Delete(_root, recursive: true);
        }
    }

    [Fact]
    public void ASecondRunOfTheM5aExitCorpusReportsEveryTheoremFromTheCacheWithNoTacticRuns()
    {
        var service = NewService();
        int theorems = 0;
        foreach (var compilation in CorpusSet.M5a.Names.Select(n => $"m5a/{n}"))
        {
            var inputs = engine.Inputs(compilation);
            var cold = service.Verify(Request(inputs));
            var warm = service.Verify(Request(inputs));

            Assert.Equal(Texts(cold), Texts(warm));
            Assert.Equal(0, warm.Counters.TacticRuns);
            var warmTheorems = warm.Units.Where(u => u.Outcome.UnitKind == VirUnitKind.Theorem).ToList();
            Assert.All(warmTheorems, u => Assert.True(u.FromCache, $"{compilation}: {u.Outcome.Key}"));
            theorems += warmTheorems.Count;
        }
        Assert.True(theorems >= 8, $"{theorems} theorems");
    }

    [Fact]
    public void EditingOneTheoremsScriptReprovesOnlyThatTheoremAndAdmitsItsCalleesWithoutTactics()
    {
        var service = NewService();
        service.Verify(Request(Units(Source)));
        var edited = Units(Source.Replace(
            "Inc(x) == x + 1).By(Tactic.Unfold(nameof(Inc)), Tactic.Omega())",
            "Inc(x) == x + 1).By(Tactic.Unfold(nameof(Inc)), Tactic.Simp())",
            StringComparison.Ordinal));

        var warm = service.Run(Request(edited));

        Assert.Equal(1, warm.Response.Counters.TacticRuns);
        Assert.Equal(
            [IncAddsOne],
            warm.Response.Units.Where(u => u.Outcome.UnitKind == VirUnitKind.Theorem && !u.FromCache).Select(u => u.Outcome.Key));
        Assert.Equal(OutcomeKind.Proved, Result(warm.Response, IncAddsOne).Outcome.Kind);
        Assert.Contains(warm.Result.Admitted, d => d is DefinitionDecl { Value.Name: var n } && n.ToString() == "Cs.S.«Inc(System.Int32)»");
        Assert.Equal(Texts(Pipeline.Run(edited, engine.Bundle, engine.Options).Units.Select(OutcomeDto.From)), Texts(warm.Response));
    }

    [Fact]
    public void ARecursiveCalleesCachedDecreaseProofIsReusedWhenACallerTheoremMisses()
    {
        var service = NewService();
        service.Verify(Request(Units(Source)));
        var edited = Units(EditSumOfZero(Source));

        var warm = service.Run(Request(edited));

        // Only SumOfZero's script ran: Sum's decrease theorem came from its certificate, and the kernel admitted it.
        Assert.Equal(1, warm.Response.Counters.TacticRuns);
        Assert.True(Result(warm.Response, Sum).FromCache);
        Assert.False(Result(warm.Response, SumOfZero).FromCache);
        Assert.Equal(OutcomeKind.Proved, Result(warm.Response, SumOfZero).Outcome.Kind);
        Assert.Contains(warm.Result.Admitted, d => d is TheoremDecl { Value.Name: var n } && n.ToString() == "Cs.S.«Sum(System.Int32)».$dec_1");
    }

    [Fact]
    public void ACachedDecreaseProofTheKernelRejectsMakesItsDefinitionAMiss()
    {
        var units = Units(Source);
        var service = NewService();
        service.Verify(Request(units));
        var original = new FileResultCache().Read(Dir, KeyOf(units, Sum))!.Entry;
        // The decrease theorem's proof replaced by its own statement, which proves nothing.
        Tamper(units, Sum, ProofReplacedByStatement(original.Certificate, "$dec_1"));

        var warm = NewService().Verify(Request(Units(EditSumOfZero(Source))));

        Assert.False(Result(warm, Sum).FromCache);
        Assert.Equal(OutcomeKind.Translated, Result(warm, Sum).Outcome.Kind);
        Assert.Equal(2, warm.Counters.TacticRuns);
        Assert.Equal(OutcomeKind.Proved, Result(warm, SumOfZero).Outcome.Kind);
        // The entry Sum ran again for replaces the bad one.
        Assert.Equal(original.Certificate, new FileResultCache().Read(Dir, KeyOf(units, Sum))!.Entry.Certificate);
    }

    [Fact]
    public void RecheckOfADefinitionWhoseDecreaseProofWasReplacedReportsWrt0010AndSkipsItsUsers()
    {
        var units = Units(Source);
        NewService().Verify(Request(units));
        Tamper(units, Sum, ProofReplacedByStatement(new FileResultCache().Read(Dir, KeyOf(units, Sum))!.Entry.Certificate, "$dec_1"));

        var recheck = NewService().Verify(Request(units) with { Recheck = true });

        var sum = Result(recheck, Sum);
        Assert.Equal(OutcomeKind.Failed, sum.Outcome.Kind);
        Assert.Equal(InternalErrorOutcome.Code, sum.Outcome.Code);
        Assert.StartsWith("cached certificate for 'S.Sum(int)' was rejected by the kernel: ", sum.Outcome.Message, StringComparison.Ordinal);
        Assert.Equal(OutcomeKind.Skipped, Result(recheck, SumOfZero).Outcome.Kind);
        Assert.Equal(0, recheck.Counters.TacticRuns);
        Assert.False(File.Exists(FileResultCache.PathOf(Dir, KeyOf(units, Sum))));
    }

    [Fact]
    public void ATheoremThatNamesALemmaMissesWhileTheLemmaHitsAndTheLemmasProofIsCheckedByTheKernel()
    {
        var service = NewService();
        var units = Units(Source);
        service.Verify(Request(units));
        var edited = Units(EditUser(Source, "b"));

        var warm = service.Verify(Request(edited));

        Assert.True(Result(warm, Lemma).FromCache);
        Assert.False(Result(warm, User).FromCache);
        Assert.Equal(OutcomeKind.Proved, Result(warm, User).Outcome.Kind);
        Assert.Equal(1, warm.Counters.TacticRuns);
        Assert.Equal(Texts(Pipeline.Run(edited, engine.Bundle, engine.Options).Units.Select(OutcomeDto.From)), Texts(warm));

        // The lemma's cached proof replaced by another theorem's: the kernel rejects it, so the lemma runs again.
        Tamper(units, Lemma, Certificate(units, IncAddsOne));
        var again = NewService().Verify(Request(Units(EditUser(Source, "c"))));
        Assert.False(Result(again, Lemma).FromCache);
        Assert.Equal(OutcomeKind.Proved, Result(again, Lemma).Outcome.Kind);
        Assert.Equal(OutcomeKind.Proved, Result(again, User).Outcome.Kind);
        Assert.Equal(2, again.Counters.TacticRuns);
    }

    [Fact]
    public void ALemmaCachedAsNotProvedSkipsItsUserWithoutRunningTheUsersScript()
    {
        const string source = """
            public static class S
            {
                [Verified] public static int Twice(int x) => x + x;

                [Theorem] static Proof Lemma() => Prove.That(Spec.ForAll<int>(x => Twice(x) == x + x)).By(Tactic.Exact("h"));

                [Theorem] static Proof User(int a) => Prove.That(Twice(a) == a + a).By(Tactic.Apply(nameof(Lemma)));
            }
            """;
        var units = Units(source);
        var service = NewService();
        var cold = service.Verify(Request(units));
        Assert.Equal(OutcomeKind.NotProved, Result(cold, Lemma).Outcome.Kind);
        Assert.Equal(OutcomeKind.Skipped, Result(cold, User).Outcome.Kind);

        var warm = service.Verify(Request(units));

        Assert.True(Result(warm, Lemma).FromCache);
        Assert.Equal(OutcomeKind.Skipped, Result(warm, User).Outcome.Kind);
        Assert.Equal(0, warm.Counters.TacticRuns);
        Assert.Equal(Texts(cold), Texts(warm));
    }

    [Fact]
    public void AUnitWhoseNameCollidesWithACachedUnitsIsReportedAlthoughEveryOtherUnitHits()
    {
        var units = Units(Source);
        var service = NewService();
        service.Verify(Request(units));
        // A key with another kind letter names the same Lean constant as the cached IncAddsOne.
        var twin = units.Single(u => u.Unit.Key == IncAddsOne);
        var colliding = units.Append(twin with { Unit = twin.Unit with { Key = "P:S.IncAddsOne(System.Int32)" } }).ToList();

        var response = service.Verify(Request(colliding));

        var failed = Assert.Single(response.Units, u => u.Outcome.Kind == OutcomeKind.Failed);
        Assert.Contains("collides with another declaration", failed.Outcome.Message, StringComparison.Ordinal);
        Assert.All(
            response.Units.Where(u => u != failed && (u.Outcome.UnitKind == VirUnitKind.Theorem || u.Outcome.Key == Sum)),
            u => Assert.True(u.FromCache, u.Outcome.Key));
    }

    [Fact]
    public void RecheckOfTheWarmM5aCorpusReportsEveryProvedTheoremRecheckedWithNoTacticRuns()
    {
        var service = NewService();
        int rechecked = 0;
        foreach (var compilation in CorpusSet.M5a.Names.Select(n => $"m5a/{n}"))
        {
            var inputs = engine.Inputs(compilation);
            var cold = service.Verify(Request(inputs));

            var recheck = service.Verify(Request(inputs) with { Recheck = true });

            Assert.Equal(Texts(cold), Texts(recheck));
            Assert.Equal(0, recheck.Counters.TacticRuns);
            foreach (var unit in recheck.Units.Where(u => u.Outcome.UnitKind == VirUnitKind.Theorem))
            {
                Assert.True(unit.FromCache, unit.Outcome.Key);
                Assert.Equal(unit.Outcome.Kind == OutcomeKind.Proved, unit.Rechecked);
            }
            Assert.Equal(recheck.Units.Count(u => u.Rechecked), recheck.Counters.Rechecked);
            rechecked += recheck.Counters.Rechecked;
        }
        Assert.True(rechecked >= 5, $"{rechecked} rechecked");
    }

    [Fact]
    public void AWarmRecheckOfATheoremThatNamesALemmaReportsBothRechecked()
    {
        var units = Units(Source);
        NewService().Verify(Request(units));

        var recheck = NewService().Verify(Request(units) with { Recheck = true });

        Assert.True(Result(recheck, Lemma).Rechecked);
        Assert.True(Result(recheck, User).Rechecked);
        Assert.Equal(OutcomeKind.Proved, Result(recheck, User).Outcome.Kind);
        // Sum's decrease proof and equation lemma come from its certificate, checked by the kernel.
        Assert.True(Result(recheck, Sum).Rechecked);
        Assert.Equal(0, recheck.Counters.TacticRuns);
    }

    [Fact]
    public void RecheckOfAnEntryWhoseProofWasReplacedByAnotherTheoremsReportsWrt0010AndDeletesTheEntry()
    {
        var units = Units(Source);
        var service = NewService();
        var cold = service.Verify(Request(units));
        Tamper(units, IncAddsOne, Certificate(units, SumOfZero));
        // A hit is trusted: without recheck the tampered entry is reported as it is.
        Assert.True(Result(NewService().Verify(Request(units)), IncAddsOne).FromCache);

        var recheck = service.Verify(Request(units) with { Recheck = true });

        var rejected = Result(recheck, IncAddsOne);
        Assert.Equal(OutcomeKind.Failed, rejected.Outcome.Kind);
        Assert.Equal(InternalErrorOutcome.Code, rejected.Outcome.Code);
        Assert.StartsWith("cached certificate for 'S.IncAddsOne(int)' was rejected by the kernel: ", rejected.Outcome.Message, StringComparison.Ordinal);
        Assert.False(rejected.FromCache);
        Assert.False(rejected.Rechecked);
        Assert.False(File.Exists(FileResultCache.PathOf(Dir, KeyOf(units, IncAddsOne))));
        // Not re-proved in that run; every other unit is reported as before.
        Assert.Equal(0, recheck.Counters.TacticRuns);
        Assert.True(Result(recheck, SumOfZero).Rechecked);
        Assert.Equal(
            Texts(cold).Where(t => !t.Contains(IncAddsOne, StringComparison.Ordinal)),
            Texts(recheck).Where(t => !t.Contains(IncAddsOne, StringComparison.Ordinal)));

        // The next build proves it again.
        var next = service.Verify(Request(units));
        Assert.Equal(OutcomeKind.Proved, Result(next, IncAddsOne).Outcome.Kind);
        Assert.False(Result(next, IncAddsOne).FromCache);
    }

    [Fact]
    public void ALemmaWhoseRecheckFailsSkipsItsUser()
    {
        var units = Units(Source);
        NewService().Verify(Request(units));
        Tamper(units, Lemma, Certificate(units, IncAddsOne));

        var recheck = NewService().Verify(Request(units) with { Recheck = true });

        Assert.Equal(OutcomeKind.Failed, Result(recheck, Lemma).Outcome.Kind);
        Assert.Equal(OutcomeKind.Skipped, Result(recheck, User).Outcome.Kind);
        Assert.Equal(0, recheck.Counters.TacticRuns);
    }

    [Fact]
    public void RecheckAfterChangingACalleesBodyMissesTheTheorem()
    {
        var service = NewService();
        service.Verify(Request(Units(Source)));
        var edited = Units(Source.Replace("Inc(int x) => x + 1;", "Inc(int x) => 1 + x;", StringComparison.Ordinal));

        var recheck = service.Verify(Request(edited) with { Recheck = true });

        var theorem = Result(recheck, IncAddsOne);
        Assert.False(theorem.FromCache);
        Assert.False(theorem.Rechecked);
        Assert.Equal(OutcomeKind.Proved, theorem.Outcome.Kind);
        Assert.False(Result(recheck, Wrong).FromCache);
        Assert.True(Result(recheck, SumOfZero).Rechecked);
    }

    [Fact]
    public void ACachedFalseOutcomeUnderRecheckIsReportedAsFalse()
    {
        var units = Units(Source);
        var cold = NewService().Verify(Request(units));

        var recheck = NewService().Verify(Request(units) with { Recheck = true });

        var wrong = Result(recheck, Wrong);
        Assert.Equal(OutcomeKind.False, wrong.Outcome.Kind);
        Assert.True(wrong.FromCache);
        Assert.False(wrong.Rechecked);
        Assert.Equal(Text(Result(cold, Wrong).Outcome), Text(wrong.Outcome));
    }

    /// <summary>Units that admit nothing a tiny kernel fuel cannot, but their own proofs: no non-recursive definition.</summary>
    private const string Standalone = """
        public static class S
        {
            [Verified]
            public static int Sum(int n)
            {
                Spec.Decreases(n);
                if (n <= 0) return 0;
                return n + Sum(n - 1);
            }

            [Theorem] static Proof Lemma() => Prove.That(Spec.ForAll<int>(x => x == x)).By(Tactic.Intro("x"), Tactic.Exact(Lean.Const("rfl")));

            [Theorem] static Proof User(int a) => Prove.That(a == a).By(Tactic.Apply(nameof(Lemma)));
        }
        """;

    [Fact]
    public void RecheckThatRunsOutOfKernelFuelIsUndecidedAndKeepsTheEntries()
    {
        var units = Units(Standalone);
        NewService().Verify(Request(units));
        // The entries say their proofs needed one step of kernel fuel, so they apply to a run with that much.
        WithKernelFuel(units, Sum, 1);
        WithKernelFuel(units, Lemma, 1);
        var tiny = engine.Options with { Kernel = engine.Options.Kernel with { Fuel = 1 } };

        var recheck = NewService().Run(Request(units, tiny) with { Recheck = true });

        foreach (var (key, activity) in new[] { (Sum, "the kernel checked the cached proof of Cs.S.«Sum(System.Int32)».$dec_1"), (Lemma, "the kernel checked the cached proof") })
        {
            var undecided = Assert.IsType<UndecidedOutcome>(recheck.Result.Find(key)); // WRT0006, not WRT0010
            Assert.Equal(ExhaustedBudget.KernelFuel, undecided.Exhausted);
            Assert.Equal($"kernel fuel ran out (1 steps) while {activity}.", undecided.Reason);
            Assert.False(Result(recheck.Response, key).Rechecked);
            Assert.True(File.Exists(FileResultCache.PathOf(Dir, KeyOf(units, key))), key);
        }
        Assert.Equal(OutcomeKind.Skipped, Result(recheck.Response, User).Outcome.Kind);
        Assert.Equal(0, recheck.Response.Counters.TacticRuns);
    }

    [Fact]
    public void AMissWhoseCachedLemmaRunsOutOfKernelFuelGivesTheColdOutcome()
    {
        var units = Units(Standalone);
        NewService().Verify(Request(units));
        WithKernelFuel(units, Lemma, 1);
        var tiny = engine.Options with { Kernel = engine.Options.Kernel with { Fuel = 1 } };
        var edited = Units(Standalone.Replace("User(int a) => Prove.That(a == a)", "User(int b) => Prove.That(b == b)", StringComparison.Ordinal));

        var warm = NewService().Verify(Request(edited, tiny));

        Assert.False(Result(warm, User).FromCache);
        Assert.False(Result(warm, Lemma).FromCache);
        Assert.Equal(Texts(Pipeline.Run(edited, engine.Bundle, tiny).Units.Select(OutcomeDto.From)), Texts(warm));
    }

    /// <summary>Rewrites a unit's entry to say its proof needed the given kernel fuel, with a hash of its new body.</summary>
    private void WithKernelFuel(IReadOnlyList<EngineUnit> units, string unitKey, long fuel)
    {
        var cache = new FileResultCache();
        var entry = cache.Read(Dir, KeyOf(units, unitKey), fromDisk: true)!.Entry;
        Assert.Equal(BudgetMatch.AtLeast, entry.Match);
        Assert.True(cache.Write(Dir, entry with { Budgets = entry.Budgets with { KernelFuel = fuel } }));
    }

    private static string EditSumOfZero(string source) => source.Replace(
        "SumOfZero() => Prove.That(Sum(0) == 0)", "SumOfZero() => Prove.That(0 == Sum(0))", StringComparison.Ordinal);

    private static string EditUser(string source, string parameter) => source.Replace(
        "User(int a) => Prove.That(Twice(a) == a + a)", $"User(int {parameter}) => Prove.That(Twice({parameter}) == {parameter} + {parameter})", StringComparison.Ordinal);

    /// <summary>
    /// A certificate whose theorem with the given last name component has, as its proof, the expression of its own type:
    /// still well-formed NDJSON, but a term the kernel rejects at once.
    /// </summary>
    private static string ProofReplacedByStatement(string certificate, string component)
    {
        var lines = certificate.Split('\n');
        var names = new Dictionary<long, string>();
        for (int i = 0; i < lines.Length; i++)
        {
            if (lines[i].Length == 0 || JsonNode.Parse(lines[i]) is not JsonObject line)
            {
                continue;
            }
            if (line["str"] is JsonObject str && line["in"] is JsonValue id)
            {
                names[id.GetValue<long>()] = str["str"]!.GetValue<string>();
            }
            if (line["thm"] is JsonObject theorem && names.GetValueOrDefault(theorem["name"]!.GetValue<long>()) == component)
            {
                theorem["value"] = theorem["type"]!.GetValue<long>();
                lines[i] = line.ToJsonString();
                return string.Join('\n', lines);
            }
        }
        throw new InvalidOperationException($"The certificate has no theorem named ...{component}.");
    }

    /// <summary>A unit's cached certificate.</summary>
    private string Certificate(IReadOnlyList<EngineUnit> units, string unitKey) =>
        new FileResultCache().Read(Dir, KeyOf(units, unitKey), fromDisk: true)!.Entry.Certificate;

    /// <summary>Replaces a unit's cached certificate and writes the entry with a hash of its new body, as a deliberate edit would.</summary>
    private void Tamper(IReadOnlyList<EngineUnit> units, string unitKey, string certificate)
    {
        var cache = new FileResultCache();
        var entry = cache.Read(Dir, KeyOf(units, unitKey), fromDisk: true)!.Entry;
        Assert.NotEqual(entry.Certificate, certificate);
        Assert.True(cache.Write(Dir, entry with { Certificate = certificate }));
        Assert.NotNull(cache.Read(Dir, entry.Key, fromDisk: true));
    }

    private VerificationService NewService()
    {
        var service = new VerificationService(engine.Bundle, EngineFixture.SharedSidecar.Value, workers: 2, Hashes);
        _services.Add(service);
        return service;
    }

    private VerifyRequest Request(IEnumerable<EngineUnit> units, EngineOptions? options = null) =>
        ServiceTests.Request(units, options ?? engine.Options) with { CacheDirectory = Dir };

    private static IReadOnlyList<EngineUnit> Units(string source) => EngineCorpus.Inputs(EngineCorpus.Inline(source));

    private static string KeyOf(IReadOnlyList<EngineUnit> units, string unitKey) =>
        CacheKeyInputs.ForUnits(units, Hashes.Bundle, Hashes.Sidecar)[unitKey].Key(Toolchain.Identity);

    private static UnitResult Result(VerifyResponse response, string key) => response.Units.Single(u => u.Outcome.Key == key);

    private static string Text(OutcomeDto outcome) => JsonSerializer.Serialize(outcome, ServiceJsonContext.Default.OutcomeDto);

    private static List<string> Texts(VerifyResponse response) => Texts(response.Units.Select(u => u.Outcome));

    private static List<string> Texts(IEnumerable<OutcomeDto> outcomes) => [.. outcomes.Select(Text)];
}
