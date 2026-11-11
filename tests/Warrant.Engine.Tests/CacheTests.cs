using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;
using Warrant.Engine.Reports;
using Warrant.Engine.Service;
using Warrant.Engine.Service.Cache;
using Warrant.Kernel;
using Warrant.Vir;

namespace Warrant.Engine.Tests;

/// <summary>
/// The result cache (M5b plan U6, KTD13, KTD14; R8, R9, R10, R12): a finished unit's outcome is stored under a key that
/// changes exactly when the outcome could, read back on the next request instead of running, and never trusted when it
/// is damaged, from another toolchain, or computed under budgets it does not hold under.
/// </summary>
public sealed class CacheTests(EngineFixture engine) : IClassFixture<EngineFixture>, IDisposable
{
    private const string Increments = """
        public static class S
        {
            [Verified] public static int Inc(int x) => x + 1;

            [Verified] public static int Dec(int x) => x - 1;

            [Verified]
            public static int Sum(int n)
            {
                Spec.Decreases(n);
                if (n <= 0) return 0;
                return n + Sum(n - 1);
            }

            [Theorem] static Proof IncAddsOne(int x) => Prove.That(Inc(x) == x + 1).By(Tactic.Unfold(nameof(Inc)), Tactic.Omega());

            [Theorem] static Proof DecSubtractsOne(int x) => Prove.That(Dec(x) == x - 1).By(Tactic.Unfold(nameof(Dec)), Tactic.Omega());

            [Theorem] static Proof SumOfZero() => Prove.That(Sum(0) == 0).By(Tactic.Unfold(nameof(Sum)), Tactic.Simp());

            [Theorem] static Proof AlwaysLarger(int x) => Prove.That(Inc(x) > x).By(Tactic.Unfold(nameof(Inc)), Tactic.Omega());

            [Theorem] static Proof Wrong() => Prove.That(Inc(1) == 3);
        }
        """;

    private const string IncAddsOne = "M:S.IncAddsOne(System.Int32)";
    private const string DecSubtractsOne = "M:S.DecSubtractsOne(System.Int32)";
    private const string SumOfZero = "M:S.SumOfZero";
    private const string AlwaysLarger = "M:S.AlwaysLarger(System.Int32)";
    private const string Wrong = "M:S.Wrong";
    private const string Sum = "M:S.Sum(System.Int32)";

    private static readonly BundleHashes Hashes =
        new(AttributeSidecarFixture.BundleSha256, OutcomeText.FileSha256(TestData.Path(AttributeSidecarFixture.FileName)));

    private readonly string _root = Path.Combine(Path.GetTempPath(), "warrant-cache-tests-" + Guid.NewGuid().ToString("N"));
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
    public void AUnitVerifiedTwiceHitsTheSecondTimeAndNoTacticRuns()
    {
        var service = NewService();
        var units = Units(Increments);

        var cold = service.Verify(Request(units));
        Assert.Equal(0, cold.Counters.Hits);
        Assert.True(cold.Counters.TacticRuns >= 6, $"{cold.Counters.TacticRuns} tactic runs");
        var tacticRuns = service.Totals.TacticRuns;

        var warm = service.Verify(Request(units));

        Assert.Equal(Texts(cold), Texts(warm));
        Assert.Equal(0, warm.Counters.TacticRuns);
        Assert.Equal(tacticRuns, service.Totals.TacticRuns);
        // Every theorem and the recursive Sum come from the cache; Inc and Dec are admitted again, which runs nothing.
        Assert.Equal(
            new[] { Sum, IncAddsOne, DecSubtractsOne, SumOfZero, AlwaysLarger, Wrong }.Order(StringComparer.Ordinal),
            warm.Units.Where(u => u.FromCache).Select(u => u.Outcome.Key).Order(StringComparer.Ordinal));
        Assert.Equal(6, warm.Counters.Hits);
        Assert.Equal(2, warm.Counters.Misses);

        // A new service, with nothing in memory, reads the same entries from disk.
        var fresh = NewService().Verify(Request(units));
        Assert.Equal(Texts(cold), Texts(fresh));
        Assert.Equal(6, fresh.Counters.Hits);
        Assert.Equal(0, fresh.Counters.TacticRuns);
    }

    [Fact]
    public void TheCacheMarksItsDirectoryAndHoldsOnlyKeyNamedEntriesBesideTheMarker()
    {
        // WarrantClean deletes only a directory with the marker, and only these files (Warrant.Build.targets).
        NewService().Verify(Request(Units(Increments)));

        Assert.True(File.Exists(Path.Combine(Dir, FileResultCache.MarkerFileName)));
        Assert.All(
            Directory.GetFiles(Dir).Select(Path.GetFileName).Where(f => f != FileResultCache.MarkerFileName),
            f => Assert.Matches("^[0-9a-f]{64}\\.json$", f!));
    }

    [Fact]
    public void EditingACalleesBodyChangesItsCallersKeyAndNoOtherUnits()
    {
        var units = Units(Increments);
        var edited = Units(Increments.Replace("Inc(int x) => x + 1;", "Inc(int x) => 1 + x;", StringComparison.Ordinal));
        var before = CacheKeyInputs.ForUnits(units, Hashes.Bundle, Hashes.Sidecar);
        var after = CacheKeyInputs.ForUnits(edited, Hashes.Bundle, Hashes.Sidecar);
        string Key(Dictionary<string, CacheKeyInputs> keys, string unit) => keys[unit].Key(Toolchain.Identity);

        Assert.NotEqual(Key(before, IncAddsOne), Key(after, IncAddsOne));
        Assert.NotEqual(Key(before, AlwaysLarger), Key(after, AlwaysLarger));
        Assert.NotEqual(Key(before, Wrong), Key(after, Wrong));
        Assert.Equal(Key(before, DecSubtractsOne), Key(after, DecSubtractsOne));
        Assert.Equal(Key(before, SumOfZero), Key(after, SumOfZero));

        var service = NewService();
        service.Verify(Request(units));
        var response = service.Verify(Request(edited));
        Assert.False(Result(response, IncAddsOne).FromCache);
        Assert.False(Result(response, AlwaysLarger).FromCache);
        Assert.True(Result(response, DecSubtractsOne).FromCache);
        Assert.True(Result(response, SumOfZero).FromCache);
        Assert.Equal(OutcomeKind.Proved, Result(response, IncAddsOne).Outcome.Kind);
    }

    [Fact]
    public void ChangingTheSidecarFilesBytesMissesEveryUnit()
    {
        var units = Units(Increments);
        NewService().Verify(Request(units));
        var copy = Path.Combine(_root, "sidecar-copy.ndjson.gz");
        Directory.CreateDirectory(_root);
        File.WriteAllBytes(copy, [.. File.ReadAllBytes(TestData.Path(AttributeSidecarFixture.FileName)), 0]);

        var response = NewService(Hashes with { Sidecar = OutcomeText.FileSha256(copy) }).Verify(Request(units));

        Assert.All(response.Units, u => Assert.False(u.FromCache, u.Outcome.Key));
        Assert.Equal(0, response.Counters.Hits);
        // The same sidecar bytes hit again.
        Assert.Equal(6, NewService().Verify(Request(units)).Counters.Hits);
    }

    [Theory]
    [InlineData("truncated")]
    [InlineData("flipped")]
    public void ADamagedEntryIsAMissAndIsDeleted(string damage)
    {
        var units = Units(Increments);
        NewService().Verify(Request(units));
        var key = KeyOf(units, IncAddsOne);
        var path = FileResultCache.PathOf(Dir, key);
        var bytes = File.ReadAllBytes(path);
        Assert.NotNull(new FileResultCache().Read(Dir, key));
        if (damage == "truncated")
        {
            bytes = bytes[..(bytes.Length / 2)];
        }
        else
        {
            // A letter of the outcome's display name, inside the hashed body: still JSON, no longer the hashed text.
            var at = Encoding.UTF8.GetString(bytes).IndexOf("\"displayName\":\"S.IncAddsOne(int)\"", StringComparison.Ordinal);
            Assert.True(at > 0);
            bytes[at + "\"displayName\":\"S.".Length] ^= 0x01;
        }
        File.WriteAllBytes(path, bytes);

        Assert.Null(new FileResultCache().Read(Dir, key));
        Assert.False(File.Exists(path));

        var response = NewService().Verify(Request(units));
        Assert.False(Result(response, IncAddsOne).FromCache);
        Assert.True(Result(response, DecSubtractsOne).FromCache);
        Assert.NotNull(new FileResultCache().Read(Dir, key));
    }

    [Theory]
    [InlineData("null assumptions")]
    [InlineData("null assumption")]
    [InlineData("null sides")]
    [InlineData("null side text")]
    [InlineData("int overflow")]
    [InlineData("null display name")]
    [InlineData("null inputs dependencies")]
    public void AnEntryWithAValidHashButAMalformedBodyIsAMissAndIsDeleted(string damage)
    {
        var units = Units(Increments);
        NewService().Verify(Request(units));
        var key = KeyOf(units, Wrong);
        var path = FileResultCache.PathOf(Dir, key);
        var body = JsonNode.Parse(File.ReadAllBytes(path))!["body"]!.DeepClone();
        var outcome = body["outcome"]!;
        Assert.Equal("False", outcome["kind"]!.GetValue<string>());
        switch (damage)
        {
            case "null assumptions":
                outcome["assumptions"] = null;
                break;
            case "null assumption":
                outcome["assumptions"] = new JsonArray((JsonNode?)null);
                break;
            case "null sides":
                outcome["sides"] = null;
                break;
            case "null side text":
                outcome["sides"]![0]!["text"] = null;
                break;
            case "int overflow":
                outcome["sides"]![0]!["kind"] = "IntValue";
                outcome["sides"]![0]!["text"] = "99999999999";
                break;
            case "null display name":
                outcome["displayName"] = null;
                break;
            default:
                body["inputs"]!.AsObject().Remove(body["inputs"]!.AsObject().First(p => p.Value is JsonArray).Key);
                break;
        }
        // A deliberate edit: the hash is of the new body, so only decoding the body can tell it is malformed.
        var bytes = Encoding.UTF8.GetBytes(body.ToJsonString());
        File.WriteAllText(path, $"{{\"sha256\":\"{Convert.ToHexStringLower(SHA256.HashData(bytes))}\",\"body\":{Encoding.UTF8.GetString(bytes)}}}");

        Assert.Null(new FileResultCache().Read(Dir, key));
        Assert.False(File.Exists(path));

        var response = NewService().Verify(Request(units));
        Assert.False(Result(response, Wrong).FromCache);
        Assert.Equal(OutcomeKind.False, Result(response, Wrong).Outcome.Kind);
    }

    [Fact]
    public void AnEntryFromAnotherToolchainIsAMissAndIsDeleted()
    {
        var units = Units(Increments);
        NewService().Verify(Request(units));
        var key = KeyOf(units, IncAddsOne);

        Assert.Null(new FileResultCache(toolchain: new string('0', 64)).Read(Dir, key));
        Assert.False(File.Exists(FileResultCache.PathOf(Dir, key)));
        Assert.NotNull(new FileResultCache().Read(Dir, KeyOf(units, DecSubtractsOne)));
    }

    [Fact]
    public void ANotProvedEntryHoldsOnlyUnderTheBudgetsItRanWith()
    {
        const string source = """
            public static class S
            {
                [Theorem] static Proof NoHypothesis(int a) => Prove.That(a == a + 0).By(Tactic.Exact("h"));
            }
            """;
        const string key = "M:S.NoHypothesis(System.Int32)";
        var units = Units(source);
        var at1000 = engine.Options with { TacticFuel = 1_000 };
        var service = NewService();

        var cold = Result(service.Verify(Request(units, at1000)), key);
        Assert.Equal(OutcomeKind.NotProved, cold.Outcome.Kind);
        var entry = new FileResultCache().Read(Dir, KeyOf(units, key))!.Entry;
        Assert.Equal(BudgetMatch.Exact, entry.Match);
        Assert.Equal(1_000, entry.Budgets.TacticFuel);

        Assert.True(Result(NewService().Verify(Request(units, at1000)), key).FromCache);
        Assert.False(Result(NewService().Verify(Request(units, engine.Options with { TacticFuel = 2_000 })), key).FromCache);
    }

    [Fact]
    public void AProofHoldsUnderBudgetsAtLeastWhatItUsedAndBelowThemFailsAsAColdRunDoes()
    {
        var units = Units(Increments);
        NewService().Verify(Request(units));
        var entry = new FileResultCache().Read(Dir, KeyOf(units, IncAddsOne))!.Entry;
        Assert.Equal(BudgetMatch.AtLeast, entry.Match);
        var used = entry.Budgets.TacticFuel;
        Assert.InRange(used, 1, engine.Options.TacticFuel - 1);

        Assert.True(Result(NewService().Verify(Request(units, engine.Options with { TacticFuel = 2 * used })), IncAddsOne).FromCache);
        Assert.True(Result(NewService().Verify(Request(units, engine.Options with { TacticFuel = used })), IncAddsOne).FromCache);

        var lower = engine.Options with { TacticFuel = used - 1 };
        var below = Result(NewService().Verify(Request(units, lower)), IncAddsOne);
        Assert.False(below.FromCache);
        Assert.Equal(OutcomeKind.Undecided, below.Outcome.Kind); // WRT0006
        Assert.StartsWith("tactic fuel ran out", below.Outcome.Message, StringComparison.Ordinal);
        var coldRun = Pipeline.Run(units, engine.Bundle, lower).Find(IncAddsOne)!;
        Assert.Equal(Text(OutcomeDto.From(coldRun)), Text(below.Outcome));
    }

    [Fact]
    public void AFalseEntryHoldsOnlyUnderTheNumeralSizeLimitItRanWith()
    {
        var units = Units(Increments);
        NewService().Verify(Request(units));
        var entry = new FileResultCache().Read(Dir, KeyOf(units, Wrong))!;
        Assert.IsType<FalseOutcome>(entry.Outcome);
        Assert.Equal(BudgetMatch.Exact, entry.Entry.Match);

        var smaller = engine.Options with { Kernel = engine.Options.Kernel with { MaxNatBytes = engine.Options.Kernel.MaxNatBytes / 2 } };
        Assert.False(Result(NewService().Verify(Request(units, smaller)), Wrong).FromCache);
        Assert.True(Result(NewService().Verify(Request(units, smaller)), Wrong).FromCache);
    }

    [Fact]
    public void ATimeoutAnInternalErrorAndACancelledUnitWriteNothing()
    {
        var source = new StringBuilder(ServiceChain(24));
        source.Append("""
                [Theorem(TimeoutSeconds = 1)] static Proof Slow() => Prove.That(A24(0) > 0);

                [Theorem] static Proof Malformed(int a) => Prove.That(a == a).By(Tactic.Exact(Lean.Const("a..b")));

                [Theorem] static Proof Fine() => Prove.That(A0(0) == 1);
            }
            """);
        var units = Units(source.ToString());
        var options = engine.Options with { Kernel = engine.Options.Kernel with { Fuel = long.MaxValue } };

        var response = NewService().Verify(Request(units, options));

        Assert.Equal(OutcomeKind.Undecided, Result(response, "M:S.Slow").Outcome.Kind);
        Assert.StartsWith("the time limit of 1 s was reached", Result(response, "M:S.Slow").Outcome.Message, StringComparison.Ordinal);
        Assert.Equal(OutcomeKind.InternalError, Result(response, "M:S.Malformed(System.Int32)").Outcome.Kind);
        Assert.False(File.Exists(FileResultCache.PathOf(Dir, KeyOf(units, "M:S.Slow"))));
        Assert.False(File.Exists(FileResultCache.PathOf(Dir, KeyOf(units, "M:S.Malformed(System.Int32)"))));
        Assert.True(File.Exists(FileResultCache.PathOf(Dir, KeyOf(units, "M:S.Fine"))));

        var other = Units(Increments);
        using var cts = new CancellationTokenSource();
        cts.Cancel();
        var cancelled = NewService().Verify(Request(other), cts.Token);
        Assert.All(cancelled.Units, u => Assert.Equal(OutcomeKind.Cancelled, u.Outcome.Kind));
        Assert.All(other, u => Assert.False(File.Exists(FileResultCache.PathOf(Dir, KeyOf(other, u.Unit.Key)))));
    }

    [Fact]
    public void AUnitThatFinishesAsNotProvedAfterItsRequestWasCancelledWritesNothing()
    {
        var units = Units(Increments);
        using var cts = new CancellationTokenSource();
        var service = NewService();
        // The run is cancelled the moment AlwaysLarger has its outcome, before the service decides whether to store it.
        service.UnitFinished = o =>
        {
            if (o.Key == AlwaysLarger)
            {
                cts.Cancel();
            }
        };

        var response = service.Verify(Request(units), cts.Token);

        Assert.Equal(OutcomeKind.NotProved, Result(response, AlwaysLarger).Outcome.Kind);
        Assert.False(File.Exists(FileResultCache.PathOf(Dir, KeyOf(units, AlwaysLarger))));
        // Without the cancel, the same outcome is stored.
        NewService().Verify(Request(units));
        Assert.True(File.Exists(FileResultCache.PathOf(Dir, KeyOf(units, AlwaysLarger))));
    }

    [Fact]
    public void ARecursiveDefinitionsEntryHoldsItsDecreaseTheoremsAndEquationLemmaAndAFailedDecreaseIsCachedAsNotProved()
    {
        const string source = """
            public static class S
            {
                [Verified]
                public static int Sum(int n)
                {
                    Spec.Decreases(n);
                    if (n <= 0) return 0;
                    return n + Sum(n - 1);
                }

                [Verified]
                public static bool AllPositive(int n)
                {
                    Spec.Decreases(n);
                    return n > 0 && AllPositive(n - 1);
                }
            }
            """;
        const string allPositive = "M:S.AllPositive(System.Int32)";
        var units = Units(source);
        var cold = NewService().Verify(Request(units));

        var sum = new FileResultCache().Read(Dir, KeyOf(units, Sum))!;
        Assert.Equal(BudgetMatch.AtLeast, sum.Entry.Match);
        var declarations = Assert.IsType<TranslatedOutcome>(sum.Outcome).Declarations;
        Assert.Collection(
            declarations,
            d => Assert.Equal("Cs.S.«Sum(System.Int32)».$dec_1", Assert.IsType<TheoremDecl>(d).Value.Name.ToString()),
            d => Assert.Equal("Cs.S.«Sum(System.Int32)»", Assert.IsType<DefinitionDecl>(d).Value.Name.ToString()),
            d => Assert.Equal("Cs.S.«Sum(System.Int32)».$eq_def", Assert.IsType<TheoremDecl>(d).Value.Name.ToString()));

        var failed = new FileResultCache().Read(Dir, KeyOf(units, allPositive))!;
        Assert.Equal(BudgetMatch.Exact, failed.Entry.Match);
        var notProved = Assert.IsType<NotProvedOutcome>(failed.Outcome);
        Assert.Equal(1, notProved.Decrease!.Index);
        Assert.Equal("n : Int32\n⊢ (n - 1).toInt.toNat < n.toInt.toNat", notProved.Goals);

        var warm = NewService().Verify(Request(units));
        Assert.All(warm.Units, u => Assert.True(u.FromCache, u.Outcome.Key));
        Assert.Equal(0, warm.Counters.TacticRuns);
        Assert.Equal(Texts(cold), Texts(warm));
    }

    [Fact]
    public void AContractObligationIsCachedAsADecreaseProofIsAndAChangedEnsuresMissesIt()
    {
        // M6 U10: a method's contract obligation is admitted after its definition and cached with it, as a recursive
        // method's decrease proofs are; its Spec.Ensures is in the unit's VIR, so editing it changes the unit's key.
        const string source = """
            public static class S
            {
                [Verified]
                public static int NonNegative(int x)
                {
                    Spec.Ensures<int>(r => r >= 0);
                    return x < 0 ? 0 : x;
                }

                [ProofFor(nameof(NonNegative))]
                static Proof NonNegativeProof() =>
                    Prove.Contract().By(
                        Tactic.Apply(Lean.Const("Std.Do.Triple.pure")),
                        Tactic.Unfold(nameof(NonNegative)),
                        Tactic.Simp(Lean.Const("Std.Do.SPred.entails_1"), Lean.Const("Std.Do.SPred.apply_pure_cons"), Lean.Const("Std.Do.SPred.down_pure_nil")),
                        Tactic.Omega());

                [Theorem]
                static Proof NeverNegative(int x) =>
                    Prove.That(NonNegative(x) >= 0).By(Tactic.Apply(Lean.Const("Cs.S.«NonNegative(System.Int32)».$contract_spec")));
            }
            """;
        const string nonNegative = "M:S.NonNegative(System.Int32)";
        const string neverNegative = "M:S.NeverNegative(System.Int32)";
        var units = Units(source);
        var cold = NewService().Verify(Request(units));
        Assert.Equal(OutcomeKind.Proved, Result(cold, neverNegative).Outcome.Kind);

        var entry = new FileResultCache().Read(Dir, KeyOf(units, nonNegative))!;
        Assert.Collection(
            Assert.IsType<TranslatedOutcome>(entry.Outcome).Declarations,
            d => Assert.Equal("Cs.S.«NonNegative(System.Int32)»", Assert.IsType<DefinitionDecl>(d).Value.Name.ToString()),
            d => Assert.Equal("Cs.S.«NonNegative(System.Int32)».$contract", Assert.IsType<TheoremDecl>(d).Value.Name.ToString()),
            d => Assert.Equal("Cs.S.«NonNegative(System.Int32)».$contract_spec", Assert.IsType<TheoremDecl>(d).Value.Name.ToString()));

        // A theorem that misses next to the cached method uses its spec lemma, admitted from the method's certificate.
        const string renamed = "M:S.StillNeverNegative(System.Int32)";
        var lemma = NewService().Verify(Request(Units(source.Replace("static Proof NeverNegative(", "static Proof StillNeverNegative(", StringComparison.Ordinal))));
        Assert.True(Result(lemma, nonNegative).FromCache);
        Assert.False(Result(lemma, renamed).FromCache);
        Assert.Equal(OutcomeKind.Proved, Result(lemma, renamed).Outcome.Kind);

        var weaker = Units(source.Replace("r => r >= 0", "r => r >= -1", StringComparison.Ordinal));
        Assert.NotEqual(KeyOf(units, nonNegative), KeyOf(weaker, nonNegative));
        var changed = NewService().Verify(Request(weaker));
        Assert.False(Result(changed, nonNegative).FromCache);
        Assert.Equal(OutcomeKind.Translated, Result(changed, nonNegative).Outcome.Kind);
        Assert.Equal(Texts(cold).Count, Texts(changed).Count);
    }

    [Fact]
    public void ATheoremThatMissesNextToTheCachedLemmaItNamesIsProvedAsInAColdRun()
    {
        const string source = """
            public static class S
            {
                [Verified] public static int Twice(int x) => x + x;

                [Theorem]
                static Proof Lemma() => Prove.That(Spec.ForAll<int>(x => Twice(x) == x + x)).By(Tactic.Intro("x"), Tactic.Exact(Lean.Const("rfl")));

                [Theorem] static Proof User(int a) => Prove.That(Twice(a) == a + a).By(Tactic.Apply(nameof(Lemma)));
            }
            """;
        var service = NewService();
        service.Verify(Request(Units(source)));
        var edited = Units(source.Replace("User(int a) => Prove.That(Twice(a) == a + a)", "User(int b) => Prove.That(Twice(b) == b + b)", StringComparison.Ordinal));

        var response = service.Verify(Request(edited));

        var user = Result(response, "M:S.User(System.Int32)");
        Assert.False(user.FromCache);
        Assert.Equal(OutcomeKind.Proved, user.Outcome.Kind);
        Assert.Equal(Texts(Pipeline.Run(edited, engine.Bundle, engine.Options).Units.Select(OutcomeDto.From)), Texts(response));
    }

    [Fact]
    public void ACachedTheoremWhoseLemmaRunsOutOfFuelIsSkippedAsInAColdRunNotReportedFromTheCache()
    {
        const string source = """
            public static class S
            {
                [Verified] public static int Inc(int x) => x + 1;

                [Theorem] static Proof Lemma() => Prove.That(Spec.ForAll<int>(x => Inc(x) == x + 1)).By(Tactic.Intro("x"), Tactic.Unfold(nameof(Inc)), Tactic.Omega());

                [Theorem(TacticFuel = 100000000)] static Proof User(int a) => Prove.That(Inc(a) == a + 1).By(Tactic.Apply(nameof(Lemma)));
            }
            """;
        const string lemma = "M:S.Lemma";
        const string user = "M:S.User(System.Int32)";
        var units = Units(source);
        var warm = NewService().Verify(Request(units));
        Assert.Equal(OutcomeKind.Proved, Result(warm, lemma).Outcome.Kind);
        Assert.Equal(OutcomeKind.Proved, Result(warm, user).Outcome.Kind);
        var used = new FileResultCache().Read(Dir, KeyOf(units, lemma))!.Entry.Budgets.TacticFuel;
        Assert.True(used > 1, $"{used} tactic fuel");
        // The project's tactic fuel below what the lemma needs; the user keeps its own, which its entry holds under.
        var lower = engine.Options with { TacticFuel = used - 1 };

        var response = NewService().Verify(Request(units, lower));

        var cold = Pipeline.Run(units, engine.Bundle, lower);
        Assert.IsType<UndecidedOutcome>(cold.Find(lemma));
        Assert.IsType<SkippedOutcome>(cold.Find(user));
        Assert.Equal(Texts(cold.Units.Select(OutcomeDto.From)), Texts(response));
        Assert.False(Result(response, user).FromCache);
    }

    [Fact]
    public void ACachedTheoremWhoseLeanConstNowNamesAnotherUnitsConstantIsWrt0004AsInAColdRun()
    {
        const string before = """
            public static class S
            {
                [Theorem] static Proof Reflexive(int a) => Prove.That(a == a).By(Tactic.Try(Tactic.Exact(Lean.Const("Cs.S.«Extra(System.Int32)»"))), Tactic.Exact(Lean.Const("rfl")));
            }
            """;
        const string reflexive = "M:S.Reflexive(System.Int32)";
        var service = NewService();
        Assert.Equal(OutcomeKind.Proved, Result(service.Verify(Request(Units(before))), reflexive).Outcome.Kind);
        // A new unit owns the constant the theorem names without depending on it; the theorem's key is unchanged.
        var after = Units(before.Replace("[Theorem]", "[Verified] public static int Extra(int x) => x;\n\n    [Theorem]", StringComparison.Ordinal));
        Assert.Equal(KeyOf(Units(before), reflexive), KeyOf(after, reflexive));

        var response = service.Verify(Request(after));

        var outcome = Result(response, reflexive);
        Assert.Equal("WRT0004", outcome.Outcome.Code);
        Assert.False(outcome.FromCache);
        Assert.Equal(Texts(Pipeline.Run(after, engine.Bundle, engine.Options).Units.Select(OutcomeDto.From)), Texts(response));
    }

    [Fact]
    public void AProofFoundAfterAnotherRanOutOfKernelFuelHoldsOnlyUnderTheBudgetsItRanWith()
    {
        // rfl needs between 15,435 and 22,682 steps of kernel fuel more than decide does for this claim: at 20,000, rfl
        // runs out and decide is accepted, a proof that more fuel would have found another way.
        var source = new StringBuilder(ServiceChain(7));
        source.Append("""
                [Verified] public static int Twice(int x) => x + x;

                [Theorem] static Proof Doubled() => Prove.That(Twice(A6(0)) == A7(0));
            }
            """);
        const string doubled = "M:S.Doubled";
        var units = Units(source.ToString());
        EngineOptions WithFuel(long fuel) => engine.Options with { Kernel = engine.Options.Kernel with { Fuel = fuel } };
        var at20000 = WithFuel(20_000);

        var cold = Result(NewService().Verify(Request(units, at20000)), doubled);
        Assert.Equal(ProofKind.Decide, cold.Outcome.By);
        var entry = new FileResultCache().Read(Dir, KeyOf(units, doubled))!.Entry;
        Assert.Equal(BudgetMatch.Exact, entry.Match);
        Assert.Equal(20_000, entry.Budgets.KernelFuel);

        Assert.True(Result(NewService().Verify(Request(units, at20000)), doubled).FromCache);
        var lower = Result(NewService().Verify(Request(units, WithFuel(19_000))), doubled);
        Assert.False(lower.FromCache);
        Assert.Equal(ProofKind.Decide, lower.Outcome.By);
        var higher = Result(NewService().Verify(Request(units, WithFuel(30_000))), doubled);
        Assert.False(higher.FromCache);
        Assert.Equal(ProofKind.Rfl, higher.Outcome.By);
    }

    [Fact]
    public void RenamingACalleesDisplayNameMissesItsUsersEntries()
    {
        var units = Units(Increments);
        var service = NewService();
        service.Verify(Request(units));
        var renamed = Request(units) with
        {
            Units = [.. Request(units).Units.Select(u => u.Key == "M:S.Inc(System.Int32)" ? u with { DisplayName = "S.Increment(int)" } : u)],
        };

        var response = service.Verify(renamed);

        Assert.False(Result(response, AlwaysLarger).FromCache);
        Assert.False(Result(response, IncAddsOne).FromCache);
        Assert.True(Result(response, DecSubtractsOne).FromCache);
    }

    [Fact]
    public void TwoServicesWritingTheSameKeysAtOnceLeaveOneValidEntryEach()
    {
        var units = Units(Increments);
        var first = NewService();
        var second = NewService();

        Parallel.Invoke(() => first.Verify(Request(units)), () => second.Verify(Request(units)));

        var entries = Directory.GetFiles(Dir).Where(f => Path.GetFileName(f) != FileResultCache.MarkerFileName).ToArray();
        Assert.All(entries, f => Assert.EndsWith(".json", f, StringComparison.Ordinal));
        Assert.Equal(6, entries.Length);
        Assert.All(entries, f => Assert.NotNull(new FileResultCache().Read(Dir, Path.GetFileNameWithoutExtension(f))));

        // The same entry written by two caches at once, many times: one valid file, no temporary file left.
        var entry = new FileResultCache().Read(Dir, KeyOf(units, IncAddsOne))!.Entry;
        var caches = new[] { new FileResultCache(), new FileResultCache() };
        Parallel.For(0, 64, i => caches[i % 2].Write(Dir, entry));
        Assert.Equal(7, Directory.GetFiles(Dir).Length);
        Assert.Equal(entry.ToFile(), File.ReadAllBytes(FileResultCache.PathOf(Dir, entry.Key)));
    }

    [Fact]
    public void AMissingCacheDirectoryIsCreatedAndOneDeletedMidRunIsNotAnError()
    {
        var units = Units(Increments);
        Assert.False(Directory.Exists(Dir));
        // One worker, so no entry is being written while the directory is deleted.
        var service = NewService(workers: 1);
        int deletions = 0;
        service.UnitFinished = o =>
        {
            // Sum's entry, written before any theorem runs, created the directory.
            if (o.UnitKind == VirUnitKind.Theorem && deletions == 0)
            {
                Assert.True(Directory.Exists(Dir));
                Directory.Delete(Dir, recursive: true);
                deletions++;
            }
        };

        var response = service.Verify(Request(units));

        Assert.Equal(1, deletions);
        Assert.True(Directory.Exists(Dir));
        Assert.Equal(OutcomeKind.Proved, Result(response, IncAddsOne).Outcome.Kind);
        Assert.True(File.Exists(FileResultCache.PathOf(Dir, KeyOf(units, IncAddsOne))));
    }

    [Fact]
    public void AWarmServiceMissesOnceTheDirectoryIsDeletedAndAnotherProjectsEmptyDirectoryMisses()
    {
        var units = Units(Increments);
        var service = NewService();
        service.Verify(Request(units));
        Assert.Equal(6, service.Verify(Request(units)).Counters.Hits);

        var otherProject = Path.Combine(_root, "other", "obj", "warrant", "cache");
        Assert.Equal(0, service.Verify(Request(units, dir: otherProject)).Counters.Hits);

        Directory.Delete(Dir, recursive: true);
        var response = service.Verify(Request(units));
        Assert.Equal(0, response.Counters.Hits);
        Assert.True(response.Counters.TacticRuns >= 6);
    }

    [Fact]
    public void AnEntryEditedOnDiskWhileItsMemoryCopyIsWarmIsReadAgainFailsItsHashAndIsDeleted()
    {
        var units = Units(Increments);
        NewService().Verify(Request(units));
        var cache = new FileResultCache();
        var key = KeyOf(units, IncAddsOne);
        Assert.NotNull(cache.Read(Dir, key));
        Assert.Equal(1, cache.MemoryCount);

        var path = FileResultCache.PathOf(Dir, key);
        var written = File.GetLastWriteTimeUtc(path);
        var text = File.ReadAllText(path);
        File.WriteAllText(path, text.Replace("\"by\":\"Script\"", "\"by\":\"Decide\"", StringComparison.Ordinal));
        File.SetLastWriteTimeUtc(path, written.AddSeconds(2));

        Assert.Null(cache.Read(Dir, key));
        Assert.False(File.Exists(path));
        Assert.Equal(0, cache.MemoryCount);
    }

    [Fact]
    public void ReadingFromDiskChecksTheFileEvenWhenItsMemoryCopyLooksCurrent()
    {
        var units = Units(Increments);
        NewService().Verify(Request(units));
        var cache = new FileResultCache();
        var key = KeyOf(units, IncAddsOne);
        Assert.NotNull(cache.Read(Dir, key));

        // The same length and last-write time, different bytes: only a read of the file itself sees it.
        var path = FileResultCache.PathOf(Dir, key);
        var written = File.GetLastWriteTimeUtc(path);
        File.WriteAllText(path, File.ReadAllText(path).Replace("\"by\":\"Script\"", "\"by\":\"Decide\"", StringComparison.Ordinal));
        File.SetLastWriteTimeUtc(path, written);

        Assert.Null(cache.Read(Dir, key, fromDisk: true));
        Assert.False(File.Exists(path));
    }

    [Fact]
    public async Task ARequestWaitsForAnotherRequestComputingTheSameKeyAndReadsItsEntry()
    {
        var units = Units(Increments);
        var service = NewService();
        using var finished = new ManualResetEventSlim();
        using var secondStarted = new ManualResetEventSlim();
        service.UnitFinished = o =>
        {
            if (o.Key == IncAddsOne && !finished.IsSet)
            {
                finished.Set();
                // Hold IncAddsOne's key while the second request looks it up.
                secondStarted.Wait(TimeSpan.FromSeconds(10));
                Thread.Sleep(500);
            }
        };

        var first = Task.Run(() => service.Verify(Request(units)));
        Assert.True(finished.Wait(TimeSpan.FromSeconds(60)));
        var second = Task.Run(() =>
        {
            secondStarted.Set();
            return service.Verify(Request(units));
        });
        var responses = await Task.WhenAll(first, second);

        Assert.False(Result(responses[0], IncAddsOne).FromCache);
        Assert.True(Result(responses[1], IncAddsOne).FromCache);
    }

    [Fact]
    public void TheCorporaGiveTheSameOutcomesWithAColdCacheAndAWarmOne()
    {
        var service = NewService();
        var compilations = CorpusSet.M5a.Names.Select(n => $"m5a/{n}").Concat(CorpusSet.M4.Names).ToList();
        int hits = 0;
        foreach (var compilation in compilations)
        {
            var inputs = engine.Inputs(compilation);
            var cold = service.Verify(Request(inputs));
            var warm = service.Verify(Request(inputs));
            Assert.Equal(Texts(engine.Run(compilation).Units.Select(OutcomeDto.From)), Texts(cold));
            Assert.Equal(Texts(cold), Texts(warm));
            Assert.Equal(0, cold.Counters.Hits);
            hits += warm.Counters.Hits;
        }
        Assert.True(hits > 0);
    }

    private VerificationService NewService(BundleHashes? hashes = null, int workers = 2)
    {
        var service = new VerificationService(engine.Bundle, EngineFixture.SharedSidecar.Value, workers, hashes ?? Hashes);
        _services.Add(service);
        return service;
    }

    private VerifyRequest Request(IEnumerable<EngineUnit> units, EngineOptions? options = null, string? dir = null) =>
        ServiceTests.Request(units, options ?? engine.Options) with { CacheDirectory = dir ?? Dir };

    private static IReadOnlyList<EngineUnit> Units(string source) => EngineCorpus.Inputs(EngineCorpus.Inline(source));

    private static string KeyOf(IReadOnlyList<EngineUnit> units, string unitKey) =>
        CacheKeyInputs.ForUnits(units, Hashes.Bundle, Hashes.Sidecar)[unitKey].Key(Toolchain.Identity);

    private static UnitResult Result(VerifyResponse response, string key) => response.Units.Single(u => u.Outcome.Key == key);

    private static string Text(OutcomeDto outcome) => JsonSerializer.Serialize(outcome, ServiceJsonContext.Default.OutcomeDto);

    private static List<string> Texts(VerifyResponse response) => Texts(response.Units.Select(u => u.Outcome));

    private static List<string> Texts(IEnumerable<OutcomeDto> outcomes) => [.. outcomes.Select(Text)];

    /// <summary><c>A0(x) = x + 1</c> and <c>A{k}(x) = A{k-1}(A{k-1}(x))</c>, in an open class <c>S</c>.</summary>
    private static string ServiceChain(int depth)
    {
        var source = new StringBuilder("public static class S\n{\n    [Verified] public static int A0(int x) => x + 1;\n");
        for (int k = 1; k <= depth; k++)
        {
            source.Append(System.Globalization.CultureInfo.InvariantCulture, $"    [Verified] public static int A{k}(int x) => A{k - 1}(A{k - 1}(x));\n");
        }
        return source.ToString();
    }
}
