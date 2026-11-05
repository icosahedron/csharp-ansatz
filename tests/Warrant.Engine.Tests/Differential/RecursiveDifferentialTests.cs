using System.Diagnostics;
using System.Globalization;
using System.Text;
using FsCheck;
using FsCheck.Fluent;
using Microsoft.CodeAnalysis.CSharp;
using Warrant.Extraction;
using Warrant.Kernel;
using Warrant.Semantics;
using Warrant.Vir;
using Xunit.Abstractions;
using Xunit.Sdk;

namespace Warrant.Engine.Tests.Differential;

/// <summary>
/// The M5a accepted corpus on both sides, for its recursive units (docs/m5a/08, "Recursive methods"): the compilation
/// extraction read, emitted and loaded; and the engine's run over its units, with the sidecar, frozen.
/// </summary>
public sealed class RecursionFixture : IDisposable
{
    public RecursionFixture()
    {
        Compilation = CorpusSet.M5a.Compile("accepted");
        Extraction = EngineCorpus.Extract(Compilation);
        var options = EngineOptions.Default with { Kernel = KernelLimits.Corpus, Attributes = EngineFixture.SharedSidecar.Value };
        Run = Pipeline.Run(EngineCorpus.Inputs(Extraction), EngineFixture.SharedBundle.Value, options);
        Run.Environment.Freeze();
        Assembly = CorpusAssembly.Load(Compilation);
        var definitions = Extraction.Units.Where(u => u.Unit.Definition is not null).ToDictionary(u => u.Key, u => u.Unit.Definition!, StringComparer.Ordinal);
        Model = new ModelCheck(Run.Environment, new Values(Assembly, definitions), KernelLimits.Corpus);
        Equations = new EquationEvaluator(Run.Environment, KernelLimits.Corpus);
    }

    internal CSharpCompilation Compilation { get; }

    internal ExtractionResult Extraction { get; }

    public EngineResult Run { get; }

    internal CorpusAssembly Assembly { get; }

    internal ModelCheck Model { get; }

    internal EquationEvaluator Equations { get; }

    /// <summary>The recursive units, in extraction order.</summary>
    internal IEnumerable<ExtractedUnit> Recursive => Extraction.Units.Where(u => Translator.IsRecursive(u.Unit));

    internal ExtractedUnit Unit(string key) => Extraction.Find(key) ?? throw new InvalidOperationException($"{key} was not extracted");

    public void Dispose() => Assembly.Dispose();
}

/// <summary>
/// Every recursive corpus function agrees with its compiled .NET method (plan M5a U15, R15, Key Decisions; docs/m5a/08):
/// on bounded random inputs by kernel <c>Eq.refl</c> over <c>Nat.fix</c>, and on five inputs each by rewriting with its
/// equation lemma.
/// </summary>
public sealed class RecursiveDifferentialTests(RecursionFixture corpus, ITestOutputHelper output) : IClassFixture<RecursionFixture>
{
    /// <summary>
    /// The largest measure an input is drawn with. M5a KTD26 starts at 1,000. The fuel measurement in README.md
    /// ("Recursive units") gives about 540 kernel fuel per level of recursion, linear in the depth, so 1,000 levels use
    /// about 0.5% of <see cref="KernelLimits.Corpus"/>: the fuel does not lower the bound. It stays at 1,000 for time
    /// (about 0.6 s per check at full depth in a Debug build) and for the CLR's stack.
    /// </summary>
    internal const int MeasureBound = 1000;

    /// <summary>
    /// Random inputs per recursive function: fewer than M4's 1,000, because one input costs up to 1,000 levels of
    /// recursion (README.md). <see cref="Pbt"/> raises it from the environment.
    /// </summary>
    internal const int RandomInputsPerFunction = 100;

    /// <summary>How many inputs per recursive unit are also evaluated by rewriting with the equation lemma.</summary>
    internal const int RewritingInputs = 5;

    public static TheoryData<string> Functions() => new(RecursiveKeys);

    private static readonly string[] RecursiveKeys =
    [
        "M:Corpus.Recursion.Sum(System.Int32)",
        "M:Corpus.Recursion.Add(System.Int32,System.Int32)",
        "M:Corpus.Recursion.SumLong(System.Int64)",
    ];

    [Fact]
    public void TheFunctionsAreExactlyTheRecursiveCorpusFunctions()
    {
        var expected = CorpusSet.M5a.Expected.GetProperty("members").GetProperty("accepted").EnumerateObject()
            .Where(m => m.Value.TryGetProperty("recursive", out var r) && r.GetBoolean())
            .Select(m => m.Name);
        Assert.Equal(expected.Order(StringComparer.Ordinal), corpus.Recursive.Select(u => u.Key).Order(StringComparer.Ordinal));
        Assert.Equal(RecursiveKeys.Order(StringComparer.Ordinal), expected.Order(StringComparer.Ordinal));
    }

    /// <summary>
    /// The property that the model agrees with the CLR on bounded inputs, by kernel <c>Eq.refl</c>. An input whose check
    /// runs out of kernel fuel is skipped, and the test fails if every input was skipped.
    /// </summary>
    [Theory]
    [MemberData(nameof(Functions))]
    public void AgreesOnBoundedRandomInputs(string key)
    {
        var unit = corpus.Unit(key);
        var check = Checker(unit, KernelLimits.Corpus);
        var config = Pbt.Config(RandomInputsPerFunction);
        var run = new BoundedRun();
        var watch = Stopwatch.StartNew();
        KernelThread.Run(() => Pbt.Check(
            Prop.ForAll(Arbitrary(unit.Unit), args =>
            {
                if (run.Record(check(args)) is { } disagreement)
                {
                    throw new XunitException(disagreement);
                }
            }),
            config));
        output.WriteLine($"{key}: {run.Checked} random inputs ({run.Skipped} skipped) in {watch.Elapsed.TotalSeconds:F2} s");
        Assert.Equal(config.MaxTest, run.Checked);
        run.AssertNotAllSkipped(key);
    }

    /// <summary>
    /// Five inputs per recursive unit evaluated a second way, by rewriting with <c>f.$eq_def</c> (plan Key Decisions):
    /// the kernel checks the <c>Eq.trans</c> chain as a proof of <c>f a = r</c>, with <c>r</c> the CLR's result.
    /// </summary>
    [Theory]
    [MemberData(nameof(Functions))]
    public void AgreesByRewritingWithTheEquationLemma(string key)
    {
        var unit = corpus.Unit(key);
        var method = corpus.Assembly.MethodOf(unit.Unit);
        var types = ModelCheck.ParameterTypes(unit.Unit);
        var inputs = RewritingInputsOf(unit.Unit);
        Assert.Equal(RewritingInputs, inputs.Count);
        var name = LeanNames.ForKey(key);
        var rewrites = KernelThread.Run(() => inputs.Select(args =>
        {
            var result = CorpusAssembly.Invoke(method, args);
            var (proof, count) = corpus.Equations.Prove(
                name, Values.CicType(unit.Unit.Returns!), [.. types.Select((t, i) => corpus.Model.Values.Term(t, args[i]))], corpus.Model.Values.Term(unit.Unit.Returns!, result));
            Assert.Contains($"{name}.$eq_def", proof.ToString(), StringComparison.Ordinal);
            // The same input, by kernel evaluation, agrees too.
            Assert.Null(corpus.Model.Disagreement(key, unit.Unit.Returns!, corpus.Model.Application(unit.Unit, args), result));
            return count;
        }).ToList());
        output.WriteLine($"{key}: rewrote with the equation lemma {string.Join(", ", rewrites)} times");
        // Each input unfolds once per level of recursion, and once more where the guard stops it.
        Assert.Equal(inputs.Select(i => Levels(unit.Unit, i) + 1), rewrites);
    }

    [Fact]
    public void RewritingCatchesAWrongResult()
    {
        // Sum(5) is 15; the chain for Sum 5 = 16 is built the same way, and the kernel rejects it at the last step.
        var name = LeanNames.ForKey("M:Corpus.Recursion.Sum(System.Int32)");
        var ex = Assert.Throws<KernelException>(() => KernelThread.Run(() =>
            corpus.Equations.Prove(name, Values.CicType(VirType.Int32), [Literals.Int32(5)], Literals.Int32(16))));
        Assert.Contains("type mismatch", ex.Message, StringComparison.OrdinalIgnoreCase);
        KernelThread.Run(() => corpus.Equations.Prove(name, Values.CicType(VirType.Int32), [Literals.Int32(5)], Literals.Int32(15)));
    }

    [Fact]
    public void AnInputOverTheFuelBudgetIsSkipped()
    {
        var unit = corpus.Unit("M:Corpus.Recursion.Sum(System.Int32)");
        var scarce = KernelLimits.Corpus with { Fuel = 50_000 };
        var check = Checker(unit, scarce);
        var run = new BoundedRun();
        KernelThread.Run(() =>
        {
            Assert.Null(run.Record(check([0])));
            Assert.Null(run.Record(check([MeasureBound])));
        });
        Assert.Equal(2, run.Checked);
        Assert.Equal(1, run.Skipped);
        run.AssertNotAllSkipped("Sum");
    }

    [Fact]
    public void ATestWhoseInputsAreAllSkippedFails()
    {
        var unit = corpus.Unit("M:Corpus.Recursion.Sum(System.Int32)");
        var check = Checker(unit, KernelLimits.Corpus with { Fuel = 50_000 });
        var run = new BoundedRun();
        KernelThread.Run(() => Assert.Null(run.Record(check([MeasureBound]))));
        var failure = Assert.Throws<XunitException>(() => run.AssertNotAllSkipped("Sum"));
        Assert.Contains("every one of its 1 inputs was skipped", failure.Message, StringComparison.Ordinal);
    }

    /// <summary>
    /// The fuel measurement behind <see cref="MeasureBound"/> (README.md, "Recursive units"): the fuel of the
    /// <c>Eq.refl</c> check at several depths, per level of recursion. Opt-in, like the M4 cost measurement.
    /// </summary>
    [FactRequiringEnv("WARRANT_DIFFERENTIAL_COST")]
    public void MeasureTheFuelPerLevelOfRecursion()
    {
        var table = new StringBuilder("| Function | Levels | Fuel | Fuel per level | ms |\n|---|---|---|---|---|\n");
        foreach (var unit in corpus.Recursive)
        {
            var method = corpus.Assembly.MethodOf(unit.Unit);
            foreach (var depth in new[] { 10, 100, 1000 })
            {
                var args = Input(unit.Unit, depth, 1);
                var result = CorpusAssembly.Invoke(method, args);
                var (fuel, elapsed) = KernelThread.Run(() => corpus.Model.Measure(unit.Unit.Returns!, corpus.Model.Application(unit.Unit, args), result));
                table.Append(CultureInfo.InvariantCulture, $"| `{unit.DisplayName}` | {depth} | {fuel} | {fuel / depth} | {elapsed.TotalMilliseconds:F0} |\n");
            }
        }
        output.WriteLine(table.ToString());
    }

    // ---- Inputs ----

    /// <summary>The index of the parameter <c>Spec.Decreases</c> names; the corpus's measures are parameters.</summary>
    private static int MeasureParameter(VirUnit unit) =>
        ((BlockStmt)unit.Body!).Stmts[0] is DecreasesStmt { Measure: ParamExpr p }
            ? p.Index
            : throw new InvalidOperationException($"{unit.Key}: the measure is not a parameter");

    /// <summary>
    /// Bounded inputs (docs/m5a/08): the measure parameter from -<see cref="MeasureBound"/> to <see cref="MeasureBound"/>
    /// (a negative measure clamps to 0 and returns at once), the others from the M4 generators.
    /// </summary>
    private static Arbitrary<object?[]> Arbitrary(VirUnit unit)
    {
        var measure = MeasureParameter(unit);
        var types = ModelCheck.ParameterTypes(unit);
        var gens = types.Select((t, i) => i == measure ? Bounded(t) : Unbounded(t)).ToList();
        var shrinkers = types.Select((t, i) => (Func<object?, IEnumerable<object?>>)(v => Shrink(t, v, i == measure))).ToList();
        var gen = gens.Aggregate(Gen.Constant(Array.Empty<object?>()), (acc, g) => acc.SelectMany(p => g.Select(v => (object?[])[.. p, v])));
        return Arb.From(gen.Resize(50), args => Generators.ShrinkFields(args, shrinkers));
    }

    private static Gen<object?> Bounded(VirType type) =>
        Gen.Choose(-MeasureBound, MeasureBound).Select(v => type is PrimitiveType { Kind: VirPrimitive.Int64 } ? (object?)(long)v : v);

    private static Gen<object?> Unbounded(VirType type) => type switch
    {
        PrimitiveType { Kind: VirPrimitive.Int32 } => Generators.Int32Values.Select(v => (object?)v),
        PrimitiveType { Kind: VirPrimitive.Int64 } => Generators.Int64Values.Select(v => (object?)v),
        _ => throw new InvalidOperationException($"no generator for {type}"),
    };

    private static IEnumerable<object?> Shrink(VirType type, object? value, bool bounded)
    {
        IEnumerable<object?> candidates = type is PrimitiveType { Kind: VirPrimitive.Int64 }
            ? Generators.ShrinkInt64((long)value!).Select(v => (object?)v)
            : Generators.ShrinkInt32((int)value!).Select(v => (object?)v);
        return bounded ? candidates.Where(v => Math.Abs(Convert.ToInt64(v, CultureInfo.InvariantCulture)) <= MeasureBound) : candidates;
    }

    /// <summary>An input with the measure parameter at <paramref name="measure"/> and the others at <paramref name="other"/>.</summary>
    private static object?[] Input(VirUnit unit, long measure, long other)
    {
        var index = MeasureParameter(unit);
        return [.. ModelCheck.ParameterTypes(unit).Select((t, i) =>
        {
            var v = i == index ? measure : other;
            return t is PrimitiveType { Kind: VirPrimitive.Int64 } ? (object?)v : (int)v;
        })];
    }

    /// <summary>The five inputs evaluated by rewriting: a negative measure, zero, and three depths, the other parameters varied.</summary>
    private static List<object?[]> RewritingInputsOf(VirUnit unit) =>
        [Input(unit, -3, 7), Input(unit, 0, -1), Input(unit, 1, 0), Input(unit, 5, int.MaxValue), Input(unit, 12, int.MinValue)];

    /// <summary>The levels of recursion an input of a corpus function takes: its measure, at least 0.</summary>
    private static int Levels(VirUnit unit, object?[] args) => (int)Math.Max(0, Convert.ToInt64(args[MeasureParameter(unit)], CultureInfo.InvariantCulture));

    // ---- Checks ----

    /// <summary>
    /// The check of one input: the agreement, or null for an input whose check ran out of <paramref name="fuel"/>
    /// (skipped). Must run on a kernel thread.
    /// </summary>
    private Func<object?[], Outcome> Checker(ExtractedUnit unit, KernelLimits fuel)
    {
        Assert.IsType<TranslatedOutcome>(corpus.Run.Find(unit.Key));
        var method = corpus.Assembly.MethodOf(unit.Unit);
        var types = ModelCheck.ParameterTypes(unit.Unit);
        return args =>
        {
            var description = $"{unit.DisplayName}({string.Join(", ", args.Select((a, i) => corpus.Model.Values.Display(types[i], a)))})";
            var result = CorpusAssembly.Invoke(method, args);
            try
            {
                return new Outcome(corpus.Model.DisagreementWithin(description, unit.Unit.Returns!, corpus.Model.Application(unit.Unit, args), result, fuel), false);
            }
            catch (KernelResourceException)
            {
                return new Outcome(null, true);
            }
        };
    }

    private sealed record Outcome(string? Disagreement, bool Skipped);

    /// <summary>Counts a property's inputs and the skipped ones.</summary>
    private sealed class BoundedRun
    {
        public int Checked { get; private set; }

        public int Skipped { get; private set; }

        public string? Record(Outcome outcome)
        {
            Checked++;
            if (outcome.Skipped)
            {
                Skipped++;
            }
            return outcome.Disagreement;
        }

        /// <summary>A test cannot pass by testing nothing (docs/m5a/08).</summary>
        public void AssertNotAllSkipped(string function)
        {
            if (Checked > 0 && Skipped == Checked)
            {
                throw new XunitException($"{function}: every one of its {Checked} inputs was skipped for running out of kernel fuel.");
            }
        }
    }
}
