using System.Diagnostics;
using System.Globalization;
using System.Text;
using FsCheck;
using FsCheck.Fluent;
using Microsoft.CodeAnalysis.CSharp;
using Warrant.Extraction;
using Warrant.Kernel;
using Warrant.Vir;
using Xunit.Abstractions;
using Xunit.Sdk;

namespace Warrant.Engine.Tests.Differential;

/// <summary>
/// One compilation on both sides, for functions that can raise (plan M6 U13): the compilation extraction read, emitted and
/// loaded; and the engine's run over its units, frozen.
/// </summary>
internal sealed class EffectCorpus : IDisposable
{
    public EffectCorpus(CSharpCompilation compilation)
    {
        Extraction = EngineCorpus.Extract(compilation);
        Run = Pipeline.Run(EngineCorpus.Inputs(Extraction), EngineFixture.SharedBundle.Value, KernelLimits.Corpus);
        Run.Environment.Freeze();
        Assembly = CorpusAssembly.Load(compilation);
        var definitions = Extraction.Units.Where(u => u.Unit.Definition is not null).ToDictionary(u => u.Key, u => u.Unit.Definition!, StringComparer.Ordinal);
        var values = new Values(Assembly, definitions);
        Inputs = new Inputs(values);
        Model = new ModelCheck(Run.Environment, values, KernelLimits.Corpus);
    }

    public ExtractionResult Extraction { get; }

    public EngineResult Run { get; }

    public CorpusAssembly Assembly { get; }

    public Inputs Inputs { get; }

    public ModelCheck Model { get; }

    public ExtractedUnit Unit(string key) => Extraction.Find(key) ?? throw new InvalidOperationException($"{key} was not extracted");

    /// <summary>
    /// The check of one input of a translated function. A pure function must return what the CLR returns, and the CLR
    /// must not throw; a raising one, run from every world, must end in the CLR's result or in an error that stands for
    /// the CLR's exception (<see cref="ClrExceptions"/>). The returned function must run on a kernel thread.
    /// </summary>
    public Func<object?[], InputCheck> Checker(ExtractedUnit unit)
    {
        Assert.IsType<TranslatedOutcome>(Run.Find(unit.Key));
        var method = Assembly.MethodOf(unit.Unit);
        var types = ModelCheck.ParameterTypes(unit.Unit);
        var returns = unit.Unit.Returns!;
        var raising = Model.IsRaising(unit.Unit);
        return args =>
        {
            var description = $"{unit.DisplayName}({string.Join(", ", args.Select((a, i) => Model.Values.Display(types[i], a)))})";
            object? result = null;
            Exception? thrown = null;
            try
            {
                result = CorpusAssembly.Invoke(method, args);
            }
#pragma warning disable CA1031 // Compared with the model's error, or reported for a pure function.
            catch (Exception ex)
#pragma warning restore CA1031
            {
                thrown = ex;
            }
            if (raising)
            {
                return Model.CheckRaising(description, returns, Model.Run(unit.Unit, args), result, thrown);
            }
            return thrown is not null
                ? InputCheck.Disagrees($"{description}: the CLR threw {thrown.GetType().Name} but the model is a pure function")
                : Model.Disagreement(description, returns, Model.Application(unit.Unit, args), result) is { } message
                    ? InputCheck.Disagrees(message)
                    : InputCheck.Agrees;
        };
    }

    public void Dispose() => Assembly.Dispose();
}

/// <summary>Counts a function's inputs, the skipped ones and the disagreements.</summary>
internal sealed class EffectRun
{
    /// <summary>
    /// The smallest share of a function's inputs that must be evaluated, not skipped for a failed <c>Spec.Assert</c>
    /// (#186), so that a test cannot pass by skipping nearly everything (#144). At least one input must be evaluated.
    /// </summary>
    public const double MinimumEvaluatedShare = 0.25;

    private readonly List<string> _disagreements = [];

    public int Checked { get; private set; }

    public int Skipped { get; private set; }

    public int Evaluated => Checked - Skipped;

    public IReadOnlyList<string> Disagreements => _disagreements;

    public string? Record(InputCheck check)
    {
        Checked++;
        if (check.IsSkipped)
        {
            Skipped++;
        }
        if (check.Disagreement is { } message)
        {
            _disagreements.Add(message);
        }
        return check.Disagreement;
    }

    /// <summary>Fails unless at least <see cref="MinimumEvaluatedShare"/> of the inputs, and at least one, were evaluated.</summary>
    public void AssertEnoughEvaluated(string function)
    {
        if (Evaluated == 0 || Evaluated < Checked * MinimumEvaluatedShare)
        {
            throw new XunitException(
                $"{function}: only {Evaluated} of its {Checked} inputs were evaluated; {Skipped} were skipped because the model failed a Spec.Assert, "
                + $"and at least {MinimumEvaluatedShare:P0} must be evaluated.");
        }
    }

    public string Report() =>
        $"{_disagreements.Count} of {Checked} inputs disagree:\n{string.Join("\n", _disagreements.Take(20))}";
}

/// <summary>The M6 corpus's compilations whose functions have no dependencies, each on both sides.</summary>
public sealed class M6DifferentialFixture : IDisposable
{
    /// <summary>The compilations read: the accepted and refuted ones, and the one compiled with overflow checking.</summary>
    public static readonly string[] Compilations = ["accepted", "refuted", "checked-project"];

    private readonly Dictionary<string, EffectCorpus> _corpora;

    public M6DifferentialFixture()
    {
        _corpora = Compilations.ToDictionary(c => c, c => new EffectCorpus(CorpusSet.M6.Compile(c)), StringComparer.Ordinal);
    }

    internal EffectCorpus this[string compilation] => _corpora[compilation];

    public void Dispose()
    {
        foreach (var corpus in _corpora.Values)
        {
            corpus.Dispose();
        }
    }
}

/// <summary>
/// Every M6 corpus function without dependencies agrees with its compiled .NET method on results and exceptions (plan M6
/// U13, R1 to R5, KTD21): accepted and refuted alike, since agreement is about the model, not about whether a contract
/// holds. A raising function is run from an arbitrary world and its <c>Except</c> part compared (#110); each model error
/// must match the CLR exception's type (<see cref="ClrExceptions"/>, #78).
/// </summary>
public sealed class EffectDifferentialTests(M6DifferentialFixture corpus, ITestOutputHelper output) : IClassFixture<M6DifferentialFixture>
{
    /// <summary>Random inputs per function, as for M4 functions (README.md, "Measured cost").</summary>
    internal const int RandomInputsPerFunction = DifferentialTests.RandomInputsPerFunction;

    /// <summary>The functions compared, by compilation.</summary>
    private static readonly (string Compilation, string Key)[] Covered =
    [
        ("accepted", "M:Corpus.Rejected.Arithmetic.Halve(System.Int32)"),
        ("accepted", "M:Corpus.Rejected.Arithmetic.Remainder(System.Int32)"),
        ("accepted", "M:Corpus.Rejected.Statements.Throws(System.Int32)"),
        ("accepted", "M:Corpus.M6.Effects.Biggest(System.Int32,System.Int32)"),
        ("accepted", "M:Corpus.M6.Effects.Smallest(System.Int64,System.Int64)"),
        ("accepted", "M:Corpus.M6.Effects.Guard(System.Int32)"),
        ("accepted", "M:Corpus.Rejected.Types.NullableParameter(Corpus.Rejected.Point)"),
        ("accepted", "M:Corpus.Rejected.Types.ReturnsNull"),
        ("accepted", "M:Corpus.M6.Nullables.OrZero(System.Nullable{System.Int32})"),
        ("accepted", "M:Corpus.M6.Nullables.OrDefault(System.Nullable{System.Int64})"),
        ("accepted", "M:Corpus.M6.Nullables.Wrap(System.Int32)"),
        ("accepted", "M:Corpus.M6.Nullables.ValueWhenKnown(System.Nullable{System.Int32})"),
        ("refuted", "M:Corpus.Rejected.Arithmetic.CheckedAdd(System.Int32,System.Int32)"),
        ("refuted", "M:Corpus.Rejected.Statements.CallsUnverified(System.Int32)"),
        ("refuted", "M:Corpus.M6.Refuted.Effects.Ratio(System.Int32,System.Int32)"),
        ("refuted", "M:Corpus.M6.Refuted.Effects.Magnitude(System.Int64)"),
        ("refuted", "M:Corpus.M6.Refuted.Nullables.Read(System.Nullable{System.Int32})"),
        ("refuted", "M:Corpus.M6.Refuted.Nullables.Cast(System.Nullable{System.Int64})"),
        ("refuted", "M:Corpus.M6.Refuted.Nullables.Use(Corpus.M6.Refuted.Payment)"),
        ("refuted", "M:Corpus.M6.Refuted.Nullables.IdOf(Corpus.M6.Refuted.Payment)"),
        ("refuted", "M:Corpus.M6.Refuted.Nullables.Unchecked(Corpus.M6.Refuted.Payment)"),
        ("checked-project", "M:Corpus.Rejected.CheckedProject.Checked.Add(System.Int32,System.Int32)"),
        ("checked-project", "M:Corpus.Rejected.CheckedProject.Checked.Negate(System.Int32)"),
        ("checked-project", "M:Corpus.Rejected.CheckedProject.Checked.Narrow(System.Int64)"),
    ];

    private const string ContractsUntilU10 = "Spec.Requires or Spec.Ensures: not translated until M6 U10";

    private const string DecimalUntilU21 = "decimal: not translated until M6 U21";

    /// <summary>
    /// The functions without dependencies that are not compared yet, each because translation does not take it on this
    /// branch. <see cref="EveryM6FunctionWithoutDependenciesIsComparedOrSkippedForAReason"/> fails as soon as one translates,
    /// so it moves to <see cref="Covered"/> with the inputs it needs.
    /// </summary>
    private static readonly Dictionary<string, string> Skipped = new(StringComparer.Ordinal)
    {
        ["M:Corpus.M6.Contracts.NonNegative(System.Int32)"] = ContractsUntilU10,
        ["M:Corpus.M6.Contracts.AtMost(System.Int32,System.Int32)"] = ContractsUntilU10,
        ["M:Corpus.M6.Contracts.Capped(System.Int32)"] = ContractsUntilU10,
        ["M:Corpus.M6.Contracts.Average(System.Int32,System.Int32)"] = ContractsUntilU10,
        ["M:Corpus.M6.Contracts.Same(System.Int32)"] = ContractsUntilU10,
        ["M:Corpus.Rejected.Statements.Decimals(System.Decimal)"] = DecimalUntilU21,
        ["M:Corpus.M6.Decimals.AtLeastOne(System.Decimal)"] = DecimalUntilU21,
        ["M:Corpus.M6.Decimals.SameAmount(Corpus.M6.Payment,Corpus.M6.Payment)"] = DecimalUntilU21,
        ["M:Corpus.M6.Decimals.SamePayment(Corpus.M6.Payment,Corpus.M6.Payment)"] = DecimalUntilU21,
        ["M:Corpus.M6.Decimals.Negate(System.Decimal)"] = DecimalUntilU21,
        ["M:Corpus.M6.Decimals.Largest(System.Decimal,System.Decimal)"] = DecimalUntilU21,
        ["M:Corpus.M6.Decimals.Smallest(System.Decimal,System.Decimal)"] = DecimalUntilU21,
        ["M:Corpus.M6.Decimals.Size(System.Decimal)"] = DecimalUntilU21,
        // Corpus.M6.Payment has a decimal field.
        ["M:Corpus.M6.Nullables.IsMissing(Corpus.M6.Payment)"] = DecimalUntilU21,
        ["M:Corpus.M6.Nullables.Use(Corpus.M6.Payment)"] = DecimalUntilU21,
        ["M:Corpus.M6.Nullables.Guarded(Corpus.M6.Payment)"] = DecimalUntilU21,
        ["M:Corpus.M6.Nullables.IdOrZero(Corpus.M6.Payment)"] = DecimalUntilU21,
        ["M:Corpus.M6.Refuted.Decimals.AddFee(System.Decimal)"] = DecimalUntilU21,
        ["M:Corpus.M6.Refuted.Decimals.Difference(System.Decimal,System.Decimal)"] = DecimalUntilU21,
    };

    /// <summary>The namespaces of the functions with dependencies (and their async helpers), which plan U22 compares with mocks.</summary>
    private static readonly string[] WithDependencies = ["Corpus.M6.Payments.", "Corpus.M6.Dependencies."];

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
    /// The compared and skipped functions are exactly the M6 corpus's functions without dependencies in the three
    /// compilations; each compared one translates, and each skipped one does not, for the reason given.
    /// </summary>
    [Fact]
    public void EveryM6FunctionWithoutDependenciesIsComparedOrSkippedForAReason()
    {
        var functions = new List<(string Compilation, string Key)>();
        foreach (var compilation in M6DifferentialFixture.Compilations)
        {
            foreach (var member in CorpusSet.M6.Expected.GetProperty("members").GetProperty(compilation).EnumerateObject())
            {
                var unit = corpus[compilation].Unit(member.Name).Unit;
                if (unit.Kind != VirUnitKind.Function)
                {
                    continue;
                }
                var name = member.Name[2..];
                if (WithDependencies.Any(ns => name.StartsWith(ns, StringComparison.Ordinal)))
                {
                    continue;
                }
                Assert.Null(unit.Dependencies);
                functions.Add((compilation, member.Name));
            }
        }
        Assert.Equal(
            functions.Select(f => f.Key).Order(StringComparer.Ordinal),
            Covered.Select(c => c.Key).Concat(Skipped.Keys).Order(StringComparer.Ordinal));
        foreach (var (compilation, key) in Covered)
        {
            Assert.Contains((compilation, key), functions);
            Assert.IsType<TranslatedOutcome>(corpus[compilation].Run.Find(key));
        }
        foreach (var (key, reason) in Skipped)
        {
            var compilation = functions.Single(f => f.Key == key).Compilation;
            var outcome = corpus[compilation].Run.Find(key);
            Assert.False(outcome is TranslatedOutcome, $"{key} translates now: compare it (move it from Skipped to Covered).");
            if (outcome is FailedOutcome failed)
            {
                var unit = reason == ContractsUntilU10 ? "U10" : "U21";
                Assert.Contains($"until M6 {unit}", failed.Reason, StringComparison.Ordinal);
            }
            else
            {
                // A function whose callee or type failed to translate (Capped calls AtMost; the Payment record has a decimal).
                Assert.IsType<SkippedOutcome>(outcome);
            }
        }
        output.WriteLine($"{Covered.Length} functions compared, {Skipped.Count} skipped");
    }

    [Theory]
    [MemberData(nameof(Functions))]
    public void AgreesOnEveryBoundaryCombination(string compilation, string key)
    {
        var side = corpus[compilation];
        var unit = side.Unit(key);
        var types = ModelCheck.ParameterTypes(unit.Unit);
        Assert.InRange(types.Count, 0, 3);
        var boundaries = side.Inputs.BoundaryInputs(types);
        Assert.Equal(types.Select(t => side.Inputs.Boundaries(t).Count).Aggregate(1, (a, b) => a * b), boundaries.Count);

        var check = side.Checker(unit);
        var run = new EffectRun();
        var watch = Stopwatch.StartNew();
        KernelThread.Run(() =>
        {
            foreach (var input in boundaries)
            {
                run.Record(check(input));
            }
        });
        output.WriteLine($"{key}: {run.Evaluated} of {run.Checked} boundary inputs evaluated ({run.Skipped} skipped) in {watch.Elapsed.TotalSeconds:F2} s");
        Assert.True(run.Disagreements.Count == 0, run.Report());
        run.AssertEnoughEvaluated(key);
    }

    /// <summary>
    /// The property that the model agrees with the CLR on every input (M5a KTD26): <see cref="RandomInputsPerFunction"/>
    /// cases from the pinned seed, or what <see cref="Pbt"/> reads from the environment.
    /// </summary>
    [Theory]
    [MemberData(nameof(Functions))]
    public void AgreesOnRandomInputs(string compilation, string key)
    {
        var side = corpus[compilation];
        var unit = side.Unit(key);
        var check = side.Checker(unit);
        var arbitrary = side.Inputs.Arbitrary(ModelCheck.ParameterTypes(unit.Unit));
        var config = Pbt.Config(RandomInputsPerFunction);
        var run = new EffectRun();
        var watch = Stopwatch.StartNew();
        KernelThread.Run(() => Pbt.Check(
            Prop.ForAll(arbitrary, args =>
            {
                if (run.Record(check(args)) is { } disagreement)
                {
                    throw new XunitException(disagreement);
                }
            }),
            config));
        output.WriteLine($"{key}: {run.Evaluated} of {run.Checked} random inputs evaluated ({run.Skipped} skipped) in {watch.Elapsed.TotalSeconds:F2} s");
        Assert.Equal(config.MaxTest, run.Checked);
        run.AssertEnoughEvaluated(key);
    }

    /// <summary>
    /// <c>a / b</c> with <c>b = 0</c> is <c>divideByZero</c> in the model and <see cref="DivideByZeroException"/> on the CLR,
    /// for every boundary <c>a</c>; <c>int.MinValue / -1</c> is <c>overflow</c> and <see cref="OverflowException"/> (R5).
    /// </summary>
    [Fact]
    public void ADivisionAgreesOnDivideByZeroForAZeroDivisor()
    {
        var side = corpus["refuted"];
        var unit = side.Unit("M:Corpus.M6.Refuted.Effects.Ratio(System.Int32,System.Int32)");
        var method = side.Assembly.MethodOf(unit.Unit);
        var int32 = Values.CicType(VirType.Int32);
        KernelThread.Run(() =>
        {
            Assert.True(side.Model.IsRaising(unit.Unit));
            foreach (var a in Generators.Int32Boundaries)
            {
                Assert.Throws<DivideByZeroException>(() => CorpusAssembly.Invoke(method, [a, 0]));
                var run = side.Model.Run(unit.Unit, [a, 0]);
                Assert.True(side.Model.RunsTo(int32, run, ModelCheck.Error(int32, ClrExceptions.Constructor("divideByZero"))), $"Ratio({a}, 0)");
                Assert.False(side.Model.RunsTo(int32, run, ModelCheck.Error(int32, ClrExceptions.Constructor("overflow"))), $"Ratio({a}, 0)");
            }
            Assert.Throws<OverflowException>(() => CorpusAssembly.Invoke(method, [int.MinValue, -1]));
            Assert.True(side.Model.RunsTo(int32, side.Model.Run(unit.Unit, [int.MinValue, -1]), ModelCheck.Error(int32, ClrExceptions.Constructor("overflow"))));
        });
    }

    /// <summary>
    /// The CLR exception must be the one the model's error stands for, and the result the one it computes: a wrong
    /// exception, a wrong result and an exception where the model returns are each reported with both sides.
    /// </summary>
    [Fact]
    public void AWrongExceptionOrResultIsCaughtWithBothOutcomes()
    {
        var side = corpus["refuted"];
        var ratio = side.Unit("M:Corpus.M6.Refuted.Effects.Ratio(System.Int32,System.Int32)").Unit;
        var read = side.Unit("M:Corpus.M6.Refuted.Nullables.Read(System.Nullable{System.Int32})").Unit;
        var messages = KernelThread.Run(() => new[]
        {
            side.Model.CheckRaising("Ratio(1, 0)", VirType.Int32, side.Model.Run(ratio, [1, 0]), null, new OverflowException()),
            side.Model.CheckRaising("Ratio(1, 0)", VirType.Int32, side.Model.Run(ratio, [1, 0]), null, new InvalidOperationException()),
            side.Model.CheckRaising("Ratio(7, 2)", VirType.Int32, side.Model.Run(ratio, [7, 2]), 4, null),
            side.Model.CheckRaising("Ratio(7, 2)", VirType.Int32, side.Model.Run(ratio, [7, 2]), null, new DivideByZeroException()),
            side.Model.CheckRaising("Read(null)", VirType.Int32, side.Model.Run(read, [null]), 0, null),
        });
        Assert.All(messages, m => Assert.False(m.IsSkipped));
        Assert.All(messages, m => Assert.NotNull(m.Disagreement));
        Assert.Contains("Ratio(1, 0): the CLR threw OverflowException but the model computes error divideByZero", messages[0].Disagreement, StringComparison.Ordinal);
        Assert.Contains("the CLR returned 4 but the model computes ok 3", messages[2].Disagreement, StringComparison.Ordinal);
        Assert.Contains("the CLR threw DivideByZeroException but the model computes ok 3", messages[3].Disagreement, StringComparison.Ordinal);
        Assert.Contains("Read(null): the CLR returned 0 but the model computes error invalidOperation", messages[4].Disagreement, StringComparison.Ordinal);

        // The honest outcomes agree, the implicit and the explicit InvalidOperationException alike (#78).
        KernelThread.Run(() =>
        {
            Assert.Same(InputCheck.Agrees, side.Model.CheckRaising("Ratio(1, 0)", VirType.Int32, side.Model.Run(ratio, [1, 0]), null, new DivideByZeroException()));
            Assert.Same(InputCheck.Agrees, side.Model.CheckRaising("Read(null)", VirType.Int32, side.Model.Run(read, [null]), null, new InvalidOperationException()));
            Assert.Same(InputCheck.Agrees, side.Model.CheckRaising("Ratio(7, 2)", VirType.Int32, side.Model.Run(ratio, [7, 2]), 3, null));
        });
    }

    /// <summary>
    /// <c>thrown k</c> matches exactly the CLR type keyed <c>k</c>: <c>Throws(-1)</c> raises
    /// <see cref="ArgumentOutOfRangeException"/>, and its base type <see cref="ArgumentException"/> does not match.
    /// </summary>
    [Fact]
    public void AThrownExceptionMatchesItsExactType()
    {
        var side = corpus["accepted"];
        var throws = side.Unit("M:Corpus.Rejected.Statements.Throws(System.Int32)").Unit;
        var guard = side.Unit("M:Corpus.M6.Effects.Guard(System.Int32)").Unit;
        KernelThread.Run(() =>
        {
            var run = side.Model.Run(throws, [-1]);
            Assert.Same(InputCheck.Agrees, side.Model.CheckRaising("Throws(-1)", VirType.Int32, run, null, new ArgumentOutOfRangeException("n")));
            Assert.NotNull(side.Model.CheckRaising("Throws(-1)", VirType.Int32, run, null, new ArgumentException("n")).Disagreement);
            var guarded = side.Model.Run(guard, [-1]);
            Assert.Same(InputCheck.Agrees, side.Model.CheckRaising(
                "Guard(-1)", VirType.Int32, guarded, null, (Exception)Activator.CreateInstance(side.Assembly.TypeOf("T:Corpus.M6.RejectedPayment"), "negative")!));
        });
        Assert.Equal("T:Corpus.M6.RejectedPayment", ClrExceptions.Key(side.Assembly.TypeOf("T:Corpus.M6.RejectedPayment")));
    }

    /// <summary>
    /// Every <c>ClrExn</c> constructor is accounted for (KTD21): four map to a CLR type, <c>thrown</c> to the type it
    /// names, <c>assertFailed</c> is skipped (#186), and <c>external</c> is plan U22's sentinel.
    /// </summary>
    [Fact]
    public void EveryClrExnConstructorIsMapped()
    {
        var info = Assert.IsType<Cic.InductiveInfo>(corpus["accepted"].Run.Environment.Get(ClrExceptions.Type));
        Assert.Equal(
            ClrExceptions.Implicit.Keys.Append(ClrExceptions.Thrown).Append(ClrExceptions.AssertFailed).Append(ClrExceptions.External).Order(StringComparer.Ordinal),
            info.Constructors.Select(c => c.StringComponent).Order(StringComparer.Ordinal));
    }

    // ---- Spec.Assert (#186) ----

    private const string Assertions = """
        public static class S
        {
            [Verified]
            public static int NonZero(int x)
            {
                Spec.Assert(x != 0);
                return 100 / (x == 0 ? 1 : x);
            }

            [Verified]
            public static int OnlyZero(int x)
            {
                Spec.Assert(x == 0);
                return x;
            }
        }
        """;

    /// <summary>
    /// An input on which the model fails a <c>Spec.Assert</c> is skipped and counted: <c>Spec.Assert</c> is
    /// <c>[Conditional]</c>, so the CLR runs on (#186). The other inputs are compared as usual.
    /// </summary>
    [Fact]
    public void AnInputThatFailsASpecAssertIsSkippedAndCounted()
    {
        using var side = new EffectCorpus(Warrant.Frontend.CompilationFactory.Create(
            [new Warrant.Frontend.SourceFile("Assertions.cs", "using Warrant;\n" + Assertions)], checkOverflow: false));
        var unit = side.Unit("M:S.NonZero(System.Int32)");
        Assert.True(side.Model.IsRaising(unit.Unit));
        Assert.Equal(100, CorpusAssembly.Invoke(side.Assembly.MethodOf(unit.Unit), [0]));
        var check = side.Checker(unit);
        var run = new EffectRun();
        KernelThread.Run(() =>
        {
            foreach (var x in Generators.Int32Boundaries)
            {
                run.Record(check([x]));
            }
        });
        Assert.Empty(run.Disagreements);
        Assert.Equal((7, 1, 6), (run.Checked, run.Skipped, run.Evaluated));
        run.AssertEnoughEvaluated("NonZero");
    }

    /// <summary>A function whose inputs are nearly all skipped fails, so it cannot pass by testing almost nothing (#144).</summary>
    [Fact]
    public void AFunctionWithTooFewEvaluatedInputsFails()
    {
        using var side = new EffectCorpus(Warrant.Frontend.CompilationFactory.Create(
            [new Warrant.Frontend.SourceFile("Assertions.cs", "using Warrant;\n" + Assertions)], checkOverflow: false));
        var unit = side.Unit("M:S.OnlyZero(System.Int32)");
        var check = side.Checker(unit);
        var run = new EffectRun();
        KernelThread.Run(() =>
        {
            foreach (var x in Generators.Int32Boundaries)
            {
                run.Record(check([x]));
            }
        });
        Assert.Empty(run.Disagreements);
        Assert.Equal((7, 6), (run.Checked, run.Skipped));
        var failure = Assert.Throws<XunitException>(() => run.AssertEnoughEvaluated("OnlyZero"));
        Assert.Contains("only 1 of its 7 inputs were evaluated; 6 were skipped", failure.Message, StringComparison.Ordinal);
    }

    /// <summary>
    /// The cost measurement for the M6 functions (README.md, "Measured cost"): fuel and wall clock per check, on their
    /// boundary inputs. Opt-in, like the M4 one.
    /// </summary>
    [FactRequiringEnv("WARRANT_DIFFERENTIAL_COST")]
    public void MeasureTheCostOfAnM6Check()
    {
        var table = new StringBuilder("| Function | Raising | Boundary inputs | Fuel per check (mean / max) | ms per check (mean) |\n|---|---|---|---|---|\n");
        long totalFuel = 0;
        int totalChecks = 0;
        foreach (var (compilation, key) in Covered)
        {
            var side = corpus[compilation];
            var unit = side.Unit(key);
            var inputs = side.Inputs.BoundaryInputs(ModelCheck.ParameterTypes(unit.Unit));
            var method = side.Assembly.MethodOf(unit.Unit);
            var check = side.Checker(unit);
            var measured = KernelThread.Run(() => inputs.Select(i => Measure(side, unit.Unit, method, i)).ToList());
            var watch = Stopwatch.StartNew();
            KernelThread.Run(() =>
            {
                foreach (var input in inputs)
                {
                    check(input);
                }
            });
            totalFuel += measured.Sum();
            totalChecks += measured.Count;
            var raising = KernelThread.Run(() => side.Model.IsRaising(unit.Unit)) ? "yes" : "no";
            table.Append(CultureInfo.InvariantCulture, $"| `{unit.DisplayName}` | {raising} | {inputs.Count} | {measured.Average():F0} / {measured.Max()} | {watch.Elapsed.TotalMilliseconds / inputs.Count:F2} |\n");
        }
        table.Append(CultureInfo.InvariantCulture, $"\n{totalChecks} checks, {totalFuel / totalChecks} fuel per check on average.\n");
        output.WriteLine(table.ToString());
    }

    /// <summary>The fuel of the agreeing check of one input: the CLR's result, or the first model error its exception matches.</summary>
    private static long Measure(EffectCorpus side, VirUnit unit, System.Reflection.MethodInfo method, object?[] input)
    {
        object? result = null;
        Exception? thrown = null;
        try
        {
            result = CorpusAssembly.Invoke(method, input);
        }
#pragma warning disable CA1031 // Measured as the model error it matches.
        catch (Exception ex)
#pragma warning restore CA1031
        {
            thrown = ex;
        }
        if (!side.Model.IsRaising(unit))
        {
            return side.Model.Measure(unit.Returns!, side.Model.Application(unit, input), result).Fuel;
        }
        var r = Values.CicType(unit.Returns!);
        var run = side.Model.Run(unit, input);
        var outcome = thrown is null
            ? ModelCheck.Ok(r, side.Model.Values.Term(unit.Returns!, result))
            : ClrExceptions.ModelErrors(thrown).Select(e => ModelCheck.Error(r, e)).First(o => side.Model.RunsTo(r, run, o));
        return side.Model.Measure(ModelCheck.RunTheorem(r, run, outcome)).Fuel;
    }
}
