using System.Diagnostics;
using System.Globalization;
using System.Text;
using FsCheck;
using FsCheck.Fluent;
using Microsoft.CodeAnalysis.CSharp;
using Warrant.Extraction;
using Warrant.Cic;
using Warrant.Kernel;
using Warrant.Semantics;
using Warrant.Vir;
using Xunit.Abstractions;
using Xunit.Sdk;

namespace Warrant.Engine.Tests.Differential;

/// <summary>
/// One compilation on both sides, for functions that can raise (plan M6 U13): the compilation extraction read, emitted and
/// loaded; and the engine's run over its units, as the build runs it (the default procedure with the attribute sidecar),
/// frozen. The model is a function's kernel-admitted definition, whether or
/// not its contract obligation (M6 U10) is proved: the engine admits the definition before the obligation and keeps it
/// when the obligation is not proved (<see cref="NotProvedOutcome"/>), and a caller of such a function, which the engine
/// skips, is admitted here (<see cref="AdmittedByTheHarness"/>).
/// </summary>
internal sealed class EffectCorpus : IDisposable
{
    private readonly Dictionary<string, string> _admittedByTheHarness = new(StringComparer.Ordinal);

    /// <param name="compilation">The compilation extraction reads.</param>
    /// <param name="clr">
    /// The compilation loaded for the CLR side, when not <paramref name="compilation"/> itself: plan U22's copy with
    /// members added (<see cref="ContractCompilation"/>), whose existing members are unchanged.
    /// </param>
    public EffectCorpus(CSharpCompilation compilation, CSharpCompilation? clr = null)
    {
        Extraction = EngineCorpus.Extract(compilation);
        var inputs = EngineCorpus.Inputs(Extraction);
        Run = Pipeline.Run(inputs, EngineFixture.SharedBundle.Value, EngineOptions.Default with { Kernel = KernelLimits.Corpus, Attributes = EngineFixture.SharedSidecar.Value });
        Run.Environment.Freeze();
        Environment = Run.Environment.Fork();
        KernelThread.Run(() => AdmitCallersOfUnprovedContracts(inputs));
        Environment.Freeze();
        // The witness copies (#233) are added members; the methods compared are unchanged.
        Assembly = CorpusAssembly.Load(AssertWitness.Add(clr ?? compilation, out var witnesses));
        Witnesses = witnesses;
        var definitions = Extraction.Units.Where(u => u.Unit.Definition is not null).ToDictionary(u => u.Key, u => u.Unit.Definition!, StringComparer.Ordinal);
        var values = new Values(Assembly, definitions);
        Inputs = new Inputs(values);
        Model = new ModelCheck(Environment, values, KernelLimits.Corpus);
    }

    public ExtractionResult Extraction { get; }

    public EngineResult Run { get; }

    /// <summary>The run's environment with the definitions in <see cref="AdmittedByTheHarness"/> admitted: the model's.</summary>
    public KernelEnvironment Environment { get; }

    /// <summary>
    /// The functions whose definition this harness admitted, not the engine, each with the dependency it was skipped for: a
    /// function whose contract obligation is not proved (M6 U10).
    /// </summary>
    public IReadOnlyDictionary<string, string> AdmittedByTheHarness => _admittedByTheHarness;

    /// <summary>
    /// Whether the engine admitted <paramref name="key"/>'s definition: its outcome is <see cref="TranslatedOutcome"/>, or
    /// <see cref="NotProvedOutcome"/> for a contract obligation not proved after the definition, and in either case the
    /// run admitted a definition under the function's name. A unit translation or the kernel rejected
    /// (<see cref="FailedOutcome"/>), one that ran out (<see cref="UndecidedOutcome"/>), one skipped, and a recursive
    /// method whose decrease obligation was not proved (its definition comes after them) are not.
    /// </summary>
    public bool EngineAdmitted(string key)
    {
        var outcome = Run.Find(key);
        var name = LeanNames.ForKey(key);
        bool IsDefinition(KernelDeclaration d) => d is DefinitionDecl { Value.Name: var n } && n == name;
        return outcome switch
        {
            TranslatedOutcome translated => translated.Declarations.Any(IsDefinition),
            NotProvedOutcome { Decrease: null } => Run.Admitted.Any(IsDefinition),
            _ => false,
        };
    }

    /// <summary>Fails unless <paramref name="key"/>'s definition was admitted, by the engine or by this harness.</summary>
    public void AssertDefinitionAdmitted(string key) =>
        Assert.True(
            EngineAdmitted(key) || _admittedByTheHarness.ContainsKey(key),
            $"{key}: its definition was not admitted, so there is no model to compare: {Run.Find(key)}");

    /// <summary>
    /// A function the engine skips because a function it depends on has a contract obligation that is not proved (M6 U10:
    /// such a function is not usable as a lemma) still has a definition, over that function's admitted definition. It is
    /// translated as the engine translates it and admitted into <see cref="Environment"/> here, in dependency order, so
    /// that its model is compared too. Only a skip whose dependency's definition is admitted qualifies; a skip for a
    /// dependency that failed to translate or was rejected does not.
    /// </summary>
    private void AdmitCallersOfUnprovedContracts(IReadOnlyList<EngineUnit> inputs)
    {
        bool Present(string key) => EngineAdmitted(key) || _admittedByTheHarness.ContainsKey(key);
        bool Candidate(UnitOutcome outcome) => outcome is SkippedOutcome && outcome.UnitKind == VirUnitKind.Function;
        if (!Run.Units.Any(Candidate))
        {
            return;
        }
        // What the engine translated: every unit not failed, cancelled or skipped, then each skipped one whose dependency is.
        var translated = Run.Units.Where(o => o is not (FailedOutcome or SkippedOutcome or CancelledOutcome)).Select(o => o.Key).ToHashSet(StringComparer.Ordinal);
        bool grown = true;
        while (grown)
        {
            grown = false;
            foreach (var skipped in Run.Units.OfType<SkippedOutcome>().Where(s => !translated.Contains(s.Key) && translated.Contains(s.Dependency)))
            {
                grown |= translated.Add(skipped.Key);
            }
        }
        var units = inputs.Where(u => translated.Contains(u.Unit.Key)).ToList();
        var translation = Translator.Translate(
            units.Select(u => u.Unit),
            EngineFixture.SharedBundle.Value.Env,
            units.Where(u => u.DisplayName is not null).ToDictionary(u => u.Unit.Key, u => u.DisplayName!, StringComparer.Ordinal));
        foreach (var unit in translation.Units)
        {
            if (Run.Find(unit.Key) is not SkippedOutcome skipped || !Candidate(skipped) || !Present(skipped.Dependency) || unit.Recursion is not null)
            {
                continue;
            }
            foreach (var declaration in unit.Declarations)
            {
                Kernel.Kernel.Add(Environment, declaration, KernelLimits.Corpus);
            }
            _admittedByTheHarness.Add(unit.Key, skipped.Dependency);
        }
    }

    public CorpusAssembly Assembly { get; }

    /// <summary>The name of each verified method's witness copy (<see cref="AssertWitness"/>), by the method's key.</summary>
    public IReadOnlyDictionary<string, string> Witnesses { get; }

    /// <summary>
    /// Whether the witness copy of a function fails on these arguments: a false <c>Spec.Assert</c> or an overflow of
    /// default-context arithmetic (#233); only a false <c>Spec.Assert</c> when the original run threw
    /// <see cref="OverflowException"/> (<paramref name="thrown"/>, #266); null when it has none.
    /// </summary>
    public bool? WitnessFails(ExtractedUnit unit, IReadOnlyList<object?> args, Exception? thrown = null) =>
        AssertWitness.Fails(Assembly.MethodOf(unit.Unit), Witnesses.GetValueOrDefault(unit.Key), args, thrown);

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
        AssertDefinitionAdmitted(unit.Key);
        var method = Assembly.MethodOf(unit.Unit);
        var types = ModelCheck.ParameterTypes(unit.Unit);
        var returns = ModelCheck.Returned(unit.Unit);
        var raising = Model.IsRaising(unit.Unit);
        // A raising method's skips need its witness copy (#266): without one they would fall back to the model's word.
        if (raising && unit.Key.StartsWith("M:", StringComparison.Ordinal) && !Witnesses.ContainsKey(unit.Key))
        {
            throw new InvalidOperationException($"{unit.Key} is a raising method with no witness copy (AssertWitness); its skips could not be confirmed.");
        }
        return args =>
        {
            var description = $"{unit.DisplayName}({string.Join(", ", args.Select((a, i) => Model.Values.Display(types[i], a)))})";
            object? result = null;
            Exception? thrown = null;
            try
            {
                // An async function is awaited (plan U22): the model is its awaited value's.
                result = method.IsStatic
                    ? CorpusAssembly.InvokeAndAwait(method, null, args)
                    : CorpusAssembly.InvokeAndAwait(method, args[0], args.Skip(1).ToList());
            }
#pragma warning disable CA1031 // Compared with the model's error, or reported for a pure function.
            catch (Exception ex)
#pragma warning restore CA1031
            {
                thrown = ex;
            }
            if (raising)
            {
                return Model.CheckRaising(description, returns, Model.Run(unit.Unit, args), result, thrown, () => WitnessFails(unit, args, thrown));
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
        ("accepted", "M:Corpus.M6.Effects.DivisibleByFour(System.Int32)"),
        ("accepted", "M:Corpus.M6.Effects.Closed(System.Int32)"),
        ("accepted", "M:Corpus.Rejected.Types.NullableParameter(Corpus.Rejected.Point)"),
        ("accepted", "M:Corpus.Rejected.Types.ReturnsNull"),
        ("accepted", "M:Corpus.M6.Nullables.OrZero(System.Nullable{System.Int32})"),
        ("accepted", "M:Corpus.M6.Nullables.OrDefault(System.Nullable{System.Int64})"),
        ("accepted", "M:Corpus.M6.Nullables.Wrap(System.Int32)"),
        ("accepted", "M:Corpus.M6.Nullables.ValueWhenKnown(System.Nullable{System.Int32})"),
        // decimal (M6 U21), compared by representation: sign, mantissa and scale.
        ("accepted", "M:Corpus.Rejected.Statements.Decimals(System.Decimal)"),
        ("accepted", "M:Corpus.M6.Decimals.AtLeastOne(System.Decimal)"),
        ("accepted", "M:Corpus.M6.Decimals.SameAmount(Corpus.M6.Payment,Corpus.M6.Payment)"),
        ("accepted", "M:Corpus.M6.Decimals.SamePayment(Corpus.M6.Payment,Corpus.M6.Payment)"),
        ("accepted", "M:Corpus.M6.Decimals.Negate(System.Decimal)"),
        ("accepted", "M:Corpus.M6.Decimals.Largest(System.Decimal,System.Decimal)"),
        ("accepted", "M:Corpus.M6.Decimals.Smallest(System.Decimal,System.Decimal)"),
        ("accepted", "M:Corpus.M6.Decimals.Size(System.Decimal)"),
        // Corpus.M6.Payment has a decimal field.
        ("accepted", "M:Corpus.M6.Nullables.IsMissing(Corpus.M6.Payment)"),
        ("accepted", "M:Corpus.M6.Nullables.Use(Corpus.M6.Payment)"),
        ("accepted", "M:Corpus.M6.Nullables.Guarded(Corpus.M6.Payment)"),
        ("accepted", "M:Corpus.M6.Nullables.IdOrZero(Corpus.M6.Payment)"),
        // Records with nullable fields (#218): $eq against the CLR's generated Equals, and the fields read and updated.
        ("accepted", "M:Corpus.M6.Refunds.SameFee(Corpus.M6.Fee,Corpus.M6.Fee)"),
        ("accepted", "M:Corpus.M6.Refunds.SameRefund(Corpus.M6.Refund,Corpus.M6.Refund)"),
        ("accepted", "M:Corpus.M6.Refunds.DaysOrZero(Corpus.M6.Fee)"),
        ("accepted", "M:Corpus.M6.Refunds.Waived(Corpus.M6.Fee)"),
        ("accepted", "M:Corpus.M6.Refunds.OriginalIdOrZero(Corpus.M6.Refund)"),
        ("refuted", "M:Corpus.M6.Refuted.Refunds.OriginalId(Corpus.M6.Refuted.Refund)"),
        ("refuted", "M:Corpus.M6.Refuted.Decimals.AddFee(System.Decimal)"),
        ("refuted", "M:Corpus.M6.Refuted.Decimals.Difference(System.Decimal,System.Decimal)"),
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
        // Contracts (M6 U10). A Spec.Requires is not checked at run time and the model is the body as is, so the inputs
        // that violate one are compared too; Average's Spec.Assert skips the inputs on which a + b wraps below zero.
        ("accepted", "M:Corpus.M6.Contracts.NonNegative(System.Int32)"),
        ("accepted", "M:Corpus.M6.Contracts.AtMost(System.Int32,System.Int32)"),
        ("accepted", "M:Corpus.M6.Contracts.Capped(System.Int32)"),
        ("accepted", "M:Corpus.M6.Contracts.Average(System.Int32,System.Int32)"),
        ("accepted", "M:Corpus.M6.Contracts.Same(System.Int32)"),
        // Spec.NoThrow (#182): the guard throws only where the Requires is violated, which the comparison covers.
        ("accepted", "M:Corpus.M6.Contracts.Quotient(System.Int32,System.Int32)"),
        ("accepted", "M:Corpus.M6.Contracts.Half(System.Int32)"),
        ("accepted", "M:Corpus.M6.Contracts.Sum(System.Int32,System.Int32)"),
        // Spec.Implies in a Spec.Ensures (#213).
        ("accepted", "M:Corpus.M6.Contracts.Successor(System.Int32)"),
        // Refuted contracts (M6 U14): the model is the body, whether or not the contract holds.
        ("refuted", "M:Corpus.M6.Refuted.Contracts.Ratio(System.Int32,System.Int32)"),
        ("refuted", "M:Corpus.M6.Refuted.Contracts.Neg(System.Int32)"),
        ("refuted", "M:Corpus.M6.Refuted.Contracts.Share(System.Int32)"),
        ("refuted", "M:Corpus.M6.Refuted.Contracts.ShareOfNothing"),
        ("refuted", "M:Corpus.M6.Refuted.Contracts.Twice(System.Int32)"),
        ("refuted", "M:Corpus.M6.Refuted.Contracts.Kept(System.Int32)"),
        ("refuted", "M:Corpus.M6.Refuted.Contracts.Asserted(System.Int32,System.Int32)"),
        ("refuted", "M:Corpus.M6.Refuted.Contracts.Impossible(System.Int32)"),
        ("refuted", "M:Corpus.M6.Refuted.Contracts.QuotientOfAny(System.Int32,System.Int32)"),
        ("refuted", "M:Corpus.M6.Refuted.Contracts.SumUnbounded(System.Int32,System.Int32)"),
        ("refuted", "M:Corpus.M6.Refuted.Contracts.Grown(System.Int32)"),
    ];

    /// <summary>
    /// The functions without dependencies that are not compared yet, each with the reason. Empty: every one is compared.
    /// <see cref="EveryM6FunctionWithoutDependenciesIsComparedOrSkippedForAReason"/> fails if one of these translates.
    /// </summary>
    private static readonly Dictionary<string, string> Skipped = new(StringComparer.Ordinal);

    /// <summary>
    /// The compared functions the engine skips because a function they call has a contract obligation that is not proved
    /// (M6 U10), whose definition the harness admits itself (<see cref="EffectCorpus.AdmittedByTheHarness"/>), each with
    /// that callee. Empty: the default procedure (M6 U11) proves every accepted obligation, AtMost's included, so the engine
    /// admits Capped; <see cref="EveryM6FunctionWithoutDependenciesIsComparedOrSkippedForAReason"/> fails if the harness
    /// admits a compared function again.
    /// </summary>
    private static readonly Dictionary<string, string> AdmittedByTheHarness = new(StringComparer.Ordinal);

    /// <summary>The namespaces of the functions with dependencies (and their async helpers), which <see cref="DependencyDifferentialTests"/> compares (plan U22).</summary>
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
            var side = corpus[compilation];
            side.AssertDefinitionAdmitted(key);
            var outcome = side.Run.Find(key);
            output.WriteLine($"{key}: {outcome!.GetType().Name}{(side.AdmittedByTheHarness.ContainsKey(key) ? ", admitted by the harness" : "")}");
        }
        foreach (var (key, reason) in Skipped)
        {
            var compilation = functions.Single(f => f.Key == key).Compilation;
            Assert.False(corpus[compilation].EngineAdmitted(key), $"{key} is admitted now ({reason}): compare it (move it from Skipped to Covered).");
        }
        Assert.Equal(
            AdmittedByTheHarness.OrderBy(p => p.Key, StringComparer.Ordinal),
            M6DifferentialFixture.Compilations
                .SelectMany(c => corpus[c].AdmittedByTheHarness.Where(p => Covered.Contains((c, p.Key))))
                .OrderBy(p => p.Key, StringComparer.Ordinal));
        output.WriteLine($"{Covered.Length} functions compared ({AdmittedByTheHarness.Count} admitted by the harness), {Skipped.Count} skipped");
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
    /// A <c>decimal</c> result is compared by representation (sign, mantissa and scale), not by C#'s <c>==</c>, which ignores
    /// scale: a result equal in value at another scale, or zero of the other sign, is a disagreement, reported with both
    /// representations; pure and raising functions alike.
    /// </summary>
    [Fact]
    public void ADecimalResultIsComparedByRepresentation()
    {
        var accepted = corpus["accepted"];
        var negate = accepted.Unit("M:Corpus.M6.Decimals.Negate(System.Decimal)").Unit;
        var refuted = corpus["refuted"];
        var addFee = refuted.Unit("M:Corpus.M6.Refuted.Decimals.AddFee(System.Decimal)").Unit;
        var negativeZero = Generators.Negate(0m);
        Assert.Equal(-1.0m, -1.00m);
        Assert.Equal(0m, negativeZero);
        KernelThread.Run(() =>
        {
            Assert.False(accepted.Model.IsRaising(negate));
            string? Negate(decimal input, decimal clr) =>
                accepted.Model.Disagreement($"Negate({Values.DisplayDecimal(input)})", VirType.Decimal, accepted.Model.Application(negate, [input]), clr);
            Assert.Null(Negate(1.0m, -1.0m));
            Assert.Null(Negate(0m, negativeZero));
            Assert.Contains("Negate(1.0m): the CLR returned -1.00m but the model computes -1.0m", Negate(1.0m, -1.00m), StringComparison.Ordinal);
            Assert.Contains("Negate(0m): the CLR returned 0m but the model computes -0m", Negate(0m, 0m), StringComparison.Ordinal);

            Assert.True(refuted.Model.IsRaising(addFee));
            var run = refuted.Model.Run(addFee, [1.0m]);
            Assert.Same(InputCheck.Agrees, refuted.Model.CheckRaising("AddFee(1.0m)", VirType.Decimal, run, 2.25m, null));
            Assert.Contains(
                "AddFee(1.0m): the CLR returned 2.250m but the model computes ok 2.25m",
                refuted.Model.CheckRaising("AddFee(1.0m)", VirType.Decimal, run, 2.250m, null).Disagreement,
                StringComparison.Ordinal);
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
    /// names, <c>assertFailed</c> is skipped (#186), and <c>external</c> is the mocks' sentinel, <see cref="MockException"/> (plan U22).
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

            [Verified]
            public static int Sum(int a, int b)
            {
                Spec.Assert(true);
                return a + b;
            }

            [Verified]
            public static int Narrow(long l)
            {
                Spec.Assert(true);
                return (int)l;
            }

            [Verified]
            public static int Bumped(int a)
            {
                Spec.Assert(a != 5);
                return checked(a + 1);
            }

            [Verified]
            public static void Positive(int x) => Spec.Assert(x > 0);

            [Verified]
            public static void CallsPositive(int x) => Positive(x);
        }
        """;

    /// <summary>
    /// A skip is confirmed on the CLR (#233): the witness copy of the method fails where a <c>Spec.Assert</c> is false or
    /// default-context <c>+</c>, <c>-</c>, <c>*</c> or unary <c>-</c> overflows, not where a default-context narrowing wraps
    /// (the model wraps there too); when the original run itself threw <see cref="OverflowException"/>, only a false
    /// <c>Spec.Assert</c> witnesses it (#266). An <c>assertFailed</c> run the CLR does not witness is a disagreement, not a
    /// skip, so a mistranslated condition cannot hide behind it. An expression-bodied void method, an assertion or a call,
    /// has a copy too.
    /// </summary>
    [Fact]
    public void ASkipMustBeWitnessedOnTheClr()
    {
        using var side = new EffectCorpus(Warrant.Frontend.CompilationFactory.Create(
            [new Warrant.Frontend.SourceFile("Assertions.cs", "using Warrant;\n" + Assertions)], checkOverflow: false));
        var nonZero = side.Unit("M:S.NonZero(System.Int32)");
        var sum = side.Unit("M:S.Sum(System.Int32,System.Int32)");
        Assert.Equal((true, false), (side.WitnessFails(nonZero, [0]), side.WitnessFails(nonZero, [5])));
        Assert.Equal((true, false), (side.WitnessFails(sum, [int.MaxValue, 1]), side.WitnessFails(sum, [1, 2])));
        // A default-context narrowing wraps in the copy as in the model.
        var narrow = side.Unit("M:S.Narrow(System.Int64)");
        Assert.Equal((false, false), (side.WitnessFails(narrow, [long.MaxValue]), side.WitnessFails(narrow, [1L])));
        // Where the original threw OverflowException, an explicit checked overflow is no witness; a false assert is.
        var bumped = side.Unit("M:S.Bumped(System.Int32)");
        Assert.Throws<OverflowException>(() => CorpusAssembly.Invoke(side.Assembly.MethodOf(bumped.Unit), [int.MaxValue]));
        Assert.Equal(true, side.WitnessFails(bumped, [int.MaxValue]));
        Assert.Equal(false, side.WitnessFails(bumped, [int.MaxValue], new OverflowException()));
        Assert.Equal(true, side.WitnessFails(bumped, [5], new OverflowException()));
        // Expression-bodied void methods, which extraction refuses but which still get a copy: an assertion, and a call whose
        // callee's assertion the copy does not see.
        bool? Fails(string name, int x) => AssertWitness.Fails(
            side.Assembly.Assembly.GetType("S", throwOnError: true)!.GetMethod(name)!, side.Witnesses[$"M:S.{name}(System.Int32)"], [x]);
        Assert.Equal((true, false), (Fails("Positive", 0), Fails("Positive", 1)));
        Assert.Equal(false, Fails("CallsPositive", 0));
        // The original methods are unchanged: the assert does nothing and the sum wraps.
        Assert.Equal(int.MinValue, CorpusAssembly.Invoke(side.Assembly.MethodOf(sum.Unit), [int.MaxValue, 1]));

        var sumCheck = side.Checker(sum);
        var run = new EffectRun();
        KernelThread.Run(() =>
        {
            run.Record(sumCheck([int.MaxValue, 1]));
            run.Record(sumCheck([1, 2]));
            var model = side.Model.Run(nonZero.Unit, [0]);
            Assert.Same(InputCheck.Skipped, side.Model.CheckRaising("NonZero(0)", VirType.Int32, model, 100, null, () => true));
            var unwitnessed = side.Model.CheckRaising("NonZero(0)", VirType.Int32, model, 100, null, () => false);
            Assert.False(unwitnessed.IsSkipped);
            Assert.Contains(
                "NonZero(0): the model computes error assertFailed, but on the CLR every Spec.Assert holds and no default-context arithmetic overflows (the CLR returned 100)",
                unwitnessed.Disagreement, StringComparison.Ordinal);
        });
        Assert.Empty(run.Disagreements);
        Assert.Equal((2, 1), (run.Checked, run.Skipped));
    }

    /// <summary>
    /// End to end (#266): when the CLR's own method asserts something other than what the method extraction read asserts,
    /// the model's <c>assertFailed</c> is not witnessed, and the checker reports a disagreement rather than a skip.
    /// </summary>
    [Fact]
    public void AnAssertTheClrDoesNotFailIsADisagreement()
    {
        var extracted = Warrant.Frontend.CompilationFactory.Create(
            [new Warrant.Frontend.SourceFile("Assertions.cs", "using Warrant;\n" + Assertions)], checkOverflow: false);
        var clr = Warrant.Frontend.CompilationFactory.Create(
            [new Warrant.Frontend.SourceFile("Assertions.cs", "using Warrant;\n" + Assertions.Replace("Spec.Assert(x == 0);", "Spec.Assert(true);", StringComparison.Ordinal))],
            checkOverflow: false);
        using var side = new EffectCorpus(extracted, clr);
        var check = side.Checker(side.Unit("M:S.OnlyZero(System.Int32)"));
        var (zero, five) = KernelThread.Run(() => (check([0]), check([5])));
        Assert.Same(InputCheck.Agrees, zero);
        Assert.False(five.IsSkipped);
        Assert.Contains("the model computes error assertFailed, but on the CLR every Spec.Assert holds", five.Disagreement, StringComparison.Ordinal);
    }

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

    // ---- Generated equality of records with nullable fields (#218, #253) ----

    private const string NullableFields = """
        #nullable enable
        [Closed]
        public sealed class Shade
        {
            public static Shade Light { get; } = new();

            public static Shade Dark { get; } = new();

            private Shade()
            {
            }
        }

        public sealed record Flags(bool? On, Shade? Color);

        public sealed record Inner(bool? Paid);

        public sealed record Outer(Inner? Maybe, Inner Always, int? Days);

        public static class E
        {
            [Verified]
            public static bool SameFlags(Flags a, Flags b) => a == b;

            [Verified]
            public static bool SameOuter(Outer a, Outer b) => a == b;
        }
        """;

    /// <summary>
    /// A record's generated <c>$eq</c> agrees with the CLR's generated <c>Equals</c> for a <c>bool?</c> field, a nullable
    /// closed class field, and a record nested in a record, nullable or not, whose own fields are nullable (#253), on every
    /// boundary combination and on random inputs. A nullable closed enum is not a nullable type M6 supports
    /// (<c>Nullable&lt;T&gt;</c> of <c>bool</c>, <c>int</c>, <c>long</c> or <c>decimal</c> only, KTD5), so a record cannot
    /// have one.
    /// </summary>
    [Fact]
    public void NullableFieldEqualityAgreesWithTheClrForBoolClosedClassAndNestedRecords()
    {
        using var side = new EffectCorpus(Warrant.Frontend.CompilationFactory.Create(
            [new Warrant.Frontend.SourceFile("NullableFields.cs", "using Warrant;\n" + NullableFields)], checkOverflow: false));
        Assert.Empty(side.Extraction.Diagnostics);
        foreach (var key in new[] { "M:E.SameFlags(Flags,Flags)", "M:E.SameOuter(Outer,Outer)" })
        {
            var unit = side.Unit(key);
            var types = ModelCheck.ParameterTypes(unit.Unit);
            var check = side.Checker(unit);
            var run = new EffectRun();
            var boundaries = side.Inputs.BoundaryInputs(types);
            var equal = 0;
            KernelThread.Run(() =>
            {
                foreach (var input in boundaries)
                {
                    run.Record(check(input));
                    equal += Equals(input[0], input[1]) ? 1 : 0;
                }
                Pbt.Check(Prop.ForAll(side.Inputs.Arbitrary(types), args =>
                {
                    if (run.Record(check(args)) is { } disagreement)
                    {
                        throw new XunitException(disagreement);
                    }
                }), Pbt.Config(RandomInputsPerFunction));
            });
            output.WriteLine($"{key}: {run.Checked} inputs, {equal} equal boundary pairs");
            Assert.True(run.Disagreements.Count == 0, run.Report());
            Assert.Equal(0, run.Skipped);
            // Both outcomes are compared: some boundary pairs are equal, most are not.
            Assert.InRange(equal, 1, boundaries.Count - 1);
        }

        var closedEnum = EngineCorpus.Extract(Warrant.Frontend.CompilationFactory.Create(
            [new Warrant.Frontend.SourceFile("ClosedEnum.cs", "using Warrant;\n[Closed] public enum Light { Red, Green }\npublic sealed record Lamp(Light? Color);\n"
                + "public static class L { [Verified] public static bool Same(Lamp a, Lamp b) => a == b; }\n")], checkOverflow: false));
        Assert.Contains(closedEnum.Diagnostics, d => (d.Id, d.Construct) == ("WRT0002", "nullable type"));
        Assert.Null(closedEnum.Find("M:L.Same(Lamp,Lamp)"));
    }

    // ---- Which definitions are compared ----

    private const string Admission = """
        public static class A
        {
            [Verified]
            public static int Bounded(int x)
            {
                Spec.Requires(x >= 0);
                Spec.Ensures<int>(r => r > x);
                return x;
            }

            [Verified]
            public static int CallsBounded(int x) => Bounded(x < 0 ? 0 : x);

            [Verified]
            public static int Climb(int n)
            {
                Spec.Decreases(n);
                return n <= 0 ? 0 : Climb(n + 1);
            }

            [Verified]
            public static int CallsClimb(int n) => Climb(n);
        }
        """;

    /// <summary>
    /// A function whose contract obligation is not proved is compared, by its definition the engine admitted before the
    /// obligation, and so is a caller the engine skips for it, admitted by the harness. A recursive method whose decrease
    /// obligation is not proved has no admitted definition, nor its caller: neither is compared.
    /// </summary>
    [Fact]
    public void OnlyAnAdmittedDefinitionIsCompared()
    {
        using var side = new EffectCorpus(Warrant.Frontend.CompilationFactory.Create(
            [new Warrant.Frontend.SourceFile("Admission.cs", "using Warrant;\n" + Admission)], checkOverflow: false));
        // Its obligation, r > x for r = x, is false: not proved now, nor once M6 U11's default procedure runs on it.
        Assert.Null(Assert.IsType<NotProvedOutcome>(side.Run.Find("M:A.Bounded(System.Int32)")).Decrease);
        Assert.True(side.EngineAdmitted("M:A.Bounded(System.Int32)"));
        Assert.IsType<SkippedOutcome>(side.Run.Find("M:A.CallsBounded(System.Int32)"));
        Assert.False(side.EngineAdmitted("M:A.CallsBounded(System.Int32)"));
        Assert.Equal(new Dictionary<string, string> { ["M:A.CallsBounded(System.Int32)"] = "M:A.Bounded(System.Int32)" }, side.AdmittedByTheHarness);

        Assert.NotNull(Assert.IsType<NotProvedOutcome>(side.Run.Find("M:A.Climb(System.Int32)")).Decrease);
        Assert.False(side.EngineAdmitted("M:A.Climb(System.Int32)"));
        Assert.IsType<SkippedOutcome>(side.Run.Find("M:A.CallsClimb(System.Int32)"));
        Assert.Throws<TrueException>(() => side.AssertDefinitionAdmitted("M:A.Climb(System.Int32)"));
        Assert.Throws<TrueException>(() => side.AssertDefinitionAdmitted("M:A.CallsClimb(System.Int32)"));

        foreach (var key in new[] { "M:A.Bounded(System.Int32)", "M:A.CallsBounded(System.Int32)" })
        {
            var check = side.Checker(side.Unit(key));
            var run = new EffectRun();
            KernelThread.Run(() =>
            {
                foreach (var x in Generators.Int32Boundaries)
                {
                    run.Record(check([x]));
                }
            });
            Assert.True(run.Disagreements.Count == 0, run.Report());
            run.AssertEnoughEvaluated(key);
        }
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
    internal static long Measure(EffectCorpus side, VirUnit unit, System.Reflection.MethodInfo method, object?[] input)
    {
        object? result = null;
        Exception? thrown = null;
        try
        {
            result = method.IsStatic
                ? CorpusAssembly.InvokeAndAwait(method, null, input)
                : CorpusAssembly.InvokeAndAwait(method, input[0], input[1..]);
        }
#pragma warning disable CA1031 // Measured as the model error it matches.
        catch (Exception ex)
#pragma warning restore CA1031
        {
            thrown = ex;
        }
        var returns = ModelCheck.Returned(unit);
        if (!side.Model.IsRaising(unit))
        {
            return side.Model.Measure(returns, side.Model.Application(unit, input), result).Fuel;
        }
        var r = Values.CicType(returns);
        var run = side.Model.Run(unit, input);
        var outcome = thrown is null
            ? ModelCheck.Ok(r, side.Model.Values.Term(returns, result))
            : ClrExceptions.ModelErrors(thrown).Select(e => ModelCheck.Error(r, e)).First(o => side.Model.RunsTo(r, run, o));
        return side.Model.Measure(ModelCheck.RunTheorem(r, run, outcome)).Fuel;
    }
}
