using System.Diagnostics;
using Microsoft.CodeAnalysis.CSharp;
using Warrant.Extraction;
using Warrant.Kernel;
using Warrant.Vir;

namespace Warrant.Engine.Tests.Differential;

/// <summary>The differential tests share one bundle, one engine run and one loaded corpus assembly.</summary>
[CollectionDefinition(Name)]
public sealed class DifferentialGroup :ICollectionFixture<DifferentialFixture>
{
    public const string Name = "Differential";
}

/// <summary>
/// The accepted corpus on both sides (docs/m4/07): the compilation extraction read, emitted and loaded; and the engine's
/// run over its units, whose environment is frozen so that every check admits into a scratch fork of it.
/// </summary>
public sealed class DifferentialFixture : IDisposable
{
    public DifferentialFixture()
    {
        Bundle = EngineFixture.SharedBundle.Value;
        Compilation = EngineCorpus.Compile("accepted");
        Extraction = EngineCorpus.Extract(Compilation);
        Run = Pipeline.Run(EngineCorpus.Inputs(Extraction), Bundle, KernelLimits.Corpus);
        Run.Environment.Freeze();
        Assembly = CorpusAssembly.Load(Compilation);
        var definitions = Extraction.Units.Where(u => u.Unit.Definition is not null).ToDictionary(u => u.Key, u => u.Unit.Definition!, StringComparer.Ordinal);
        var values = new Values(Assembly, definitions);
        Inputs = new Inputs(values);
        Model = new ModelCheck(Run.Environment, values, KernelLimits.Corpus);
    }

    public SemanticsBundle Bundle { get; }

    internal CSharpCompilation Compilation { get; }

    internal ExtractionResult Extraction { get; }

    public EngineResult Run { get; }

    internal CorpusAssembly Assembly { get; }

    internal Inputs Inputs { get; }

    internal ModelCheck Model { get; }

    /// <summary>The accepted corpus's function units, in extraction order.</summary>
    internal IEnumerable<ExtractedUnit> Functions => Extraction.Units.Where(u => u.Unit.Kind == VirUnitKind.Function);

    internal ExtractedUnit Unit(string key) => Extraction.Find(key) ?? throw new InvalidOperationException($"{key} was not extracted");

    /// <summary>
    /// Runs a function on the CLR and checks the model against each result. Every function must be translated by the run.
    /// </summary>
    internal FunctionRun Check(ExtractedUnit unit, IReadOnlyList<object?[]> inputs)
    {
        Assert.IsType<TranslatedOutcome>(Run.Find(unit.Key));
        var method = Assembly.MethodOf(unit.Unit);
        var types = ModelCheck.ParameterTypes(unit.Unit);
        var returns = unit.Unit.Returns!;
        var calls = inputs.Select(args =>
        {
            var description = $"{unit.DisplayName}({string.Join(", ", args.Select((a, i) => Model.Values.Display(types[i], a)))})";
            try
            {
                return (args, description, Result: CorpusAssembly.Invoke(method, args), Error: (Exception?)null);
            }
#pragma warning disable CA1031 // Reported as a disagreement: an accepted function must not throw on non-null inputs.
            catch (Exception ex)
#pragma warning restore CA1031
            {
                return (args, description, Result: null, Error: ex);
            }
        }).ToList();
        var watch = Stopwatch.StartNew();
        var disagreements = KernelThread.Run(() => calls
            .Select(c => c.Error is { } error
                ? $"{c.description}: the CLR threw {error.GetType().Name}: {error.Message}"
                : Model.Disagreement(c.description, returns, Model.Application(unit.Unit, c.args), c.Result))
            .OfType<string>()
            .ToList());
        return new FunctionRun(calls.Count, disagreements, watch.Elapsed);
    }

    public void Dispose() => Assembly.Dispose();
}

/// <summary>The result of checking one function on a set of inputs.</summary>
internal sealed record FunctionRun(int Checked, IReadOnlyList<string> Disagreements, TimeSpan Elapsed);
