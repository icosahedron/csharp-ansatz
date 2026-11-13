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
        // With the sidecar, as the build runs: a verified method's arithmetic has obligations the default procedure proves (#244).
        Run = Pipeline.Run(EngineCorpus.Inputs(Extraction), Bundle, Options);
        Run.Environment.Freeze();
        Assembly = CorpusAssembly.Load(Compilation);
        var definitions = Extraction.Units.Where(u => u.Unit.Definition is not null).ToDictionary(u => u.Key, u => u.Unit.Definition!, StringComparer.Ordinal);
        var values = new Values(Assembly, definitions);
        Inputs = new Inputs(values);
        Model = new ModelCheck(Run.Environment, values, KernelLimits.Corpus);
    }

    public SemanticsBundle Bundle { get; }

    /// <summary>The engine options of the corpus runs: the corpus kernel fuel and the attribute sidecar.</summary>
    public EngineOptions Options { get; } = EngineOptions.Default with { Kernel = KernelLimits.Corpus, Attributes = EngineFixture.SharedSidecar.Value };

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
        var check = Checker(unit);
        var watch = Stopwatch.StartNew();
        var disagreements = KernelThread.Run(() => inputs.Select(check).OfType<string>().ToList());
        return new FunctionRun(inputs.Count, disagreements, watch.Elapsed);
    }

    /// <summary>
    /// The check of one input of a translated function: null if the model agrees with the CLR, else a message with both
    /// values. The returned function must run on a kernel thread.
    /// </summary>
    internal Func<object?[], string?> Checker(ExtractedUnit unit)
    {
        Assert.IsType<TranslatedOutcome>(Run.Find(unit.Key));
        var method = Assembly.MethodOf(unit.Unit);
        var types = ModelCheck.ParameterTypes(unit.Unit);
        var returns = unit.Unit.Returns!;
        return args =>
        {
            var description = $"{unit.DisplayName}({string.Join(", ", args.Select((a, i) => Model.Values.Display(types[i], a)))})";
            object? result;
            try
            {
                result = CorpusAssembly.Invoke(method, args);
            }
#pragma warning disable CA1031 // Reported as a disagreement: an accepted function must not throw on non-null inputs.
            catch (Exception ex)
#pragma warning restore CA1031
            {
                return $"{description}: the CLR threw {ex.GetType().Name}: {ex.Message}";
            }
            return Model.Disagreement(description, returns, Model.Application(unit.Unit, args), result);
        };
    }

    public void Dispose() => Assembly.Dispose();
}

/// <summary>The result of checking one function on a set of inputs.</summary>
internal sealed record FunctionRun(int Checked, IReadOnlyList<string> Disagreements, TimeSpan Elapsed);
