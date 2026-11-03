using System.Diagnostics;
using System.Globalization;
using System.Text;
using FsCheck;
using FsCheck.Fluent;
using Warrant.Kernel;
using Warrant.Semantics;
using Warrant.Vir;
using Xunit.Abstractions;
using Xunit.Sdk;

namespace Warrant.Engine.Tests.Differential;

/// <summary>
/// Every accepted corpus function agrees with its compiled .NET method on generated inputs (docs/m4/07, plan U10, R5,
/// KTD14). Each input is the theorem <c>f args = r</c>, admitted by the kernel or reported with both values.
/// </summary>
[Collection(DifferentialGroup.Name)]
public sealed class DifferentialTests(DifferentialFixture corpus, ITestOutputHelper output)
{
    /// <summary>
    /// Random inputs per function by default, besides every boundary combination. Sized from the measurements in
    /// README.md so that the whole differential suite stays within a few minutes; the boundary combinations are never
    /// reduced. <see cref="Pbt"/> raises it from the environment.
    /// </summary>
    internal const int RandomInputsPerFunction = 1000;

    /// <summary>The accepted corpus's functions, from expected.json (cheap at discovery; the extraction is checked against it).</summary>
    public static TheoryData<string> Functions()
    {
        var data = new TheoryData<string>();
        foreach (var member in EngineCorpus.Expected.GetProperty("members").GetProperty("accepted").EnumerateObject())
        {
            if (member.Name[0] is 'M' or 'P' && member.Value.GetProperty("outcome").GetString() == "translated")
            {
                data.Add(member.Name);
            }
        }
        return data;
    }

    [Fact]
    public void TheFunctionsAreExactlyTheAcceptedCorpusFunctions()
    {
        Assert.Equal(
            ((IEnumerable<object[]>)Functions()).Select(d => (string)d[0]).Order(StringComparer.Ordinal),
            corpus.Functions.Select(u => u.Key).Order(StringComparer.Ordinal));
        Assert.Contains("P:Claims.Assignment.NeedsAlert", corpus.Functions.Select(u => u.Key));
    }

    [Theory]
    [MemberData(nameof(Functions))]
    public void AgreesOnEveryBoundaryCombination(string key)
    {
        var unit = corpus.Unit(key);
        var types = ModelCheck.ParameterTypes(unit.Unit);
        Assert.InRange(types.Count, 1, 3);
        var boundaries = corpus.Inputs.BoundaryInputs(types);
        Assert.Equal(types.Select(t => corpus.Inputs.Boundaries(t).Count).Aggregate(1, (a, b) => a * b), boundaries.Count);

        var run = corpus.Check(unit, boundaries);
        output.WriteLine($"{key}: {boundaries.Count} boundary inputs in {run.Elapsed.TotalSeconds:F2} s");
        Assert.True(run.Disagreements.Count == 0, Report(run));
    }

    /// <summary>
    /// The property that the model agrees with the CLR on every input (M5a KTD26): <see cref="RandomInputsPerFunction"/>
    /// cases from the pinned seed, or what <see cref="Pbt"/> reads from the environment. A failure is shrunk and says
    /// how to replay it.
    /// </summary>
    [Theory]
    [MemberData(nameof(Functions))]
    public void AgreesOnRandomInputs(string key)
    {
        var unit = corpus.Unit(key);
        var check = corpus.Checker(unit);
        var arbitrary = corpus.Inputs.Arbitrary(ModelCheck.ParameterTypes(unit.Unit));
        var config = Pbt.Config(RandomInputsPerFunction);
        var cases = 0;
        var watch = Stopwatch.StartNew();
        KernelThread.Run(() => Pbt.Check(
            Prop.ForAll(arbitrary, args =>
            {
                cases++;
                if (check(args) is { } disagreement)
                {
                    throw new XunitException(disagreement);
                }
            }),
            config));
        output.WriteLine($"{key}: {cases} random inputs in {watch.Elapsed.TotalSeconds:F2} s");
        Assert.Equal(config.MaxTest, cases);
    }

    /// <summary>A failing record input shrinks one field at a time, each toward 0 or a boundary value.</summary>
    [Fact]
    public void ARecordInputShrinksFieldByField()
    {
        var point = corpus.Assembly.TypeOf("T:Claims.Point");
        int X(object? p) => (int)point.GetProperty("X")!.GetValue(p)!;
        var arbitrary = corpus.Inputs.Arbitrary([VirType.Ref("T:Claims.Point")]);
        var failure = Assert.Throws<XunitException>(() => Pbt.Check(Prop.ForAll(arbitrary, args => X(args[0]) >= 0), 100));
        Assert.Contains("Shrunk:\n[|Point { X = -1, Y = 0 }|]", failure.Message.ReplaceLineEndings("\n"), StringComparison.Ordinal);
        Assert.Contains($"Replay with {Pbt.SeedVariable}={Pbt.DefaultSeed.Seed},{Pbt.DefaultSeed.Gamma}", failure.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void AnInstancePropertyTakesItsReceiverAsTheFirstArgument()
    {
        var unit = corpus.Unit("P:Claims.Assignment.NeedsAlert");
        Assert.Equal("T:Claims.Assignment", unit.Unit.Self);
        Assert.Equal([VirType.Ref("T:Claims.Assignment")], ModelCheck.ParameterTypes(unit.Unit));
        var alerting = corpus.Inputs.Boundaries(VirType.Ref("T:Claims.Assignment"))
            .Where(a => (bool)CorpusAssembly.Invoke(corpus.Assembly.MethodOf(unit.Unit), [a])!)
            .Select(a => new[] { a })
            .ToList();
        Assert.Single(alerting); // new Assignment(0, true, ClaimStatus.Open)
        var run = corpus.Check(unit, alerting);
        Assert.True(run.Disagreements.Count == 0, Report(run));
    }

    [Theory]
    [InlineData("M:Claims.Conversions.IsUnnamed(Claims.PaymentStatus)")]
    [InlineData("M:Claims.Conversions.StatusCode(Claims.PaymentStatus)")]
    [InlineData("M:Claims.Payments.Validate(Claims.Payment)")]
    public void AnOpenEnumParameterReceivesUnnamedValuesAndTheModelAgrees(string key)
    {
        var unit = corpus.Unit(key);
        var status = (EnumDefinition)corpus.Model.Values.Definition("T:Claims.PaymentStatus");
        var named = status.Members.Select(m => m.Value).ToHashSet();
        var unnamed = Inputs.EnumValues(status).Where(v => !named.Contains(v)).ToList();
        Assert.Contains((long)int.MinValue, unnamed);
        Assert.Contains((long)int.MaxValue, unnamed);

        var statusType = corpus.Assembly.TypeOf("T:Claims.PaymentStatus");
        var inputs = new List<object?[]>();
        foreach (var v in unnamed)
        {
            var s = Enum.ToObject(statusType, v);
            inputs.Add(key.Contains("Validate", StringComparison.Ordinal)
                ? [Activator.CreateInstance(corpus.Assembly.TypeOf("T:Claims.Payment"), 1, 10, s)] // passes the amount check
                : [s]);
        }
        var method = corpus.Assembly.MethodOf(unit.Unit);
        if (key.Contains("IsUnnamed", StringComparison.Ordinal))
        {
            Assert.All(inputs, i => Assert.Equal(true, CorpusAssembly.Invoke(method, i)));
        }
        if (key.Contains("Validate", StringComparison.Ordinal))
        {
            Assert.All(inputs, i => Assert.Equal("InvalidStatus", CorpusAssembly.Invoke(method, i)!.ToString()));
        }
        var run = corpus.Check(unit, inputs);
        Assert.Equal(unnamed.Count, run.Checked);
        Assert.True(run.Disagreements.Count == 0, Report(run));
    }

    [Fact]
    public void NestedReturnAgreesOnTheInputsThatReachTheNestedReturn()
    {
        var unit = corpus.Unit("M:Corpus.Locals.NestedReturn(System.Boolean,System.Boolean)");
        var inputs = corpus.Inputs.BoundaryInputs(ModelCheck.ParameterTypes(unit.Unit));
        var method = corpus.Assembly.MethodOf(unit.Unit);
        var nested = inputs.Where(i => (int)CorpusAssembly.Invoke(method, i)! == 1).ToList();
        Assert.Equal(new object?[] { true, true }, Assert.Single(nested));
        var run = corpus.Check(unit, nested);
        Assert.True(run.Disagreements.Count == 0, Report(run));
        Assert.Equal(4, corpus.Check(unit, inputs).Checked);
    }

    [Fact]
    public void AWrongModelIsCaughtWithBothValues()
    {
        // Increment(x) = x + 1 on the CLR, checked against x + 2 built from the operator table: test-only, production
        // translation is untouched.
        var increment = corpus.Unit("M:Corpus.Increments.Increment(System.Int32)");
        var method = corpus.Assembly.MethodOf(increment.Unit);
        var messages = KernelThread.Run(() => Generators.Int32Boundaries.Select(x =>
        {
            var wrong = Operators.Binary(BinaryOp.Add, VirPrimitive.Int32, Literals.Int32(x), Literals.Int32(2));
            return corpus.Model.Disagreement($"Increment({x})", VirType.Int32, wrong, CorpusAssembly.Invoke(method, [x]));
        }).ToList());
        Assert.All(messages, m => Assert.NotNull(m));
        Assert.Contains("Increment(0): the CLR returned 1 but the model computes 2", messages[3], StringComparison.Ordinal);
        Assert.Contains("Increment(2147483647): the CLR returned -2147483648 but the model computes -2147483647", messages[6], StringComparison.Ordinal);

        // Two functions swapped: Increment's results against Steps's definition (x + 3 + 1 - 1).
        var steps = corpus.Unit("M:Corpus.Locals.Steps(System.Int32)");
        var swapped = KernelThread.Run(() => corpus.Model.Disagreement(
            "Increment(5)", VirType.Int32, corpus.Model.Application(steps.Unit, [5]), CorpusAssembly.Invoke(method, [5])));
        Assert.NotNull(swapped);
        Assert.Contains("the CLR returned 6 but the model computes 8", swapped, StringComparison.Ordinal);

        // The honest model passes the same check.
        Assert.Null(KernelThread.Run(() => corpus.Model.Disagreement(
            "Increment(5)", VirType.Int32, corpus.Model.Application(increment.Unit, [5]), CorpusAssembly.Invoke(method, [5]))));
    }

    /// <summary>
    /// The cost measurement behind <see cref="RandomInputsPerFunction"/> (README.md): fuel and wall clock per check, per
    /// function, on its boundary inputs. Opt-in, because it repeats every check.
    /// </summary>
    [FactRequiringEnv("WARRANT_DIFFERENTIAL_COST")]
    public void MeasureTheCostOfAChecks()
    {
        var table = new StringBuilder("| Function | Boundary inputs | Fuel per check (mean / max) | ms per check (mean) |\n|---|---|---|---|\n");
        long totalFuel = 0;
        int totalChecks = 0;
        foreach (var unit in corpus.Functions)
        {
            var types = ModelCheck.ParameterTypes(unit.Unit);
            var inputs = corpus.Inputs.BoundaryInputs(types);
            var method = corpus.Assembly.MethodOf(unit.Unit);
            var results = inputs.Select(i => CorpusAssembly.Invoke(method, i)).ToList();
            var measured = KernelThread.Run(() => inputs
                .Select((i, n) => corpus.Model.Measure(unit.Unit.Returns!, corpus.Model.Application(unit.Unit, i), results[n]))
                .ToList());
            var full = corpus.Check(unit, inputs);
            totalFuel += measured.Sum(m => m.Fuel);
            totalChecks += measured.Count;
            table.Append(CultureInfo.InvariantCulture, $"| `{unit.DisplayName}` | {inputs.Count} | {measured.Average(m => m.Fuel):F0} / {measured.Max(m => m.Fuel)} | {full.Elapsed.TotalMilliseconds / inputs.Count:F2} |\n");
        }
        table.Append(CultureInfo.InvariantCulture, $"\n{totalChecks} checks, {totalFuel / totalChecks} fuel per check on average.\n");
        output.WriteLine(table.ToString());
    }

    private static string Report(FunctionRun run) =>
        $"{run.Disagreements.Count} of {run.Checked} inputs disagree:\n{string.Join("\n", run.Disagreements.Take(20))}";
}
