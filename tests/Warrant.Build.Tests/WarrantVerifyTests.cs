namespace Warrant.Build.Tests;

using Microsoft.Build.Framework;
using Warrant.Build;

public sealed class WarrantVerifyTests : IDisposable
{
    private const string Diagnostic =
        "WRT1\tdiag\terror\tWRT0001\tIncrements.cs\t7\t17\t7\t40\ttheorem 'Increment_Gt' could not be proved; counterexample x = 2147483647\\n{goal}\\nx : Int32\\n⊢ x + 1 > x";

    private const string Goal = "WRT1\tgoal\tinfo\t\t\t0\t0\t0\t0\tx : Int32\\n⊢ x + 1 > x";

    private const string Summary = "WRT1\tsummary\tinfo\t\t\t0\t0\t0\t0\tWarrant: 1 verified unit, 0 theorems proved, 1 not proved.";

    private readonly FakeCli fake = new();
    private readonly RecordingBuildEngine engine = new();

    public void Dispose() => fake.Dispose();

    [Fact]
    public void AFailedTheoremIsOneErrorAtItsLocationWithTheGoalAlsoLogged()
    {
        fake.Script([Diagnostic, Goal, Summary], exitCode: 1);

        Assert.False(Run(Task()));

        var error = Assert.Single(engine.Errors);
        Assert.Equal("WRT0001", error.Code);
        Assert.Equal("Increments.cs", error.File);
        Assert.Equal((7, 17, 7, 40), (error.LineNumber, error.ColumnNumber, error.EndLineNumber, error.EndColumnNumber));
        Assert.Equal(
            "theorem 'Increment_Gt' could not be proved; counterexample x = 2147483647\n{goal}\nx : Int32\n⊢ x + 1 > x",
            error.Message);
        Assert.Contains(engine.Messages, m => m.Importance == MessageImportance.High && m.Message == "x : Int32\n⊢ x + 1 > x");
        Assert.Contains(engine.Messages, m => m.Importance == MessageImportance.High && m.Message == "Warrant: 1 verified unit, 0 theorems proved, 1 not proved.");
        Assert.DoesNotContain(engine.Messages, m => m.Message?.Contains("MSB6006", StringComparison.Ordinal) == true);
    }

    [Fact]
    public void WarningsAndInformationDoNotFailTheBuild()
    {
        fake.Script(
            [
                "WRT1\tdiag\twarning\tWRT0008\tA.cs\t3\t1\t3\t9\tunused theorem",
                "WRT1\tdiag\tinfo\tWRT0099\tA.cs\t4\t1\t0\t0\tnote",
                "building …",
                "Warrant: 1 verified unit, 1 theorem proved, 0 not proved.",
            ],
            exitCode: 0);

        Assert.True(Run(Task()));

        Assert.Empty(engine.Errors);
        var warning = Assert.Single(engine.Warnings);
        Assert.Equal(("WRT0008", "A.cs", 3, 1, "unused theorem"), (warning.Code, warning.File, warning.LineNumber, warning.ColumnNumber, warning.Message));
        Assert.Contains(engine.Messages, m => m.Code == "WRT0099" && m.File == "A.cs" && m.LineNumber == 4 && m.Message == "note");
        Assert.Contains(engine.Messages, m => m.Importance == MessageImportance.Normal && m.Message == "building …");
        Assert.Contains(engine.Messages, m => m.Importance == MessageImportance.High && m.Message == "Warrant: 1 verified unit, 1 theorem proved, 0 not proved.");
    }

    [Fact]
    public void TheServerFallbackRecordIsANormalImportanceMessageNotAWarning()
    {
        // M5b KTD5: a message keeps TreatWarningsAsErrors builds green when the server cannot be used.
        const string fallback = "Warrant: verification server unavailable (connecting to the server timed out after 5 s); verifying in-process.";
        fake.Script([$"WRT1\tdiag\tinfo\t\t\t0\t0\t0\t0\t{fallback}", Summary.Replace("not proved.", "not proved. [in-process]", StringComparison.Ordinal)], exitCode: 0);

        Assert.True(Run(Task()));

        Assert.Empty(engine.Warnings);
        Assert.Empty(engine.Errors);
        var message = Assert.Single(engine.Messages, m => m.Message == fallback);
        Assert.Equal(MessageImportance.Normal, message.Importance);
    }

    [Fact]
    public void ExitTwoIsWrt0010QuotingTheTailOfTheErrorOutput()
    {
        var stderr = Enumerable.Range(1, 25).Select(i => $"stderr line {i}").ToArray();
        fake.Script(["WRT1\tdiag\terror\tWRT0012\t\t0\t0\t0\t0\tmissing symbols"], exitCode: 2, stderr);

        Assert.False(Run(Task()));

        Assert.Equal(["WRT0012", "WRT0010"], engine.Errors.Select(e => e.Code));
        var internalError = engine.Errors[1].Message;
        Assert.StartsWith("Warrant: the warrant CLI reported a usage or internal error (exit code 2).", internalError, StringComparison.Ordinal);
        Assert.EndsWith("\nstderr line 6\n" + string.Join("\n", stderr.Skip(6)), internalError, StringComparison.Ordinal);
        Assert.DoesNotContain("stderr line 5\n", internalError, StringComparison.Ordinal);
        Assert.DoesNotContain(engine.Errors, e => e.Code == "MSB6006");
    }

    [Fact]
    public void ExitOneWithNoErrorRecordIsWrt0010()
    {
        fake.Script(["Warrant: 0 verified units, 0 theorems proved, 0 not proved."], exitCode: 1, ["unexpected"]);

        Assert.False(Run(Task()));

        var error = Assert.Single(engine.Errors);
        Assert.Equal("WRT0010", error.Code);
        Assert.Equal("Warrant: the warrant CLI exited with code 1 without reporting an error. Its error output ended with:\nunexpected", error.Message);
    }

    [Fact]
    public void AnyOtherExitCodeIsWrt0010()
    {
        fake.Script([], exitCode: 3);

        Assert.False(Run(Task()));

        var error = Assert.Single(engine.Errors);
        Assert.Equal(("WRT0010", "Warrant: the warrant CLI exited with code 3."), (error.Code, error.Message));
    }

    [Fact]
    public void TheCliGetsTheArgsFileProjectDirectoryAndFormat()
    {
        fake.Script([Summary], exitCode: 0);

        Assert.True(Run(Task()));

        var args = Assert.Single(fake.Invocations());
        Assert.Equal(
            ["verify", "--csc-args", Path.Combine(fake.ProjectDirectory, "obj", "warrant.csc.args"), "--project-dir", fake.ProjectDirectory, "--format", "msbuild"],
            args);
    }

    [Fact]
    public void BudgetsAndTheConditionalCheckArePassedWhenSet()
    {
        fake.Script([Summary], exitCode: 0);
        var task = Task();
        task.KernelFuel = "20000000";
        task.TacticFuel = " 5000 ";
        task.TimeoutSeconds = "60";
        task.KeepConditionalCheck = true;

        Assert.True(Run(task));

        var args = Assert.Single(fake.Invocations());
        Assert.Equal(
            ["--kernel-fuel", "20000000", "--tactic-fuel", "5000", "--timeout", "60", "--keep-conditional-check"],
            args.Skip(7));
    }

    [Fact]
    public void WithoutAHostPathDotnetIsFoundOnThePath()
    {
        fake.Script([Summary], exitCode: 0);
        var task = Task();
        task.DotnetHostPath = "";

        Assert.True(Run(task));

        Assert.Single(fake.Invocations());
    }

    [Fact]
    public void AMissingCliIsWrt0010()
    {
        var task = Task();
        task.CliPath = Path.Combine(fake.ProjectDirectory, "missing", "warrant.dll");

        Assert.False(Run(task));

        var error = Assert.Single(engine.Errors);
        Assert.Equal("WRT0010", error.Code);
        Assert.Empty(fake.Invocations());
    }

    private WarrantVerify Task() => new()
    {
        BuildEngine = engine,
        CscArgsFile = Path.Combine(fake.ProjectDirectory, "obj", "warrant.csc.args"),
        ProjectDirectory = fake.ProjectDirectory,
        CliPath = FakeCli.CliPath,
        DotnetHostPath = FakeCli.DotnetHost,
    };

    private static bool Run(WarrantVerify task) => task.Execute();
}
