using System.Collections.Immutable;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Warrant.Engine.Reports;
using Warrant.Engine.Service;
using Warrant.Extraction;
using Warrant.Frontend;
using Warrant.Vir;

namespace Warrant.Engine.Tests;

/// <summary>The assumption report (docs/m4/07; plan U11, R7).</summary>
public sealed class ReportTests(EngineFixture engine) : IClassFixture<EngineFixture>
{
    private const string Validate = "M:Claims.Payments.Validate(Claims.Payment)";
    private const string RejectsZero = "M:Claims.Payments.RejectsZero";

    [Fact]
    public void ValidateListsTheNonNullAssumptionForPAndTheGlobalAssumptions()
    {
        var report = Report("accepted");
        var unit = report.Find(Validate);
        Assert.NotNull(unit);
        Assert.Equal(ReportStatus.Translated, unit.Status);
        var p = Assert.Single(unit.Assumptions);
        Assert.Equal(VirAssumptionKind.NonNull, p.Kind);
        Assert.Equal("p is not null", p.Text);
        Assert.False(p.Inherited);
        Assert.Equal([AssumptionReports.Wraps, AssumptionReports.BundleModels, AssumptionReports.Axioms], report.Global.ToArray());

        var markdown = MarkdownReport.Render(report);
        Assert.Contains("Assumed (parameters):\n    - p is not null\n", markdown, StringComparison.Ordinal);
        Assert.Contains(
            "    - The semantics bundle models C# 14 int, long, bool and decimal, their nullable forms, records, enums, closed classes, "
            + "throw and the exceptions arithmetic, division and null access raise, and Math.Min, Math.Max and Math.Abs on int, long and decimal; "
            + "decimal arithmetic throws on overflow in every region\n",
            markdown,
            StringComparison.Ordinal);
        Assert.Contains("    - The only axioms are Lean's standard ones: propext, Classical.choice, Quot.sound\n", markdown, StringComparison.Ordinal);
        Assert.Contains("    - Arithmetic wraps on overflow, except in a checked region, where it throws (overflow checking is off)\n", markdown, StringComparison.Ordinal);
    }

    [Fact]
    public void ATheoremInheritsTheAssumptionsOfTheUnitsItCalls()
    {
        var report = Report("accepted");
        var validate = report.Find(Validate)!;
        var unit = report.Find(RejectsZero);
        Assert.NotNull(unit);
        Assert.Equal(ReportStatus.Verified, unit.Status);
        Assert.Equal("rfl", unit.By);
        Assert.Equal("Validate(new Payment(1, 0, PaymentStatus.Pending)) == PaymentResult.InvalidAmount", unit.Claim);
        var p = Assert.Single(unit.Assumptions, a => a.Text == "p is not null");
        Assert.True(p.Inherited);
        Assert.Equal(validate.DisplayName, p.From);
        Assert.Contains($"  Assumed (from {validate.DisplayName}):\n    - p is not null\n", MarkdownReport.Render(report), StringComparison.Ordinal);
    }

    [Fact]
    public void ReportsUseDisplayNamesNotLeanNames()
    {
        var report = Report("accepted");
        var markdown = MarkdownReport.Render(report);
        Assert.DoesNotContain("Cs.", markdown, StringComparison.Ordinal);
        Assert.DoesNotContain("T:", markdown, StringComparison.Ordinal);
        Assert.DoesNotContain("M:", markdown, StringComparison.Ordinal);
    }

    [Fact]
    public void AFalseTheoremIsFailed()
    {
        var unit = Report("refuted").Find("M:Corpus.Refuted.Increments.NeverWraps");
        Assert.NotNull(unit);
        Assert.Equal(ReportStatus.Failed, unit.Status);
        Assert.Equal("false", unit.Outcome);
        Assert.Equal("Increment(int.MaxValue) > int.MaxValue", unit.Claim);
    }

    [Fact]
    public void TheJsonReportRoundTripsAndIsByteIdenticalAcrossRuns()
    {
        var first = JsonReport.Render(Report("accepted"));
        var second = JsonReport.Render(Report("accepted"));
        Assert.Equal(first, second);

        var read = JsonReport.Read(first);
        Assert.Equal(first, JsonReport.Render(read));
        var original = Report("accepted");
        Assert.Equal(original.Units.Length, read.Units.Length);
        Assert.Equal(original.Find(RejectsZero)!.Assumptions.ToArray(), read.Find(RejectsZero)!.Assumptions.ToArray());
        Assert.Equal(original.Global.ToArray(), read.Global.ToArray());
    }

    [Fact]
    public void AClosedClassFromAReferencedProjectIsReportedAsReferencedSourceInTextAndJson()
    {
        // #53: the assumption every unit using a referenced project's closed class carries (#32), in both reports.
        var report = ReferencedReport();
        var unit = report.Find("M:Painter.Same(Shapes.Color,Shapes.Color)");
        Assert.NotNull(unit);
        Assert.Equal(ReportStatus.Translated, unit.Status);
        var referenced = Assert.Single(unit.Assumptions, a => a.Kind == VirAssumptionKind.ReferencedSource);
        const string Text = "Shapes.Color comes from a referenced assembly built from the source Warrant checked, as that project's build recorded it";
        Assert.Equal(Text, referenced.Text);
        Assert.Contains(unit.Assumptions, a => a.Kind == VirAssumptionKind.Closed);

        Assert.Contains($"    - {Text}\n", MarkdownReport.Render(report), StringComparison.Ordinal);

        var json = JsonReport.Render(report);
        Assert.Contains("\"referenced-source\"", json, StringComparison.Ordinal);
        Assert.Contains(Text, json, StringComparison.Ordinal);
        var read = JsonReport.Read(json);
        Assert.Equal(json, JsonReport.Render(read));
        Assert.Equal(unit.Assumptions.ToArray(), read.Find(unit.Key)!.Assumptions.ToArray());
    }

    [Fact]
    public void AMethodsOwnRequiresIsReportedAsACallerPreconditionInTextAndJson()
    {
        // M6 U10 (#89): the data and its text; M6 U12 words the report's contract sections.
        var inputs = EngineCorpus.Inputs(EngineCorpus.Inline("""
            public static class S
            {
                [Verified]
                public static int Halve(int x)
                {
                    Spec.Requires(x >= 0);
                    return x / 2;
                }
            }
            """));
        var report = AssumptionReports.Build(
            Pipeline.Run(inputs, engine.Bundle, engine.Options), inputs, new ReportSettings(CheckOverflow: false, Bundle: "warrant-semantics test"));
        var unit = report.Find("M:S.Halve(System.Int32)");
        Assert.NotNull(unit);
        var requires = Assert.Single(unit.Assumptions);
        Assert.Equal(VirAssumptionKind.CallerPrecondition, requires.Kind);
        const string Text = "S.Halve(int)'s Spec.Requires is assumed on entry: verified callers prove it at each call, but it is not checked at run time or at call sites Warrant does not verify";
        Assert.Equal(Text, requires.Text);
        Assert.Contains($"Assumed (contracts):\n    - {Text}\n", MarkdownReport.Render(report), StringComparison.Ordinal);
        var json = JsonReport.Render(report);
        Assert.Contains("\"caller-precondition\"", json, StringComparison.Ordinal);
        var read = JsonReport.Read(json);
        Assert.Equal(json, JsonReport.Render(read));
        Assert.Equal(unit.Assumptions.ToArray(), read.Find(unit.Key)!.Assumptions.ToArray());
    }

    [Fact]
    public void RatiosReportSaysItsRequiresIsNotCheckedAtRunTimeOrAtUnverifiedCallSites()
    {
        // M6 U12 (#89, KTD20).
        var inputs = EngineCorpus.Inputs(EngineCorpus.Inline("""
            public static class S
            {
                [Verified]
                public static int Ratio(int a, int b)
                {
                    Spec.Requires(b != 0 && b != -1);
                    return a / b;
                }
            }
            """));
        var report = AssumptionReports.Build(
            Pipeline.Run(inputs, engine.Bundle, engine.Options), inputs, new ReportSettings(CheckOverflow: false, Bundle: "warrant-semantics test"));
        var requires = Assert.Single(report.Find("M:S.Ratio(System.Int32,System.Int32)")!.Assumptions);
        Assert.Equal(VirAssumptionKind.CallerPrecondition, requires.Kind);
        Assert.Equal(
            "S.Ratio(int, int)'s Spec.Requires is assumed on entry: verified callers prove it at each call, but it is not checked at run time or at call sites Warrant does not verify",
            requires.Text);
    }

    [Fact]
    public void AThrowingMethodListsItsThrowSiteAndAVerifiedCallerListsThePropagatedThrowWithTheCalleesSite()
    {
        // M6 U12 (#70, KTD20). The walker (U11) attaches these assumptions to the outcomes; here they are built by hand
        // from the units' own node IDs, which the report maps to source lines through the units' span tables.
        var inputs = EngineCorpus.Inputs(EngineCorpus.Inline("""
            public static class S
            {
                [Verified]
                public static int G(int x)
                {
                    if (x < 0)
                    {
                        throw new System.ArgumentException("x");
                    }
                    return x;
                }

                [Verified]
                public static int F(int x)
                {
                    var y = G(x);
                    return y;
                }
            }
            """));
        const string G = "M:S.G(System.Int32)", F = "M:S.F(System.Int32)", Thrown = "T:System.ArgumentException";
        var g = inputs.Single(u => u.Unit.Key == G);
        var f = inputs.Single(u => u.Unit.Key == F);
        var throwNode = VirTree.IdOf(g.Unit, VirTree.PreOrder(g.Unit).Single(n => n is ThrowStmt))!.Value;
        var callNode = VirTree.IdOf(f.Unit, VirTree.PreOrder(f.Unit).Single(n => n is CallExpr))!.Value;
        Assert.True(g.Spans!.TryGetSpan(throwNode, out var throwSpan));
        Assert.True(f.Spans!.TryGetSpan(callNode, out var callSpan));
        Assert.Equal(("Test.cs", 9, 17), (throwSpan!.Path, throwSpan.StartLine, callSpan!.StartLine));

        var outcomes = new[]
        {
            Proved(G, "S.G(int)", new AssumptionDto(G, VirAssumptionKind.MayThrow, new MayThrowSubject(Thrown, throwNode).Format())),
            Proved(
                F,
                "S.F(int)",
                new AssumptionDto(F, VirAssumptionKind.CalleeContract, G),
                new AssumptionDto(F, VirAssumptionKind.MayThrow, new MayThrowSubject(Thrown, throwNode, In: G, Via: G, CallNode: callNode).Format())),
        };
        var report = AssumptionReports.Build(outcomes, inputs, new ReportSettings(CheckOverflow: false, Bundle: "warrant-semantics test"));

        const string Own = "S.G(int) may throw System.ArgumentException (the throw at Test.cs:9); its proof says nothing about a call that ends in it";
        var own = Assert.Single(report.Find(G)!.Assumptions);
        Assert.Equal((VirAssumptionKind.MayThrow, "System.ArgumentException", false, Own), (own.Kind, own.Subject, own.Inherited, own.Text));

        const string Propagated =
            "S.F(int) may throw System.ArgumentException through its call to S.G(int) at Test.cs:17 (the throw at Test.cs:9); its proof says nothing about a call that ends in it";
        const string Callee =
            "S.G(int) returns only values its Spec.Ensures allows, as Warrant proved under its own assumptions; this method proves its Spec.Requires at each call";
        var fUnit = report.Find(F)!;
        Assert.Equal([Callee, Propagated], fUnit.Assumptions.Select(a => a.Text).ToArray());
        Assert.All(fUnit.Assumptions, a => Assert.False(a.Inherited));

        var markdown = MarkdownReport.Render(report);
        Assert.Contains($"  Assumed (exceptions):\n    - {Own}\n", markdown, StringComparison.Ordinal);
        Assert.Contains($"  Assumed (contracts):\n    - {Callee}\n  Assumed (exceptions):\n    - {Propagated}\n", markdown, StringComparison.Ordinal);
    }

    [Fact]
    public void AnExceptionFromADependencyAndAThrowWithoutASpanAreReported()
    {
        // KTD20: a propagated external exception names the member and its call; a site the report cannot place is left out.
        const string F = "M:S.F(System.Int32)";
        var outcomes = new[]
        {
            Proved(
                F,
                "S.F(int)",
                new AssumptionDto(F, VirAssumptionKind.MayThrow, new MayThrowSubject("M:Payments.IStore.Get(System.Int32)", 3).Format()),
                new AssumptionDto(F, VirAssumptionKind.MayThrow, "T:System.InvalidOperationException")),
        };
        var report = AssumptionReports.Build(
            outcomes, new Dictionary<string, EngineUnit>(), new ReportSettings(CheckOverflow: false, Bundle: "b"), _ => null);
        Assert.Equal(
            [
                "S.F(int) may throw an exception from Payments.IStore.Get(System.Int32); its proof says nothing about a call that ends in it",
                "S.F(int) may throw System.InvalidOperationException; its proof says nothing about a call that ends in it",
            ],
            report.Find(F)!.Assumptions.Select(a => a.Text).ToArray());
    }

    [Fact]
    public void AMayThrowSubjectRoundTrips()
    {
        MayThrowSubject[] subjects =
        [
            new("T:System.ArgumentException"),
            new("T:System.ArgumentException", 7),
            new("T:System.ArgumentException", 7, In: "M:S.G(System.Int32)", Via: "M:S.G(System.Int32)", CallNode: 3),
            new("M:Payments.IStore.Get(System.Int32)", 2, Via: "M:S.H", CallNode: 11),
        ];
        foreach (var s in subjects)
        {
            Assert.Equal(s, MayThrowSubject.Parse(s.Format()));
        }
        Assert.Equal("T:System.ArgumentException", subjects[0].Format());
        Assert.Throws<FormatException>(() => MayThrowSubject.Parse("T:X|seven"));
    }

    [Fact]
    public void EveryAssumptionKindAndUnitKindRoundTripsThroughJson()
    {
        // M6 U12: every KTD20 kind, and the contract units U18 extracts, render and read back.
        const string F = "M:S.F(System.Int32)";
        var all = Enum.GetValues<VirAssumptionKind>();
        var outcomes = new[]
        {
            Proved(
                F,
                "S.F(int)",
                [.. all.Select(k => new AssumptionDto(F, k, k switch
                {
                    VirAssumptionKind.NonNull => "store",
                    VirAssumptionKind.ExternalContract => "M:Payments.IStore.Get(System.Int32)",
                    VirAssumptionKind.MayThrow => new MayThrowSubject("T:System.ArgumentException", 4, In: "M:S.G", Via: "M:S.G", CallNode: 2).Format(),
                    VirAssumptionKind.CalleeContract => "M:S.G",
                    VirAssumptionKind.CallerPrecondition => F,
                    _ => "T:S.Color",
                }))]),
            new OutcomeDto(OutcomeKind.Translated, "M:Payments.IStore.Get(System.Int32)", VirUnitKind.Contract, "Payments.IStore.Get(int)", []),
        };
        var report = AssumptionReports.Build(
            outcomes, new Dictionary<string, EngineUnit>(), new ReportSettings(CheckOverflow: true, Bundle: "b"), _ => null);
        Assert.Equal(all, report.Find(F)!.Assumptions.Select(a => a.Kind).Order().ToArray());
        Assert.Contains(
            "  Assumed (contracts):\n    - Every implementation of Payments.IStore.Get(int) keeps what its contract class states\n",
            MarkdownReport.Render(report),
            StringComparison.Ordinal);

        var json = JsonReport.Render(report);
        foreach (var name in new[] { "external-contract", "callee-contract", "may-throw", "caller-precondition", "\"contract\"" })
        {
            Assert.Contains(name, json, StringComparison.Ordinal);
        }
        var read = JsonReport.Read(json);
        Assert.Equal(json, JsonReport.Render(read));
        Assert.Equal(report.Find(F)!.Assumptions.ToArray(), read.Find(F)!.Assumptions.ToArray());
        Assert.Equal(VirUnitKind.Contract, read.Find("M:Payments.IStore.Get(System.Int32)")!.Kind);
    }

    /// <summary>
    /// The milestone's headline (plan M6 U20, design §5.2 and §8.4): ProcessPayment, proved with its store as a hypothesis,
    /// lists GetPayment's and SavePayment's contracts, that the store and GetPayment's Task are not null, and the exceptions
    /// either call may propagate. Its block of the Markdown report is the checked-in
    /// <c>tests/corpus/m6/ProcessPayment.report.txt</c>.
    /// </summary>
    [Fact]
    public void TheReportOfProcessPaymentIsTheCheckedInOne()
    {
        const string Key = "M:Corpus.M6.Payments.PaymentService.ProcessPayment(System.Int32)";
        var report = AssumptionReports.Build(
            engine.Run("m6/accepted"),
            engine.Inputs("m6/accepted"),
            new ReportSettings(CheckOverflow: false, Bundle: "warrant-semantics test", Kernel: "Warrant test"),
            span => SourceTextIn(CorpusSet.M6.Root, span));
        var unit = report.Find(Key);
        Assert.NotNull(unit);
        Assert.Equal((ReportStatus.Translated, "translated"), (unit.Status, unit.Outcome));
        var block = Block(MarkdownReport.Render(report), "Corpus.M6.Payments.PaymentService.ProcessPayment(int) ");
        var expected = File.ReadAllText(Path.Combine(CorpusSet.M6.Root, "ProcessPayment.report.txt")).ReplaceLineEndings("\n");
        Assert.Equal(expected, block);
    }

    /// <summary>
    /// A method that throws on every path (plan M6 U14, KTD12, KTD20): its Spec.Ensures holds vacuously, so the report's
    /// may-throw line for its throw is all that says the method never returns. Its block is the checked-in
    /// <c>tests/corpus/m6/Closed.report.txt</c>.
    /// </summary>
    [Fact]
    public void TheReportOfAMethodThatThrowsOnEveryPathIsTheCheckedInOne()
    {
        var report = AssumptionReports.Build(
            engine.Run("m6/accepted"),
            engine.Inputs("m6/accepted"),
            new ReportSettings(CheckOverflow: false, Bundle: "warrant-semantics test", Kernel: "Warrant test"),
            span => SourceTextIn(CorpusSet.M6.Root, span));
        var block = Block(MarkdownReport.Render(report), "Corpus.M6.Effects.Closed(int) ");
        var expected = File.ReadAllText(Path.Combine(CorpusSet.M6.Root, "Closed.report.txt")).ReplaceLineEndings("\n");
        Assert.Equal(expected, block);
    }

    /// <summary>A unit's block of a Markdown report: its line and its assumption lines, up to the next unit.</summary>
    internal static string Block(string markdown, string head)
    {
        var lines = markdown.Split('\n');
        int start = Array.FindIndex(lines, l => l.StartsWith(head, StringComparison.Ordinal));
        Assert.True(start >= 0, markdown);
        int end = start + 1;
        while (end < lines.Length && lines[end].StartsWith(' '))
        {
            end++;
        }
        return string.Join('\n', lines[start..end]) + "\n";
    }

    [Fact]
    public void TheOverflowLineStatesBothRegionsWhicheverTheProjectSetting()
    {
        // #147: a checked project's theorems may be proved over unchecked regions, which wrap, and an unchecked project's
        // methods may have checked regions, which throw (M6 U7, U9); the global line must not contradict either.
        Assert.Equal("Arithmetic throws on overflow, except in an unchecked region, where it wraps (overflow checking is on)", AssumptionReports.Throws);
        Assert.Equal("Arithmetic wraps on overflow, except in a checked region, where it throws (overflow checking is off)", AssumptionReports.Wraps);
        var report = AssumptionReports.Build(
            Array.Empty<OutcomeDto>(), new Dictionary<string, EngineUnit>(), new ReportSettings(CheckOverflow: true, Bundle: "b"), _ => null);
        Assert.Equal([AssumptionReports.Throws, AssumptionReports.BundleModels, AssumptionReports.Axioms], report.Global.ToArray());
    }

    private static OutcomeDto Proved(string key, string display, params AssumptionDto[] assumptions) =>
        new(OutcomeKind.Proved, key, VirUnitKind.Function, display, [.. assumptions]) { By = ProofKind.Script };

    /// <summary>A unit using a closed class from a referenced assembly, extracted with that assembly's source.</summary>
    private AssumptionReport ReferencedReport()
    {
        var shapes = CompilationFactory.Create(
            [new SourceFile("Color.cs", "namespace Shapes { [Warrant.Closed] public sealed class Color { public static Color Red { get; } = new(); public static Color Blue { get; } = new(); private Color() { } } }")],
            checkOverflow: false,
            assemblyName: "Shapes");
        using var image = new MemoryStream();
        Assert.True(shapes.Emit(image).Success);
        var app = CSharpCompilation.Create(
            "Painter",
            [CSharpSyntaxTree.ParseText("using Warrant; public static class Painter { [Verified] public static bool Same(Shapes.Color a, Shapes.Color b) => a == b; }", CompilationFactory.ParseOptions, "Painter.cs")],
            [.. CompilationFactory.References, MetadataReference.CreateFromImage(ImmutableArray.Create(image.ToArray()))],
            CompilationFactory.Options(checkOverflow: false));
        var extraction = Extractor.Extract(app, new ExtractionOptions { ReferencedSource = name => name == "Shapes" ? shapes : null });
        Assert.Empty(extraction.Diagnostics);
        var inputs = EngineCorpus.Inputs(extraction);
        return AssumptionReports.Build(
            Pipeline.Run(inputs, engine.Bundle, engine.Options),
            inputs,
            new ReportSettings(CheckOverflow: false, Bundle: "warrant-semantics test"));
    }

    private AssumptionReport Report(string compilation)
    {
        var extraction = EngineCorpus.Extract(compilation);
        return AssumptionReports.Build(
            engine.Run(compilation),
            EngineCorpus.Inputs(extraction),
            new ReportSettings(CheckOverflow: false, Bundle: "warrant-semantics test"),
            SourceText);
    }

    private static string? SourceText(VirSpan span) => SourceTextIn(EngineCorpus.Root, span);

    private static string? SourceTextIn(string root, VirSpan span)
    {
        var lines = File.ReadAllLines(Path.Combine(root, span.Path));
        return span.StartLine == span.EndLine ? lines[span.StartLine - 1][(span.StartColumn - 1)..(span.EndColumn - 1)] : null;
    }
}
