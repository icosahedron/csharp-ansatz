using System.Collections.Immutable;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Warrant.Engine.Reports;
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
        Assert.Contains("    - The semantics bundle models C# 14 int, long and bool\n", markdown, StringComparison.Ordinal);
        Assert.Contains("    - The only axioms are Lean's standard ones: propext, Classical.choice, Quot.sound\n", markdown, StringComparison.Ordinal);
        Assert.Contains("    - Arithmetic wraps on overflow (overflow checking is off)\n", markdown, StringComparison.Ordinal);
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

    private static string? SourceText(VirSpan span)
    {
        var lines = File.ReadAllLines(Path.Combine(EngineCorpus.Root, span.Path));
        return span.StartLine == span.EndLine ? lines[span.StartLine - 1][(span.StartColumn - 1)..(span.EndColumn - 1)] : null;
    }
}
