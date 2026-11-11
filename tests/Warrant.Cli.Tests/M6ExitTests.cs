using System.Text.RegularExpressions;
using Warrant.Cic;
using Warrant.Engine;
using Warrant.Semantics;

namespace Warrant.Cli.Tests;

/// <summary>
/// M6's exit criterion (the plan's Success Criteria, KTD24; plan U14), one fact per criterion, so a failure names it.
/// <c>dotnet test --filter M6Exit</c> runs them. The two criteria whose harnesses live in other test projects have their
/// facts there, in a class of the same name: <c>Warrant.Engine.Tests.M6ExitTests</c> (the differential tests with
/// contract-satisfying mocked externals) and <c>Warrant.Semantics.Tests.M6ExitTests</c> (CLR agreement of every new model
/// operation).
/// </summary>
/// <remarks>
/// Not tests, by the plan: the private codebase's blocked candidates, which are checked by hand there and reported without
/// naming its code (KTD24), and the survey of its service methods against the dependency rules, which is reported (#177).
/// Lean's half of the second criterion is <c>scripts/cross-check.sh</c>'s M6 row, which needs a Lean toolchain: Lean's
/// kernel replays the certificate this test checks with Warrant's.
/// </remarks>
public sealed class M6ExitTests
{
    private static readonly string Corpus = Path.Combine(AppContext.BaseDirectory, "corpus", "m6");

    private const string ProcessPayment = "M:Corpus.M6.Payments.PaymentService.ProcessPayment(System.Int32)";

    /// <summary>
    /// The pure parts of the payment example (design §5.2) verify: the records and enums it uses, <c>Validate</c>, and the
    /// contract class's members, with no diagnostic.
    /// </summary>
    [Fact]
    public void ThePurePartsOfThePaymentExampleVerify()
    {
        var (code, output) = Verify(Path.Combine(Corpus, "accepted"), "--server", "off");
        Assert.True(code == 0, output);
        foreach (var unit in new[]
        {
            "Corpus.M6.Payments.Payment?", "Corpus.M6.Payments.PaymentStatus", "Corpus.M6.Payments.PaymentResult", "Corpus.M6.Payments.Result",
            "Corpus.M6.Payments.PaymentService.Validate(Corpus.M6.Payments.Payment)",
            "Corpus.M6.Payments.IPaymentStore.GetPayment(int)", "Corpus.M6.Payments.IPaymentStore.SavePayment(Corpus.M6.Payments.Payment)",
        })
        {
            Assert.Matches($@"(?m)^  {Regex.Escape(unit)} +translated$", output);
        }
        Assert.DoesNotContain(": error ", output, StringComparison.Ordinal);
        Assert.DoesNotContain(": warning ", output, StringComparison.Ordinal);
    }

    /// <summary>
    /// <c>ProcessPayment</c> verifies with <c>IPaymentStore</c> as a hypothesis: its contract obligation is proved by the
    /// default procedure, the certificate <c>--out</c> writes holds its <c>$contract</c> theorem and passes Warrant's kernel
    /// on its own, and the report lists the store's two contracts as what the proof assumed.
    /// </summary>
    [Fact]
    public void ProcessPaymentVerifiesWithItsStoreAsAHypothesisAndItsCertificateChecks()
    {
        var work = Directory.CreateTempSubdirectory("warrant-m6-exit-");
        try
        {
            var ndjson = Path.Combine(work.FullName, "m6.ndjson");
            var reports = Path.Combine(work.FullName, "report");
            var (code, output) = Verify(Path.Combine(Corpus, "accepted"), "--server", "off", "--out", ndjson, "--report", reports);
            Assert.True(code == 0, output);
            Assert.Matches(@"(?m)^  Corpus\.M6\.Payments\.PaymentService\.ProcessPayment\(int\) +translated$", output);

            var contract = LeanNames.Contract(ProcessPayment).ToString();
            var written = Lean4Export.Lean4Export.ReadFile(ndjson);
            Assert.Contains(written.Declarations.SelectMany(d => d.Constants), c => c is TheoremInfo && c.Name.ToString() == contract);
            Assert.Equal(0, global::Cli.Run(["check", ndjson, "--quiet"]));

            var json = Warrant.Engine.Reports.JsonReport.Read(File.ReadAllText(Path.Combine(reports, "report.json")));
            var unit = Assert.Single(json.Units, u => u.Key == ProcessPayment);
            Assert.Equal(
                ["Corpus.M6.Payments.IPaymentStore.GetPayment(int)", "Corpus.M6.Payments.IPaymentStore.SavePayment(Corpus.M6.Payments.Payment)"],
                unit.Assumptions.Where(a => a.Kind == Vir.VirAssumptionKind.ExternalContract).Select(a => a.Subject).Order(StringComparer.Ordinal));
        }
        finally
        {
            work.Delete(recursive: true);
        }
    }

    private static (int Code, string Output) Verify(params string[] args)
    {
        using var output = new StringWriter { NewLine = "\n" };
        var code = VerifyCommand.Run(args, output, output);
        return (code, output.ToString());
    }
}
