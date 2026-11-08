using Warrant.Cic;
using Warrant.Lean4Export;

namespace Warrant.Engine.Tests;

/// <summary>
/// A bundle may declare only Lean's standard axioms, exactly as Lean declares them (#26): the kernel admits any
/// well-typed axiom, so one more would make every proof check.
/// </summary>
public sealed class SemanticsBundleTests
{
    private static readonly Lazy<ExportFile> Committed = new(() => Lean4Export.Lean4Export.ReadFile(TestData.Path(SemanticsBundle.FileName)));

    private static Declaration Axiom(string name, Expr type) =>
        new ConstantDeclaration(new AxiomInfo(Name.Parse(name), EquatableArray<Name>.Empty, type, false));

    private static Declaration Find(string name) =>
        Committed.Value.Declarations.Single(d => d.Constants.Any(c => c.Name.ToString() == name));

    [Fact]
    public void TheCommittedBundleDeclaresOnlyTheStandardAxiomsAsLeanDoes()
    {
        Assert.Null(SemanticsBundle.AxiomProblem(Committed.Value.Declarations));
        var axioms = Committed.Value.Declarations.SelectMany(d => d.Constants).OfType<AxiomInfo>().Select(a => a.Name.ToString());
        Assert.Equal(SemanticsBundle.StandardAxioms.Order(StringComparer.Ordinal), axioms.Order(StringComparer.Ordinal));
    }

    [Fact]
    public void ABundleWithAnotherAxiomIsRejectedBeforeAnythingIsChecked()
    {
        var path = Path.Combine(Path.GetTempPath(), $"warrant-bad-bundle-{Guid.NewGuid():N}.ndjson");
        try
        {
            using (var stream = File.Create(path))
            using (var writer = new Lean4ExportWriter(stream, Committed.Value.Metadata))
            {
                writer.WriteAll(Committed.Value.Declarations.Append(Axiom("Bad", Expr.Const(Name.Parse("False")))));
            }
            var e = Assert.Throws<InvalidDataException>(() => SemanticsBundle.Load(path));
            Assert.Contains("declares the axiom Bad, which is not one of propext, Classical.choice, Quot.sound.", e.Message, StringComparison.Ordinal);
        }
        finally
        {
            File.Delete(path);
        }
    }

    [Fact]
    public void SorryAxIsRejected()
    {
        var sorry = Axiom("sorryAx", Expr.Sort(Level.Zero));
        Assert.Equal(
            "declares the axiom sorryAx, which is not one of propext, Classical.choice, Quot.sound.",
            SemanticsBundle.AxiomProblem([sorry]));
    }

    [Fact]
    public void AStandardAxiomWithAnotherStatementIsRejected()
    {
        // axiom propext : False, before Lean's propext would come.
        var declarations = Committed.Value.Declarations
            .Select(d => d.Constants.Any(c => c.Name.ToString() == "propext") ? Axiom("propext", Expr.Const(Name.Parse("False"))) : d);
        Assert.Equal("declares propext differently from Lean 4.35.0.", SemanticsBundle.AxiomProblem(declarations));
    }

    [Fact]
    public void ATypeAStandardAxiomMentionsIsRejectedIfItIsNotLeans()
    {
        // propext means what it says only for Lean's Iff: an Iff anyone can build would make it prove any two propositions
        // equal. Any difference at all is rejected; here, a flipped flag.
        var iff = (InductiveDeclaration)Find("Iff");
        var forged = iff with { Types = [iff.Types[0] with { IsRec = !iff.Types[0].IsRec }] };
        var declarations = Committed.Value.Declarations.Select(d => ReferenceEquals(d, iff) ? forged : d);
        Assert.Equal("declares Iff differently from Lean 4.35.0.", SemanticsBundle.AxiomProblem(declarations));
    }

    [Fact]
    public void AConstantTheKernelComputesWithByNameIsRejectedIfItIsNotLeans()
    {
        // def Nat.add (n m : Nat) : Nat := n. The kernel still computes Nat.add 1 1 = 2 on literals, while unfolding the
        // definition gives Nat.add n 1 = n; together they prove False with no axiom.
        var add = (ConstantDeclaration)Find("Nat.add");
        var real = (DefinitionInfo)add.Constant;
        var nat = Expr.Const(Name.Parse("Nat"));
        var first = Expr.Lam(Name.Parse("n"), nat, Expr.Lam(Name.Parse("m"), nat, Expr.BVar(1)));
        var forged = new ConstantDeclaration(real with { DefinitionValue = first });
        var declarations = Committed.Value.Declarations.Select(d => ReferenceEquals(d, add) ? forged : d);
        Assert.Equal("declares Nat.add differently from Lean 4.35.0.", SemanticsBundle.AxiomProblem(declarations));
    }

    [Fact]
    public void AConstantAPinnedDefinitionMentionsIsRejectedIfItIsNotLeans()
    {
        // Nat.add unfolds through the constants its value mentions, so those are pinned too.
        var mentioned = SemanticsBundle.PinnedDeclarations()
            .OfType<ConstantDeclaration>()
            .First(d => d.Constant is DefinitionInfo && !SemanticsBundle.KernelReducedNames.Contains(d.Constant.Name));
        var forged = new ConstantDeclaration(((DefinitionInfo)mentioned.Constant) with { Hints = ReducibilityHints.Opaque });
        var declarations = Committed.Value.Declarations.Select(d => d.Equals(mentioned) ? forged : d);
        Assert.Equal($"declares {mentioned.Constant.Name} differently from Lean 4.35.0.", SemanticsBundle.AxiomProblem(declarations));
    }

    [Fact]
    public void AKernelReducedNameLeansBundleDoesNotDeclareIsRejected()
    {
        // The kernel computes Nat.lor on literals, and the committed bundle does not declare it, so a bundle may not.
        Assert.DoesNotContain(Committed.Value.Declarations.SelectMany(d => d.Constants), c => c.Name.ToString() == "Nat.lor");
        var nat = Expr.Const(Name.Parse("Nat"));
        var lor = new ConstantDeclaration(new DefinitionInfo(
            Name.Parse("Nat.lor"), EquatableArray<Name>.Empty, nat, Expr.NatLit(0), ReducibilityHints.Abbrev,
            DefinitionSafety.Safe, [Name.Parse("Nat.lor")]));
        Assert.Equal(
            "declares Nat.lor, which the kernel computes with by name and Lean 4.35.0's bundle does not declare.",
            SemanticsBundle.AxiomProblem(Committed.Value.Declarations.Append(lor)));
    }

    [Fact]
    public void TheEmbeddedPinnedDeclarationsAreTheClosureOfTheCommittedBundle() =>
        Assert.Equal(SemanticsBundle.PinnedClosure(Committed.Value.Declarations), SemanticsBundle.PinnedDeclarations());

    [Fact]
    public void TheReportNamesTheAxiomsAsAGlobalAssumption() =>
        Assert.Equal("The only axioms are Lean's standard ones: propext, Classical.choice, Quot.sound", Reports.AssumptionReports.Axioms);
}
