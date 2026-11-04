using Warrant.Cic;
using Warrant.Kernel;

namespace Warrant.Engine.Tests;

/// <summary>
/// The <c>casesOn</c> and <c>ctorIdx</c> the engine generates for translated inductives (M5a U14, KTD8): the same terms Lean
/// makes for Init's types, admitted by the kernel for every translated type, and exported with the run.
/// </summary>
public sealed class ConstructionsTests(EngineFixture engine) : IClassFixture<EngineFixture>
{
    private IEnumerable<DefinitionInfo> BundleDefinitions(string suffix) =>
        engine.Bundle.Declarations.OfType<ConstantDeclaration>().Select(d => d.Constant).OfType<DefinitionInfo>()
            .Where(c => c.Name.Kind == NameKind.Str && c.Name.StringComponent == suffix);

    /// <summary>
    /// Lean builds <c>casesOn</c> of a structure-like proposition that eliminates into every universe from projections
    /// (<c>mkCasesOnViaProjs?</c>, Lean/Meta/Constructions/CasesOn.lean 48), not from the recursor. Translated types are
    /// never propositions, so the engine does not port it.
    /// </summary>
    private bool IsLargeEliminatingPropStructure(Name indName)
    {
        var ind = (InductiveInfo)engine.Bundle.Env.Get(indName);
        var type = ind.Type;
        while (type is ForallExpr f)
        {
            type = f.Body;
        }
        var rec = engine.Bundle.Env.Get(indName.Append("rec"));
        return type is SortExpr { Level.Kind: LevelKind.Zero } && ind.Constructors.Count == 1 && ind.NumIndices == 0
            && rec.LevelParams.Count > ind.LevelParams.Count;
    }

    [Fact]
    public void CasesOnIsTheTermLeanMakesForEveryInitTypeInTheBundle()
    {
        var compared = new List<string>();
        foreach (var lean in BundleDefinitions("casesOn"))
        {
            var ind = lean.Name.Prefix!;
            if (IsLargeEliminatingPropStructure(ind))
            {
                continue;
            }
            var ours = Constructions.MkCasesOn(engine.Bundle.Env, ind);
            // Equal up to binder names, which Lean sometimes makes hygienic (Lean's Expr ==).
            Assert.True(ours.Type.AlphaEquals(lean.Type), $"{lean.Name}: type\n{ours.Type}\n{lean.Type}");
            Assert.True(ours.Value.AlphaEquals(lean.Value), $"{lean.Name}: value\n{ours.Value}\n{lean.Value}");
            Assert.Equal(lean.LevelParams, ours.LevelParams);
            Assert.Equal(lean.Hints, ours.Hints);
            compared.Add(lean.Name.ToString());
        }
        Assert.Contains("Bool.casesOn", compared);
        Assert.Contains("Nat.casesOn", compared);
        Assert.Contains("Prod.casesOn", compared);
        Assert.Contains("Eq.casesOn", compared); // with an index
        // Bool.casesOn exactly, binder names and annotations included.
        var boolCasesOn = (DefinitionInfo)engine.Bundle.Env.Get(Name.Parse("Bool.casesOn"));
        Assert.Equal(boolCasesOn, Constructions.MkCasesOn(engine.Bundle.Env, Name.Parse("Bool")));
    }

    [Fact]
    public void CtorIdxIsTheTermLeanMakesForEveryInitTypeThatHasOne()
    {
        var compared = new List<string>();
        foreach (var lean in BundleDefinitions("ctorIdx"))
        {
            var ours = Constructions.MkCtorIdx(engine.Bundle.Env, lean.Name.Prefix!);
            Assert.NotNull(ours);
            Assert.True(ours.Type.AlphaEquals(lean.Type), $"{lean.Name}: type\n{ours.Type}\n{lean.Type}");
            Assert.True(ours.Value.AlphaEquals(lean.Value), $"{lean.Name}: value\n{ours.Value}\n{lean.Value}");
            Assert.Equal(lean.LevelParams, ours.LevelParams);
            Assert.Equal(lean.Hints, ours.Hints);
            compared.Add(lean.Name.ToString());
        }
        Assert.Contains("Bool.ctorIdx", compared);
        Assert.Contains("List.ctorIdx", compared); // with a parameter
        // Lean makes none for a proposition.
        Assert.Null(Constructions.MkCtorIdx(engine.Bundle.Env, Name.Parse("Or")));
    }

    [Fact]
    public void EveryTranslatedInductiveHasItsCasesOnAndCtorIdxAdmitted()
    {
        var result = engine.Run("accepted");
        var inductives = result.Admitted.OfType<InductiveDecl>().SelectMany(d => d.Types).Select(t => t.Name).ToList();
        Assert.Contains(Name.Parse("Cs.Claims.ClaimStatus"), inductives); // a [Closed] enum
        Assert.Contains(Name.Parse("Cs.Claims.Payment"), inductives); // a record
        Assert.Contains(inductives, n => n.ToString().EndsWith(".Outcome", StringComparison.Ordinal)); // a [Closed] class
        var admitted = result.Admitted.OfType<DefinitionDecl>().Select(d => d.Value.Name).ToHashSet();
        foreach (var ind in inductives)
        {
            Assert.Contains(Constructions.CasesOnName(ind), admitted);
            Assert.Contains(Constructions.CtorIdxName(ind), admitted);
            Assert.IsType<DefinitionInfo>(result.Environment.Find(Constructions.CasesOnName(ind)));
        }

        // The documented shape (docs/m5a/04): {motive : ClaimStatus → Sort u} → (t : ClaimStatus) → motive Open → … → motive t.
        var casesOn = (DefinitionInfo)result.Environment.Get(Name.Parse("Cs.Claims.ClaimStatus.casesOn"));
        Assert.Equal(["motive", "t", "Open", "Paid", "Denied", "Withdrawn"], Binders(casesOn.Type));
        Assert.Equal(ReducibilityHints.Abbrev, casesOn.Hints);
        var ctorIdx = (DefinitionInfo)result.Environment.Get(Name.Parse("Cs.Claims.ClaimStatus.ctorIdx"));
        Assert.Equal(ReducibilityHints.Regular(1), ctorIdx.Hints);
        // A record has one constructor, so its index is 0.
        var paymentIdx = (DefinitionInfo)result.Environment.Get(Name.Parse("Cs.Claims.Payment.ctorIdx"));
        Assert.Equal(Expr.NatLit(0), Assert.IsType<LamExpr>(paymentIdx.Value).Body);

        // A type's outcome lists everything admitted for it.
        var claimStatus = Assert.IsType<TranslatedOutcome>(result.Find("T:Claims.ClaimStatus"));
        Assert.Contains(claimStatus.Declarations, d => d is DefinitionDecl { Value.Name: var n } && n == casesOn.Name);
    }

    [Fact]
    public void TheGeneratedConstantsAreExportedAndRecheckedInAnEmptyEnvironment()
    {
        var result = engine.Run("m5a/accepted");
        var path = Path.Combine(Path.GetTempPath(), $"warrant-constructions-{Guid.NewGuid():N}.ndjson");
        try
        {
            using (var file = File.Create(path))
            {
                result.WriteNdjson(file);
            }
            var declarations = Lean4Export.Lean4Export.ReadFile(path).Declarations;
            var checks = new ExportChecker(new KernelEnvironment(), KernelLimits.Corpus).CheckAll(declarations);
            Assert.All(checks, c => Assert.True(c.Accepted, $"{c.Name}: {c.Error}"));
            Assert.Contains(checks, c => c.Name.ToString() == "Cs.Corpus.Light.casesOn");
            Assert.Contains(checks, c => c.Name.ToString() == "Cs.Corpus.Light.ctorIdx");
            Assert.Contains(checks, c => c.Name.ToString() == "Cs.Claims.Payment.casesOn");
        }
        finally
        {
            File.Delete(path);
        }
    }

    private static List<string> Binders(Expr e)
    {
        var names = new List<string>();
        while (e is ForallExpr f)
        {
            names.Add(f.BinderName.ToString());
            e = f.Body;
        }
        return names;
    }
}
