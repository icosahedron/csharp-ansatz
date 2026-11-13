using Warrant.Cic;
using Warrant.Extraction;
using Warrant.Kernel;
using Warrant.Vir;

namespace Warrant.Semantics.Tests;

/// <summary>
/// The terms well-founded recursion translates to (plan M5a U15, KTD14, KTD15; docs/m5a/03): the <c>Nat.fix</c>
/// definition with <c>dite</c> on the way to the call, the packing of several parameters, the decrease theorems and the
/// equation lemma. That the kernel admits them is the engine's test (RecursionTests there), because the definition
/// needs its decrease theorems proved first.
/// </summary>
public sealed class RecursionTests(SemanticsBundleFixture bundle) : IClassFixture<SemanticsBundleFixture>
{
    private const string SumKey = "M:Corpus.Recursion.Sum(System.Int32)";
    private const string AddKey = "M:Corpus.Recursion.Add(System.Int32,System.Int32)";
    private const string SumLongKey = "M:Corpus.Recursion.SumLong(System.Int64)";

    private static readonly Lazy<ExtractionResult> Corpus = new(() =>
    {
        var result = Extractor.Extract(CorpusSet.M5a.Compile("accepted"));
        Assert.False(result.HasCompileErrors, string.Join("\n", result.Diagnostics.Select(d => d.Message)));
        return result;
    });

    private static readonly Expr Int32 = C("Int32");
    private static readonly Expr Nat = C("Nat");
    private static readonly Name X = Name.From("x");
    private static readonly Name N = Name.From("n");
    private static readonly Name H = Name.From("h");

    private static Expr C(string dotted, params Level[] levels) => Expr.Const(Name.Parse(dotted), levels);

    private static Expr App(Expr f, params Expr[] args) => Expr.App(f, args);

    private static Expr Lit(int n) => App(C("OfNat.ofNat", Level.Zero), Int32, Expr.NatLit(n), App(C("Int32.instOfNat"), Expr.NatLit(n)));

    private static Expr Le(Expr a, Expr b) => App(C("LE.le", Level.Zero), Int32, C("instLEInt32"), a, b);

    private static Expr Sub(Expr a, Expr b) =>
        App(C("HSub.hSub", Level.Zero, Level.Zero, Level.Zero), Int32, Int32, Int32, App(C("instHSub", Level.Zero), Int32, C("instSubInt32")), a, b);

    private static Expr Add(Expr a, Expr b) =>
        App(C("HAdd.hAdd", Level.Zero, Level.Zero, Level.Zero), Int32, Int32, Int32, App(C("instHAdd", Level.Zero), Int32, C("instAddInt32")), a, b);

    private static Expr Measure(Expr x) => App(C("Int.toNat"), App(C("Int32.toInt"), x));

    private static Expr NatLt(Expr a, Expr b) => App(C("LT.lt", Level.Zero), Nat, C("instLTNat"), a, b);

    private Translation Translate() => Translator.Translate(Corpus.Value.Units.Select(u => u.Unit), bundle.Env);

    private static RecursiveDefinition Recursion(Translation translation, string key) =>
        translation.Find(key)?.Recursion ?? throw new InvalidOperationException($"{key} is not recursive");

    [Fact]
    public void SumIsNatFixWithDiteOnThePathToTheCall()
    {
        // The term of docs/m5a/03, which Lean 4.35.0 builds for termination_by n.toInt.toNat.
        var translation = Translate();
        var sum = Assert.IsType<DefinitionDecl>(Assert.Single(translation.Find(SumKey)!.Declarations)).Value;
        var name = LeanNames.ForKey(SumKey);
        var dec1 = C($"{name}.$dec_1");
        var mu = Expr.Lam(N, Int32, Measure(Expr.BVar(0)));
        // rec : (y : Int32) → InvImage (fun a b => a < b) μ y n → Int32, under F's n.
        var relation = Expr.Lam(Name.From("a"), Nat, Expr.Lam(Name.From("b"), Nat, NatLt(Expr.BVar(1), Expr.BVar(0))));
        var recType = Expr.Forall(Name.From("y"), Int32, Expr.Forall(X, App(C("InvImage", Level.One, Level.One), Int32, Nat, relation, mu, Expr.BVar(0), Expr.BVar(1)), Int32));
        // Under fun n rec, then fun h: n = #2, rec = #1, h = #0.
        var call = App(Expr.BVar(1), Sub(Expr.BVar(2), Lit(1)), App(dec1, Expr.BVar(2), Expr.BVar(0)));
        var body = App(
            C("dite", Level.One),
            Int32,
            Le(Expr.BVar(1), Lit(0)),
            App(C("Int32.decLe"), Expr.BVar(1), Lit(0)),
            Expr.Lam(H, Le(Expr.BVar(1), Lit(0)), Lit(0)),
            Expr.Lam(H, App(C("Not"), Le(Expr.BVar(1), Lit(0))), Add(Expr.BVar(2), call)));
        var functional = Expr.Lam(N, Int32, Expr.Lam(Name.From("rec"), recType, body));
        var expected = Expr.Lam(N, Int32, App(
            C("WellFounded.Nat.fix", Level.One, Level.One), Int32, Expr.Lam(X, Int32, Int32), mu, functional, Expr.BVar(0)));
        Assert.Equal(expected, sum.Value);
        Assert.Equal(Expr.Forall(N, Int32, Int32), sum.Type);
    }

    [Fact]
    public void SumsDecreaseTheoremBindsTheParameterAndTheGuard()
    {
        // Sum.$dec_1 : ∀ (n : Int32), ¬n ≤ 0 → Int.toNat (Int32.toInt (n - 1)) < Int.toNat (Int32.toInt n).
        var decrease = Assert.Single(Recursion(Translate(), SumKey).Decreases);
        Assert.Equal(1, decrease.Index);
        Assert.Equal($"{LeanNames.ForKey(SumKey)}.$dec_1", decrease.Theorem.Name.ToString());
        Assert.Equal(2, decrease.Binders);
        var expected = Expr.Forall(N, Int32, Expr.Forall(H, App(C("Not"), Le(Expr.BVar(0), Lit(0))),
            NatLt(Measure(Sub(Expr.BVar(1), Lit(1))), Measure(Expr.BVar(1)))));
        Assert.Equal(expected, decrease.Theorem.Type);
        Assert.Null(decrease.Theorem.Statement.Instance);
        Assert.Equal("Sum(n - 1)", SourceOf(decrease.Call));
    }

    [Fact]
    public void TwoParametersPackIntoAPSigmaReadByProjections()
    {
        // fun a b => @Nat.fix ((_ : Int32) ×' Int32) (fun _ => Int32) (fun x => μ x.2) F ⟨a, b⟩, with F reading x.1 and x.2.
        var add = Assert.IsType<DefinitionDecl>(Assert.Single(Translate().Find(AddKey)!.Declarations)).Value;
        var a = Assert.IsType<LamExpr>(add.Value);
        var b = Assert.IsType<LamExpr>(a.Body);
        var fix = b.Body;
        Assert.Equal(C("WellFounded.Nat.fix", Level.One, Level.One), fix.GetAppFn());
        var args = fix.GetAppArgs();
        var pair = App(C("PSigma", Level.One, Level.One), Int32, Expr.Lam(X, Int32, Int32));
        Assert.Equal(pair, args[0]);
        Assert.Equal(Expr.Lam(X, pair, Measure(Expr.Proj(Name.Parse("PSigma"), 1, Expr.BVar(0)))), args[2]);
        Assert.Equal(App(C("PSigma.mk", Level.One, Level.One), Int32, Expr.Lam(X, Int32, Int32), Expr.BVar(1), Expr.BVar(0)), args[4]);
        var functional = Assert.IsType<LamExpr>(args[3]);
        Assert.Equal(pair, functional.BinderType);
        var text = functional.Body.ToString();
        Assert.Contains(".1", text, StringComparison.Ordinal);
        Assert.Contains(".2", text, StringComparison.Ordinal);
        Assert.DoesNotContain("casesOn", text, StringComparison.Ordinal);
    }

    [Fact]
    public void ALongMeasureUsesInt64ToInt()
    {
        var sumLong = Assert.IsType<DefinitionDecl>(Assert.Single(Translate().Find(SumLongKey)!.Declarations)).Value;
        var fix = Assert.IsType<LamExpr>(sumLong.Value).Body;
        var mu = fix.GetAppArgs()[2];
        Assert.Equal(Expr.Lam(N, C("Int64"), App(C("Int.toNat"), App(C("Int64.toInt"), Expr.BVar(0)))), mu);
    }

    [Theory]
    [InlineData(SumKey)]
    [InlineData(AddKey)]
    [InlineData(SumLongKey)]
    public void TheEquationLemmaStatesTheM4TranslationOfTheBody(string key)
    {
        // f.$eq_def : ∀ p, f p = body, where body is M4's translation (ite, the call a constant): the term the plain
        // function translation produces for the same unit.
        var unit = Corpus.Value.Find(key)!.Unit;
        var recursion = Recursion(Translate(), key);
        Assert.Equal($"{LeanNames.ForKey(key)}.$eq_def", recursion.Equation.Name.ToString());
        // Contracted: a recursive method may state Spec.Requires (#256), which neither term runs.
        var (_, m4) = new BodyTranslator(new TypeTable([unit])) { Contracted = true }.Function(unit);
        var statement = recursion.Equation.Type;
        var binders = 0;
        var lambda = m4;
        while (lambda is LamExpr lam && statement is ForallExpr pi)
        {
            Assert.Equal(lam.BinderType, pi.BinderType);
            lambda = lam.Body;
            statement = pi.Body;
            binders++;
        }
        Assert.Equal(unit.Params!.Count, binders);
        var eq = statement.GetAppArgs();
        Assert.Equal(C("Eq", Level.One), statement.GetAppFn());
        Assert.Equal(lambda, eq[2]);
        Assert.Equal(Expr.App(Expr.Const(LeanNames.ForKey(key)), [.. Enumerable.Range(0, binders).Select(i => Expr.BVar(binders - 1 - i))]), eq[1]);
        var text = eq[2].ToString();
        Assert.Contains("ite", text, StringComparison.Ordinal);
        Assert.DoesNotContain("dite", text, StringComparison.Ordinal);
        // The proof is the bare Nat.fix_eq instance, applied like the definition's Nat.fix.
        var proof = recursion.EquationProof;
        for (int i = 0; i < binders; i++)
        {
            proof = Assert.IsType<LamExpr>(proof).Body;
        }
        Assert.Equal(C("WellFounded.Nat.fix_eq", Level.One, Level.One), proof.GetAppFn());
    }

    [Fact]
    public void NestedRecursionIsATranslationError()
    {
        // Extraction rejects F(F(n - 1)) with WRT0002; translation refuses it too, because the outer obligation could not
        // name the inner result.
        var sum = Corpus.Value.Find(SumKey)!.Unit;
        var n = new ParamExpr(VirType.Int32, 0);
        var inner = new CallExpr(VirType.Int32, SumKey, new VirList<VirExpr>([n]));
        var body = new BlockStmt(new VirList<VirStmt>([new DecreasesStmt(n), new ReturnStmt(new CallExpr(VirType.Int32, SumKey, new VirList<VirExpr>([inner])))]));
        var ex = Assert.Throws<TranslationException>(() => Translator.Translate([sum with { Body = body }], bundle.Env));
        Assert.Contains("nested recursion", ex.Message, StringComparison.Ordinal);
    }

    /// <summary>The source text of a node of the corpus's Recursion.cs, through the unit's spans.</summary>
    private static string SourceOf(VirNode node)
    {
        var unit = Corpus.Value.Find(SumKey)!;
        Assert.True(unit.Spans!.TryGetSpan(VirTree.IdOf(unit.Unit, node)!.Value, out var span));
        Assert.NotNull(span);
        var lines = File.ReadAllLines(Path.Combine(CorpusSet.M5a.Root, "accepted", "Recursion.cs"));
        Assert.Equal(span.StartLine, span.EndLine);
        return lines[span.StartLine - 1][(span.StartColumn - 1)..(span.EndColumn - 1)];
    }
}
